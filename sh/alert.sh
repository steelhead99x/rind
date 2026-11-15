#!/usr/bin/env bash
# Discord alerting for scheduled, landing, and release failures, after moq-dev/moq's.
# Usage:
#   sh/alert.sh discord   Post the current workflow_run failure to Discord.
#   sh/alert.sh check     Verify alert.yml watches every alertable workflow
#                         and alerts a scheduled failure, timeout, or cancellation.
#
# Environment (discord):
#   DISCORD_WEBHOOK   Required. The #alerts channel webhook URL.
#   RUN_REPO          Repository, since the channel is shared.
#   RUN_NAME          Workflow name (github.event.workflow_run.name).
#   RUN_URL           Run html_url.
#   RUN_CONCLUSION    failure, timed_out, or cancelled.
#   RUN_EVENT         What triggered the failed run (schedule, push, ...).
#   RUN_REF           head_branch.
#   RUN_TITLE         display_title, usually the commit subject.
#   RUN_ACTOR         Triggering actor login.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
workflows=.github/workflows

# jq builds the body so a commit subject with quotes or newlines can't produce
# malformed JSON.
discord() {
    : "${DISCORD_WEBHOOK:?DISCORD_WEBHOOK is required}"

    local payload
    payload=$(jq -n \
        --arg title "${RUN_REPO:-rind} ${RUN_NAME:-workflow} ${RUN_CONCLUSION:-failed}" \
        --arg url "${RUN_URL:-}" \
        --arg desc "${RUN_TITLE:-}" \
        --arg ref "${RUN_REF:-unknown}" \
        --arg event "${RUN_EVENT:-unknown}" \
        --arg actor "${RUN_ACTOR:-unknown}" \
        '{
            embeds: [{
                title: $title,
                url: $url,
                description: $desc,
                color: 15548997,
                fields: [
                    { name: "Ref", value: $ref, inline: true },
                    { name: "Trigger", value: $event, inline: true },
                    { name: "Actor", value: $actor, inline: true }
                ]
            }]
        }')

    # A rejected webhook fails the run instead of dropping every future alert,
    # and a stalled endpoint fails in seconds instead of at the job timeout.
    curl -sS --fail-with-body -X POST \
        --connect-timeout 5 --max-time 15 \
        -H "Content-Type: application/json" \
        -d "$payload" \
        "$DISCORD_WEBHOOK"
}

# A workflow's name when a failure there would otherwise go unseen: it runs
# outside a pull request (whose failure shows on the PR) and outside a caller
# (whose run reports it). A workflow without a name can't be listed in
# alert.yml, so it is an error rather than a skip.
# shellcheck disable=SC2016 # A jq program, not a shell expansion.
alertable='
    (.on | if type == "string" then [.]
        elif type == "array" then .
        elif type == "object" then keys
        else error("cannot read on:") end) as $triggers
    | if $triggers - ["pull_request", "pull_request_target", "merge_group", "workflow_call"] == [] then empty
    elif (.name | type) != "string" or .name == "" then error("no top-level name:")
    else .name end'

# Scheduled runs alert on failure, timed_out, and cancelled. A job past its
# timeout-minutes ends cancelled, not timed_out, so timed_out alone misses a
# scheduled run that stops. Release and Dart release stay on failure and timed_out:
# a newer push cancels the run it supersedes.
# shellcheck disable=SC2016 # A jq program, not a shell expansion.
conclusions='
    def norm: gsub("[[:space:]]+"; " ") | gsub(" ?\\|\\| ?"; " || ") | sub("^ "; "") | sub(" $"; "");
    def lists($text):
        [$text | match("\\[[^\\[\\]]*\\]"; "g") | .string | fromjson];
    def alerts($sched; $push; $names; $event; $conclusion; $name):
        ($event == "schedule" and ($sched | index($conclusion) != null))
        or (($push | index($conclusion) != null) and ($names | index($name) != null));
    ($expr | norm) as $text
    | ($text | split(" || ")) as $arms
    | if ($arms | length) != 2 then
        error("alert if: expected a schedule arm or a release arm, got \($arms | length): \($text)")
      elif ($arms[0] | test("event == .schedule.")) | not then
        error("alert if: the first arm must match a scheduled run: \($arms[0])")
      elif ($arms[1] | test("\\.name")) | not then
        error("alert if: the second arm must match workflow names: \($arms[1])")
      else .
      end
    | (lists($arms[0])) as $sched_lists
    | (lists($arms[1])) as $push_lists
    | if ($sched_lists | length) != 1 or ($push_lists | length) != 2 then
        error("alert if: the schedule arm needs one list and the release arm two; got \($sched_lists | length) and \($push_lists | length)")
      else .
      end
    | ($sched_lists[0] | sort) as $sched
    | ($push_lists[0] | sort) as $push
    | ($push_lists[1] | sort) as $names
    | (["cancelled", "failure", "timed_out"] | sort) as $want_sched
    | (["failure", "timed_out"] | sort) as $want_push
    | (["Dart release", "Release"] | sort) as $want_names
    | if $sched != $want_sched then
        error("schedule arm alerts on " + ($sched | join(", ")) + "; want failure, timed_out, and cancelled")
      elif $push != $want_push then
        error("release arm alerts on " + ($push | join(", ")) + "; want failure and timed_out")
      elif $names != $want_names then
        error("release arm watches " + ($names | join(", ")) + "; want Release and Dart release")
      else .
      end
    | [
        ["schedule", "failure", "asan", true],
        ["schedule", "timed_out", "miri", true],
        ["schedule", "cancelled", "mutants", true],
        ["schedule", "success", "asan", false],
        ["schedule", "skipped", "coverage", false],
        ["workflow_dispatch", "cancelled", "asan", false],
        ["workflow_dispatch", "failure", "miri", false],
        ["push", "failure", "Release", true],
        ["push", "timed_out", "Dart release", true],
        ["push", "cancelled", "Release", false],
        ["push", "failure", "asan", false],
        ["schedule", "cancelled", "Release", true]
      ] as $cases
    | (
        reduce $cases[] as $case (
          [];
          (alerts($sched; $push; $names; $case[0]; $case[1]; $case[2])) as $got
          | if $got == $case[3] then .
            else . + ["\($case[0]) \($case[1]) \($case[2]): got \($got), want \($case[3])"]
            end
        )
      ) as $bad
    | if ($bad | length) > 0 then
        error("alert condition: " + ($bad | join("; ")))
      else
        "alert.yml alerts a scheduled failure, timeout, or cancellation"
      end
'

judge() {
    jq -nr --arg expr "$1" "$conclusions"
}

# The checker has to reject the condition this fixes, or a checker that always
# passes would hide a schedule arm that dropped cancelled again.
prove_conclusions() {
    local good bad err
    good=$(
        cat <<'EOF'
(github.event.workflow_run.event == 'schedule' && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
    )
    bad=$(
        cat <<'EOF'
(github.event.workflow_run.event == 'schedule' && contains(fromJSON('["failure", "timed_out"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
    )
    judge "$good" >/dev/null
    if err=$(judge "$bad" 2>&1); then
        echo "sh/alert.sh: conclusion check accepted a schedule arm without cancelled" >&2
        return 1
    fi
    if [[ "$err" != *cancelled* ]]; then
        echo "sh/alert.sh: a schedule arm without cancelled failed for another reason: $err" >&2
        return 1
    fi
}

check_conclusions() {
    local expr
    prove_conclusions
    expr=$(yq -r '.jobs.discord.if' "$workflows/alert.yml")
    if [[ -z "$expr" || "$expr" == null ]]; then
        echo "sh/alert.sh: alert.yml has no jobs.discord.if" >&2
        return 2
    fi
    judge "$expr"
}

check() {
    local file name expected=() watched
    shopt -s nullglob
    for file in "$workflows"/*.yml "$workflows"/*.yaml; do
        # Watching itself would be a trigger loop.
        [[ ! "$file" =~ /alert\.ya?ml$ ]] || continue
        if ! name=$(yq -o=json . "$file" | jq -r "$alertable"); then
            echo "sh/alert.sh: cannot classify $file" >&2
            return 2
        fi
        [[ -z "$name" ]] || expected+=("$name")
    done
    watched=$(yq '.on.workflow_run.workflows[]' "$workflows/alert.yml")

    if diff -u --label expected --label alert.yml \
        <(printf '%s\n' "${expected[@]}" | sort -u) <(sort -u <<<"$watched") >&2; then
        echo "alert.yml watches all ${#expected[@]} alertable workflows"
    else
        echo "alert.yml's workflow list is out of sync with $workflows/" >&2
        return 1
    fi
    check_conclusions
}

case "${1:-}" in
    discord) discord ;;
    check) check ;;
    *)
        echo "usage: sh/alert.sh discord|check" >&2
        exit 2
        ;;
esac
