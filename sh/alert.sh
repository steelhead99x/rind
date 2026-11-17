#!/usr/bin/env bash
# Discord alerting for scheduled, landing, and release failures, after moq-dev/moq's.
# Usage:
#   sh/alert.sh discord   Post the current workflow_run failure to Discord.
#   sh/alert.sh check     Verify alert.yml watches every alertable workflow,
#                         and that no push can cancel a release it alerts on.
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

# True when no concurrency group in a workflow replaces a pending run: each
# one is an object with `queue: max` and without cancel-in-progress.
# shellcheck disable=SC2016 # A jq program, not a shell expansion.
queues='
    [.concurrency, (.jobs // {} | .[].concurrency)] | map(select(. != null))
    | all(type == "object" and .queue == "max" and (.["cancel-in-progress"] // false) == false)'

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
        # alert.yml posts every cancelled release, which is right only while
        # no push can cancel one: each concurrency group must queue.
        case "$name" in
            Release | "Dart release")
                if ! yq -o=json . "$file" | jq -e "$queues" >/dev/null; then
                    echo "sh/alert.sh: a push can cancel a pending $name run, which alert.yml would post; give $file's concurrency groups queue: max" >&2
                    return 1
                fi
                ;;
        esac
    done
    watched=$(yq '.on.workflow_run.workflows[]' "$workflows/alert.yml")

    if diff -u --label expected --label alert.yml \
        <(printf '%s\n' "${expected[@]}" | sort -u) <(sort -u <<<"$watched") >&2; then
        echo "alert.yml watches all ${#expected[@]} alertable workflows"
    else
        echo "alert.yml's workflow list is out of sync with $workflows/" >&2
        return 1
    fi
}

case "${1:-}" in
    discord) discord ;;
    check) check ;;
    *)
        echo "usage: sh/alert.sh discord|check" >&2
        exit 2
        ;;
esac
