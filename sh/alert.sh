#!/usr/bin/env bash
# Discord alerting for scheduled, landing, and release failures, after moq-dev/moq's.
# Usage:
#   sh/alert.sh discord    Post the current workflow_run failure to Discord.
#   sh/alert.sh timed-out  Print yes when a cancelled job of the run hit its
#                          time limit, no when none did.
#   sh/alert.sh check      Verify alert.yml watches every alertable workflow.
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
#   RUN_ID            Run id, to classify a cancellation.
#   RUN_ATTEMPT       Run attempt, to classify a cancellation.
#   GH_TOKEN          Token with actions: read and checks: read, for the same.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
workflows=.github/workflows

# jq builds the body so a commit subject with quotes or newlines can't produce
# malformed JSON.
discord() {
    : "${DISCORD_WEBHOOK:?DISCORD_WEBHOOK is required}"

    # A job past its time limit ends cancelled, not timed_out, and so does a
    # run that a hand cancel, a newer run in its concurrency group, or a
    # pending Release behind another stops. Only the first is an alert. A
    # cancellation that can't be classified still posts: nothing watches
    # Alert, so dropping it would hide the hang it may be.
    local title="${RUN_REPO:-rind} ${RUN_NAME:-workflow} ${RUN_CONCLUSION:-failed}" verdict
    if [[ ${RUN_CONCLUSION:-} == cancelled ]]; then
        # A deadline leaves the 5-minute job time to post.
        if ! verdict=$(timeout 120 sh/alert.sh timed-out); then
            title+=", could not tell whether it hit a time limit"
        elif [[ $verdict == no ]]; then
            echo "not posting: no cancelled job of the run hit its time limit"
            return 0
        else
            title+=" at its time limit"
        fi
    fi

    local payload
    payload=$(jq -n \
        --arg title "$title" \
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

# Both forms GitHub writes: "The job has exceeded the maximum execution time
# of 1h0m0s" for timeout-minutes, and "The job running on runner ... has
# exceeded the maximum execution time of 360 minutes." for the hosted limit.
timed_out() {
    : "${RUN_REPO:?}" "${RUN_ID:?}" "${RUN_ATTEMPT:?}" "${GH_TOKEN:?}"
    local jobs id hits
    # Assignments, not pipes or conditions, so errexit fails on a bad request.
    jobs=$(gh api --paginate "repos/$RUN_REPO/actions/runs/$RUN_ID/attempts/$RUN_ATTEMPT/jobs?per_page=100" \
        --jq '.jobs[] | select(.conclusion == "cancelled") | .id')
    for id in $jobs; do
        hits=$(gh api --paginate "repos/$RUN_REPO/check-runs/$id/annotations?per_page=100" \
            --jq '.[].message | select(test("has exceeded the maximum execution time of "))')
        if [[ -n $hits ]]; then
            echo yes
            return 0
        fi
    done
    echo no
}

# A workflow's name when a failure there would otherwise go unseen: it runs
# outside a pull request (whose failure shows on the PR), outside a caller
# (whose run reports it), and outside a manual dispatch (whose dispatcher is
# watching it). A workflow without a name can't be listed in
# alert.yml, so it is an error rather than a skip.
# shellcheck disable=SC2016 # A jq program, not a shell expansion.
alertable='
    (.on | if type == "string" then [.]
        elif type == "array" then .
        elif type == "object" then keys
        else error("cannot read on:") end) as $triggers
    | if $triggers - ["pull_request", "pull_request_target", "merge_group", "workflow_call", "workflow_dispatch"] == [] then empty
    elif (.name | type) != "string" or .name == "" then error("no top-level name:")
    else .name end'

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
}

case "${1:-}" in
    discord) discord ;;
    timed-out) timed_out ;;
    check) check ;;
    *)
        echo "usage: sh/alert.sh discord|timed-out|check" >&2
        exit 2
        ;;
esac
