#!/usr/bin/env bash
# Discord alerts for scheduled and release runs that stop with nobody watching,
# after moq-dev/moq's. A scheduled cancellation posts only when a job exceeded
# its time limit (GitHub reports that as cancelled, not timed_out). The
# annotation is one of two sentences: timeout-minutes, or the hosted runner's
# 360-minute cap ("The job running on runner ..."). A Release or Dart release
# cancellation posts when a job started, unless the only cancel annotation is
# "Canceling since a higher priority waiting request": release.yml does not set
# queue: max, so a newer push cancels the pending publish behind the one that
# is running. A hand cancel of a job that started, and a time limit, still
# post. The jobs GET is retried. When it still cannot classify a
# cancellation, the embed posts and
# says so: no workflow watches Alert, so a failed classification would
# otherwise vanish.
# Usage:
#   sh/alert.sh discord   Post this workflow_run when it should alert.
#   sh/alert.sh check     Verify alert.yml's watch list and its if.
#   sh/alert.sh prove     Run this checker's fixtures. check does not call it.
#
# Environment (discord):
#   DISCORD_WEBHOOK   Required. The #alerts channel webhook URL.
#   RUN_REPO          Repository, since the channel is shared.
#   RUN_NAME          Workflow name (github.event.workflow_run.name).
#   RUN_URL           Run html_url.
#   RUN_CONCLUSION    failure, timed_out, or cancelled.
#   RUN_EVENT         What triggered the run (schedule, push, ...).
#   RUN_REF           head_branch.
#   RUN_TITLE         display_title, usually the commit subject.
#   RUN_ACTOR         Triggering actor login.
#   GITHUB_TOKEN      Required to classify a cancellation.
#   RUN_ID            workflow_run id, required for that classification.
#   RUN_ATTEMPT       workflow_run attempt, required for that classification.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
workflows=.github/workflows

# Names of the release workflows. alert.yml's release arm must list these and
# no others; judge reads this array, and is_release reads it too, so the
# poster and the checker cannot drift. A cancellation of one of these posts
# once a job has started, unless a newer push replaced a pending run.
release_names=(
    Release
    "Dart release"
)

# The two sentences GitHub writes when a job hits a time limit, whole
# annotation or not at all. timeout-minutes produces "The job has exceeded the
# maximum execution time of 59m0s". The hosted runner's own 360-minute cap,
# which asan, bench, coverage, miri, python, and dart-libraries hit because
# they set no timeout-minutes, produces "The job running on runner GitHub
# Actions N has exceeded the maximum execution time of 360 minutes." A hand
# cancel and a concurrency cancel do not match either sentence.
timeout_re='^(The job has exceeded the maximum execution time of .+|The job running on runner .+ has exceeded the maximum execution time of .+)$'
# A pending run replaced by a newer one in the same concurrency group. GitHub
# also writes "The operation was canceled." on that job; that line alone is
# not this reason.
replaced_re='^Canceling since a higher priority waiting request'
generic_re='^The operation was canceled\.$'

# Posts one embed. A scheduled cancellation posts only for a job time limit.
# A release cancellation posts once a job has started, unless the pending run
# was replaced. A cancellation that cannot be classified still posts, with
# that fact in the title.
discord() {
    : "${DISCORD_WEBHOOK:?DISCORD_WEBHOOK is required}"

    local class="" status=0
    if [[ ${RUN_CONCLUSION:-} == cancelled ]]; then
        # Do not fold this into `local`. `local x=$(...)` is always status 0,
        # which would hide a classification failure and drop the alert.
        class=$(classify_run) || status=$?
        if (( status != 0 )); then
            echo "sh/alert.sh: could not classify ${RUN_NAME:-workflow}; posting anyway" >&2
            post_discord "could not classify"
            return 0
        fi
    fi
    if ! should_post "${RUN_CONCLUSION:-}" "${RUN_NAME:-}" "$class"; then
        if is_release "${RUN_NAME:-}"; then
            if [[ $class == replaced ]]; then
                echo "sh/alert.sh: not posting ${RUN_NAME:-workflow}; a pending release a newer push replaced does not post"
            else
                echo "sh/alert.sh: not posting ${RUN_NAME:-workflow}; a release cancellation posts only after a job has started"
            fi
        else
            echo "sh/alert.sh: not posting ${RUN_NAME:-workflow} conclusion ${RUN_CONCLUSION:-}; a scheduled cancellation posts only when a job exceeded its time limit"
        fi
        return 0
    fi
    post_discord
}

# post_discord [note]
# note is appended to the title, so a failed classification reads
# "rind asan cancelled, could not classify" instead of a bare cancellation.
post_discord() {
    local note="${1:-}"
    local title="${RUN_REPO:-rind} ${RUN_NAME:-workflow} ${RUN_CONCLUSION:-failed}"
    if [[ -n $note ]]; then
        title="${title}, ${note}"
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
    http_curl -sS --fail-with-body -X POST \
        --connect-timeout 5 --max-time 15 \
        -H "Content-Type: application/json" \
        -d "$payload" \
        "$DISCORD_WEBHOOK"
}

is_release() {
    local name="$1" each
    for each in "${release_names[@]}"; do
        [[ $name == "$each" ]] && return 0
    done
    return 1
}

# should_post <conclusion> <workflow name> <class>
# class is timeout, started, never, or replaced, from classify_run. A failure
# or timed_out always posts. A release cancellation posts for a time limit or
# a job that started. It stays quiet when no job started, and when the only
# cancel annotation is a higher-priority waiting request: a pending run a
# newer push replaced, which can still carry started_at. Any other
# cancellation posts only when a job annotation is a time limit.
should_post() {
    local conclusion="$1" name="$2" class="$3"
    case $conclusion in
        failure | timed_out) return 0 ;;
        cancelled)
            if is_release "$name"; then
                case $class in
                    never | replaced) return 1 ;;
                    *) return 0 ;;
                esac
            fi
            [[ $class == timeout ]]
            ;;
        *) return 1 ;;
    esac
}

# One curl. prove replaces this function; production always runs curl.
http_curl() {
    command curl "$@"
}

# gh_get <url>
# A 502, a rate limit, or a dropped connection is retried. prove sets
# GH_GET_ATTEMPTS and GH_GET_BACKOFF; a run uses 3 attempts and waits one
# second between them. The last failure is returned so the caller can post
# that the cancellation could not be classified.
gh_get() {
    local url=$1 attempt=1 max=${GH_GET_ATTEMPTS:-3} wait=${GH_GET_BACKOFF:-1}
    local body status
    if [[ ! $max =~ ^[1-9][0-9]*$ || ! $wait =~ ^[0-9]+$ ]]; then
        echo "sh/alert.sh: GH_GET_ATTEMPTS and GH_GET_BACKOFF must be numbers" >&2
        return 2
    fi
    while (( attempt <= max )); do
        status=0
        body=$(http_curl -sS --fail-with-body \
            --connect-timeout 5 --max-time 20 \
            -H "Authorization: Bearer ${GITHUB_TOKEN}" \
            -H "Accept: application/vnd.github+json" \
            -H "X-GitHub-Api-Version: 2022-11-28" \
            -- "$url") || status=$?
        if (( status == 0 )); then
            printf '%s\n' "$body"
            return 0
        fi
        echo "sh/alert.sh: GET failed (${status}), attempt ${attempt} of ${max}" >&2
        if (( attempt == max )); then
            return "$status"
        fi
        if (( wait > 0 )); then
            sleep "$wait"
        fi
        attempt=$((attempt + 1))
    done
}

# stdin: a JSON array of annotation messages. Prints timeout, replaced,
# generic, or other. timeout is either time-limit sentence. replaced is the
# higher-priority waiting request, with or without the generic cancel line
# GitHub writes beside it. generic is only that line, or nothing. other is a
# hand cancel or any other note.
annotation_class() {
    jq -r --arg timeout "$timeout_re" --arg replaced "$replaced_re" --arg generic "$generic_re" '
        if type != "array" or any(.[]; type != "string") then "bad"
        elif any(.[]; test($timeout)) then "timeout"
        elif any(.[]; test($replaced)) and all(.[]; test($replaced) or test($generic)) then "replaced"
        elif all(.[]; test($generic)) then "generic"
        else "other"
        end'
}

# stdin: a JSON array of annotation messages. Exit 0 when one is a job time limit.
annotation_is_timeout() {
    local kind
    kind=$(annotation_class) || return 1
    [[ $kind == timeout ]]
}

# Print timeout, replaced, or other for this job. Exit 2 when a page is missing
# or not a list. A time-limit sentence wins. A higher-priority waiting request
# is replaced only when no page has any other reason. The generic cancel line
# does not decide the job.
job_cancel_class() {
    local id=$1 page=1 notes count messages kind
    local saw_replaced=no saw_other=no
    while (( page <= 5 )); do
        notes=$(gh_get "https://api.github.com/repos/${RUN_REPO}/check-runs/${id}/annotations?per_page=100&page=${page}") || {
            echo "sh/alert.sh: annotations request failed for job ${id}" >&2
            return 2
        }
        if ! jq -e 'type == "array"' <<<"$notes" >/dev/null; then
            echo "sh/alert.sh: annotations for job ${id} were not a list" >&2
            return 2
        fi
        messages=$(jq -c '[.[] | .message | select(type == "string")]' <<<"$notes")
        kind=$(annotation_class <<<"$messages") || {
            echo "sh/alert.sh: annotations for job ${id} could not be classified" >&2
            return 2
        }
        case $kind in
            timeout)
                echo timeout
                return 0
                ;;
            replaced) saw_replaced=yes ;;
            generic) ;;
            other) saw_other=yes ;;
            *)
                echo "sh/alert.sh: annotations for job ${id} could not be classified" >&2
                return 2
                ;;
        esac
        count=$(jq -r 'length' <<<"$notes")
        if [[ ! $count =~ ^[0-9]+$ ]]; then
            echo "sh/alert.sh: annotations for job ${id} could not be classified" >&2
            return 2
        fi
        if (( count < 100 )); then
            if [[ $saw_other == yes ]]; then
                echo other
            elif [[ $saw_replaced == yes ]]; then
                echo replaced
            else
                echo other
            fi
            return 0
        fi
        page=$((page + 1))
    done
    echo "sh/alert.sh: too many annotations on job ${id}" >&2
    return 2
}

# Reject a repository or run id that would change the request URL. Exit 2.
require_run_ids() {
    : "${GITHUB_TOKEN:?GITHUB_TOKEN is required to classify a cancellation}"
    : "${RUN_REPO:?RUN_REPO is required to classify a cancellation}"
    : "${RUN_ID:?RUN_ID is required to classify a cancellation}"
    : "${RUN_ATTEMPT:?RUN_ATTEMPT is required to classify a cancellation}"
    if [[ ! $RUN_REPO =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ || $RUN_REPO == *..* ]]; then
        echo "sh/alert.sh: RUN_REPO is not an owner/name" >&2
        return 2
    fi
    if [[ ! $RUN_ID =~ ^[0-9]+$ || ! $RUN_ATTEMPT =~ ^[0-9]+$ ]]; then
        echo "sh/alert.sh: RUN_ID and RUN_ATTEMPT must be numbers" >&2
        return 2
    fi
}

# Print timeout, started, never, or replaced. Exit 2 when the run id is
# unusable or a page is missing. timeout: a cancelled job's annotation is a
# time limit. started: some job has started_at, and the cancellation is not
# only a higher-priority waiting request. never: no job has started_at,
# including a run cancelled before it had jobs. replaced: a job may have
# started_at, but the only cancel annotation is a higher-priority waiting
# request, which is how a newer push replaces a pending Release.
classify_run() {
    require_run_ids || return $?

    local page=1 jobs total count scanned=0 started=no cancelled_ids id status
    local saw_replaced=no saw_other=no kind
    while (( page <= 10 )); do
        jobs=$(gh_get "https://api.github.com/repos/${RUN_REPO}/actions/runs/${RUN_ID}/attempts/${RUN_ATTEMPT}/jobs?per_page=100&page=${page}") || {
            echo "sh/alert.sh: jobs request failed" >&2
            return 2
        }
        if ! jq -e '.jobs | type == "array"' <<<"$jobs" >/dev/null; then
            echo "sh/alert.sh: jobs response has no list" >&2
            return 2
        fi
        total=$(jq -r '.total_count' <<<"$jobs")
        count=$(jq -r '.jobs | length' <<<"$jobs")
        if [[ ! $total =~ ^[0-9]+$ || ! $count =~ ^[0-9]+$ ]]; then
            echo "sh/alert.sh: jobs response has no total_count" >&2
            return 2
        fi
        if (( count == 0 )); then
            if (( total == 0 )); then
                echo never
                return 0
            fi
            echo "sh/alert.sh: jobs page was empty before the list ended" >&2
            return 2
        fi
        scanned=$((scanned + count))
        if jq -e 'any(.jobs[]; (.started_at | type) == "string" and (.started_at | length) > 0)' <<<"$jobs" >/dev/null; then
            started=yes
        fi
        cancelled_ids=$(jq -r '.jobs[] | select(.conclusion == "cancelled") | (.id | tostring)' <<<"$jobs")
        while IFS= read -r id; do
            [[ -n $id ]] || continue
            if [[ ! $id =~ ^[0-9]+$ ]]; then
                echo "sh/alert.sh: bad job id" >&2
                return 2
            fi
            status=0
            kind=$(job_cancel_class "$id") || status=$?
            if (( status != 0 )); then
                return "$status"
            fi
            case $kind in
                timeout)
                    echo timeout
                    return 0
                    ;;
                replaced) saw_replaced=yes ;;
                other) saw_other=yes ;;
                *)
                    echo "sh/alert.sh: bad cancel class for job ${id}" >&2
                    return 2
                    ;;
            esac
        done <<<"$cancelled_ids"
        if (( scanned >= total )); then
            if [[ $started == no ]]; then
                echo never
            elif [[ $saw_other == no && $saw_replaced == yes ]]; then
                echo replaced
            else
                echo started
            fi
            return 0
        fi
        page=$((page + 1))
    done
    echo "sh/alert.sh: stopped before reading every job (${scanned} of ${total})" >&2
    return 2
}

# A workflow's name when a failure there would otherwise go unseen. A pull
# request, a reusable caller, and a dispatch-only workflow are left out:
# someone is already watching those runs. A workflow without a name can't be
# listed in alert.yml, so it is an error rather than a skip.
# shellcheck disable=SC2016 # A jq program, not a shell expansion.
alertable='
    (.on | if type == "string" then [.]
        elif type == "array" then .
        elif type == "object" then keys
        else error("cannot read on:") end) as $triggers
    | if $triggers - ["pull_request", "pull_request_target", "merge_group", "workflow_call", "workflow_dispatch"] == [] then empty
    elif (.name | type) != "string" or .name == "" then error("no top-level name:")
    else .name end'

# The if is two arms joined by ||. Each arm is && of predicates. Operand order
# and list order do not matter. A predicate outside this shape, such as
# `&& false`, is rejected. Both arms alert on failure, timed_out, and
# cancelled: the schedule arm so a time-limit kill starts this job, and the
# release arm because a newer push does not cancel Release or Dart release.
# shellcheck disable=SC2016 # A jq program, not a shell expansion.
form='
def squeeze:
  reduce explode[] as $c (
    {q: null, out: [], skip: false};
    if .skip then
      .skip = false | .out += [$c]
    elif .q == 34 and $c == 92 then
      .skip = true | .out += [$c]
    elif .q != null then
      (if $c == .q then .q = null else . end) | .out += [$c]
    elif ($c == 39 or $c == 34) then
      .q = $c | .out += [$c]
    elif ($c == 32 or $c == 9 or $c == 10 or $c == 13) then
      .
    else .out += [$c]
    end
  )
  | if .q != null or .skip then error("unbalanced quote") else (.out | implode) end;

def split_top($op):
  . as $s
  | ($op | length) as $olen
  | reduce range(0; $s | length) as $i (
      {quote: null, depth: 0, start: 0, parts: [], skip: 0, esc: false};
      if .esc then .esc = false
      elif .skip > 0 then .skip -= 1
      elif .quote == "\"" and $s[$i:$i+1] == "\\" then .esc = true
      elif .quote != null then
        if $s[$i:$i+1] == .quote then .quote = null else . end
      elif ($s[$i:$i+1] == "\u0027") or ($s[$i:$i+1] == "\"") then .quote = $s[$i:$i+1]
      elif $s[$i:$i+1] == "(" then .depth += 1
      elif $s[$i:$i+1] == ")" then
        if .depth == 0 then error("unbalanced )") else .depth -= 1 end
      elif .depth == 0 and $s[$i:$i+$olen] == $op then
        .parts += [$s[.start:$i]] | .start = ($i + $olen) | .skip = ($olen - 1)
      else . end
    )
  | if .quote != null or .esc then error("unbalanced quote")
    elif .depth != 0 then error("unbalanced (")
    else (.parts + [$s[.start:]])
    end;

def wraps:
  . as $s
  | if (($s | startswith("(")) and ($s | endswith(")"))) | not then false
    else
      reduce range(0; ($s | length) - 1) as $i (
        {quote: null, depth: 0, closed: false, esc: false};
        if .closed or .esc then
          if .esc then .esc = false else . end
        elif .quote == "\"" and $s[$i:$i+1] == "\\" then .esc = true
        elif .quote != null then
          if $s[$i:$i+1] == .quote then .quote = null else . end
        elif ($s[$i:$i+1] == "\u0027") or ($s[$i:$i+1] == "\"") then .quote = $s[$i:$i+1]
        elif $s[$i:$i+1] == "(" then .depth += 1
        elif $s[$i:$i+1] == ")" then
          .depth -= 1
          | if .depth == 0 then .closed = true else . end
        else . end
      )
      | (.closed | not) and .depth == 1 and .quote == null and (.esc | not)
    end;

def unwrap: squeeze | if wraps then .[1:-1] | unwrap else . end;

def unquote:
  . as $s
  | if ($s | length) < 2 then error("not a quoted string: \($s)")
    else ($s[0:1]) as $q
    | if ($s[-1:] != $q) or ($q != "\u0027" and $q != "\"") then error("not a quoted string: \($s)")
      elif $q == "\u0027" then $s[1:-1]
      else ("\"" + $s[1:-1] + "\"" | fromjson)
      end
    end;

def string_list:
  if type != "array" or any(.[]; type != "string") then
    error("expected a list of strings")
  else unique
  end;

def parse_atom:
  unwrap
  | if startswith("github.event.workflow_run.event==") then
      (.[("github.event.workflow_run.event==" | length):]) as $rest
      | if ($rest | startswith("\u0027") or startswith("\"")) | not then
          error("unsupported predicate: \(.)")
        else {kind: "event", value: ($rest | unquote)}
        end
    elif startswith("contains(") and endswith(")") then
      (.[("contains(" | length):-1] | split_top(",")) as $args
      | if ($args | length) != 2 then error("unsupported predicate: \(.)")
        elif ($args[0] | startswith("fromJSON(") and endswith(")")) | not then
          error("unsupported predicate: \(.)")
        else
          ($args[0] | .[("fromJSON(" | length):-1] | unquote | fromjson | string_list) as $vals
          | if $args[1] == "github.event.workflow_run.conclusion" then
              {kind: "conclusion", values: $vals}
            elif $args[1] == "github.event.workflow_run.name" then
              {kind: "name", values: $vals}
            else error("unsupported predicate: \(.)")
            end
        end
    else error("unsupported predicate: \(.)")
    end;

def parse_and:
  unwrap
  | split_top("&&")
  | if any(.[]; length == 0) then error("unsupported predicate: empty")
    else map(parse_atom)
    | if (map(.kind) | unique | length) != length then error("duplicate predicate")
      else sort_by(.kind)
      end
    end;

def parse_or:
  unwrap
  | split_top("||")
  | if any(.[]; length == 0) then error("unsupported predicate: empty")
    else map(parse_and) | sort_by(tostring)
    end;

def want($names):
  def conclusions: ["cancelled", "failure", "timed_out"];
  [
    [{kind: "conclusion", values: conclusions}, {kind: "event", value: "schedule"}],
    [{kind: "conclusion", values: conclusions}, {kind: "name", values: ($names | unique)}]
  ] | map(sort_by(.kind)) | sort_by(tostring);

($expr | parse_or) as $got
| want($names) as $expect
| if $got == $expect then "alert.yml uses the supported schedule and release form"
  else error("alert condition is not the supported form: " + ($got | tojson))
  end
'

judge() {
    local names
    names=$(jq -nc --args '$ARGS.positional' -- "${release_names[@]}")
    jq -nr --arg expr "$1" --argjson names "$names" "$form"
}

# The discord step needs actions:read to list the run's jobs and checks:read
# to read the time-limit annotation. Without the run id it cannot tell a
# time-limit kill from a cancel somebody asked for.
check_wiring() {
    local actions checks token run_id attempt
    local token_expr run_id_expr attempt_expr
    actions=$(yq -r '.permissions.actions // ""' "$workflows/alert.yml")
    checks=$(yq -r '.permissions.checks // ""' "$workflows/alert.yml")
    token=$(yq -r '.jobs.discord.steps[] | select(.name == "Post to Discord") | .env.GITHUB_TOKEN // ""' "$workflows/alert.yml")
    run_id=$(yq -r '.jobs.discord.steps[] | select(.name == "Post to Discord") | .env.RUN_ID // ""' "$workflows/alert.yml")
    attempt=$(yq -r '.jobs.discord.steps[] | select(.name == "Post to Discord") | .env.RUN_ATTEMPT // ""' "$workflows/alert.yml")
    # shellcheck disable=SC2016 # GitHub expressions, compared as text.
    token_expr='${{ github.token }}'
    # shellcheck disable=SC2016 # GitHub expressions, compared as text.
    run_id_expr='${{ github.event.workflow_run.id }}'
    # shellcheck disable=SC2016 # GitHub expressions, compared as text.
    attempt_expr='${{ github.event.workflow_run.run_attempt }}'
    if [[ $actions != read || $checks != read ]]; then
        echo "sh/alert.sh: alert.yml needs permissions actions: read and checks: read to classify a cancellation" >&2
        return 1
    fi
    if [[ $token != "$token_expr" ]]; then
        echo "sh/alert.sh: alert.yml must pass github.token as GITHUB_TOKEN" >&2
        return 1
    fi
    if [[ $run_id != "$run_id_expr" ]]; then
        echo "sh/alert.sh: alert.yml must pass workflow_run.id as RUN_ID" >&2
        return 1
    fi
    if [[ $attempt != "$attempt_expr" ]]; then
        echo "sh/alert.sh: alert.yml must pass workflow_run.run_attempt as RUN_ATTEMPT" >&2
        return 1
    fi
}

check() {
    local file name expected=() watched
    shopt -s nullglob
    for file in "$workflows"/*.yml "$workflows"/*.yaml; do
        # Watching itself would be a trigger loop.
        [[ ! $file =~ /alert\.ya?ml$ ]] || continue
        if ! name=$(yq -o=json . "$file" | jq -r "$alertable"); then
            echo "sh/alert.sh: cannot classify $file" >&2
            return 2
        fi
        [[ -z $name ]] || expected+=("$name")
    done
    watched=$(yq '.on.workflow_run.workflows[]' "$workflows/alert.yml")

    if diff -u --label expected --label alert.yml \
        <(printf '%s\n' "${expected[@]}" | sort -u) <(sort -u <<<"$watched") >&2; then
        echo "alert.yml watches all ${#expected[@]} alertable workflows"
    else
        echo "alert.yml's workflow list is out of sync with $workflows/" >&2
        return 1
    fi
    check_wiring
    local expr
    expr=$(yq -r '.jobs.discord.if' "$workflows/alert.yml")
    if [[ -z $expr || $expr == null ]]; then
        echo "sh/alert.sh: alert.yml has no jobs.discord.if" >&2
        return 2
    fi
    judge "$expr"
}

expect_ok() {
    local label=$1 expr=$2 out
    if ! out=$(judge "$expr" 2>&1); then
        echo "sh/alert.sh prove: ${label} was rejected: ${out}" >&2
        return 1
    fi
    if [[ $out != *"supported schedule and release form"* ]]; then
        echo "sh/alert.sh prove: ${label} did not report a pass: ${out}" >&2
        return 1
    fi
}

expect_fail() {
    local label=$1 expr=$2 needle=$3 out
    if out=$(judge "$expr" 2>&1); then
        echo "sh/alert.sh prove: ${label} was accepted: ${out}" >&2
        return 1
    fi
    if [[ $out != *"$needle"* ]]; then
        echo "sh/alert.sh prove: ${label} failed for another reason: ${out}" >&2
        return 1
    fi
}

# Fixtures for the parser. They are not run from check: a failure here means
# the checker is wrong, not that alert.yml is.
prove_form() {
    local good swapped loose dot disabled
    good=$(cat <<'EOF'
(github.event.workflow_run.event == 'schedule' && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)
    swapped=$(cat <<'EOF'
(contains(fromJSON('["Dart release", "Release"]'), github.event.workflow_run.name) && contains(fromJSON('["cancelled", "failure", "timed_out"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["timed_out", "cancelled", "failure"]'), github.event.workflow_run.conclusion) && github.event.workflow_run.event == "schedule")
EOF
)
    expect_ok "supported form" "$good"
    expect_ok "reordered arms and operands" "$swapped"
    expect_fail "schedule arm without cancelled" "$(cat <<'EOF'
(github.event.workflow_run.event == 'schedule' && contains(fromJSON('["failure", "timed_out"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)" "not the supported form"
    expect_fail "release arm without cancelled" "$(cat <<'EOF'
(github.event.workflow_run.event == 'schedule' && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)" "not the supported form"
    disabled=$(cat <<'EOF'
(github.event.workflow_run.event == 'schedule' && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && false) || (contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)
    expect_fail "added && false" "$disabled" "unsupported predicate: false"
    loose=$(cat <<'EOF'
(github.event.workflow_run.event == xschedulex && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)
    expect_fail "unquoted event" "$loose" "unsupported predicate"
    dot=$(cat <<'EOF'
(github.event.workflow_run.event == .schedule. && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)
    expect_fail "dot standing in for a quote" "$dot" "unsupported predicate"
    expect_fail "quoted event that merely contains schedule" "$(cat <<'EOF'
(github.event.workflow_run.event == 'xschedulex' && contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion)) || (contains(fromJSON('["failure", "timed_out", "cancelled"]'), github.event.workflow_run.conclusion) && contains(fromJSON('["Release", "Dart release"]'), github.event.workflow_run.name))
EOF
)" "xschedulex"
}

expect_post() {
    local conclusion="$1" name="$2" class="$3" want="$4" got=no
    if should_post "$conclusion" "$name" "$class"; then
        got=yes
    fi
    if [[ $got != "$want" ]]; then
        echo "sh/alert.sh prove: should_post ${conclusion} ${name} class=${class} got ${got}, want ${want}" >&2
        return 1
    fi
}

# These outcomes are the post policy. They are not derived from a list the
# checker already required to equal the expected list, so a wrong branch fails.
prove_post() {
    expect_post failure asan started yes
    expect_post timed_out miri started yes
    expect_post cancelled mutants timeout yes
    expect_post cancelled mutants started no
    expect_post cancelled mutants never no
    expect_post cancelled asan started no
    expect_post success asan started no
    # A release that started posts, including a hand cancel with no time-limit
    # annotation. One that never started is the pending run a newer push replaced.
    expect_post cancelled Release started yes
    expect_post cancelled Release never no
    expect_post cancelled Release replaced no
    expect_post cancelled Release timeout yes
    expect_post cancelled "Dart release" started yes
    expect_post cancelled "Dart release" never no
    expect_post cancelled "Dart release" replaced no
    expect_post cancelled asan replaced no
    expect_post failure Release started yes
    expect_post timed_out "Dart release" started yes
    expect_post cancelled asan timeout yes
    # conclusion values other than failure, timed_out, and cancelled do not post.
    expect_post skipped coverage started no
}

prove_timeout() {
    local hit='["The job has exceeded the maximum execution time of 360m0s"]'
    local minutes='["The job has exceeded the maximum execution time of 360 minutes."]'
    local runner='["The job running on runner GitHub Actions 2 has exceeded the maximum execution time of 360 minutes."]'
    local hand='["The operation was canceled."]'
    local both='["The operation was canceled.","The job has exceeded the maximum execution time of 1m0s"]'
    local loose='["exceeded the maximum execution time"]'
    local wrapped='["Note: The job has exceeded the maximum execution time of 1m0s"]'
    local runner_cut='["The job running on runner GitHub Actions 2 has exceeded"]'
    local waiting='["Canceling since a higher priority waiting request for release exists"]'
    local minutes_short='["The job has exceeded the maximum execution time of 59m0s"]'
    local empty='[]'
    if ! annotation_is_timeout <<<"$hit"; then
        echo "sh/alert.sh prove: a time-limit annotation was not recognized" >&2
        return 1
    fi
    if ! annotation_is_timeout <<<"$minutes"; then
        echo "sh/alert.sh prove: a time-limit annotation in minutes was not recognized" >&2
        return 1
    fi
    if ! annotation_is_timeout <<<"$runner"; then
        echo "sh/alert.sh prove: a runner time-limit annotation was not recognized" >&2
        return 1
    fi
    if annotation_is_timeout <<<"$hand"; then
        echo "sh/alert.sh prove: a hand cancel was treated as a time limit" >&2
        return 1
    fi
    if ! annotation_is_timeout <<<"$both"; then
        echo "sh/alert.sh prove: a time-limit annotation beside a cancel was missed" >&2
        return 1
    fi
    if annotation_is_timeout <<<"$loose"; then
        echo "sh/alert.sh prove: a partial time-limit phrase was accepted" >&2
        return 1
    fi
    if annotation_is_timeout <<<"$wrapped"; then
        echo "sh/alert.sh prove: a time-limit sentence with a prefix was accepted" >&2
        return 1
    fi
    if annotation_is_timeout <<<"$runner_cut"; then
        echo "sh/alert.sh prove: a partial runner sentence was accepted" >&2
        return 1
    fi
    if annotation_is_timeout <<<"$waiting"; then
        echo "sh/alert.sh prove: a higher-priority waiting request was treated as a time limit" >&2
        return 1
    fi
    if ! annotation_is_timeout <<<"$minutes_short"; then
        echo "sh/alert.sh prove: a timeout-minutes annotation was not recognized" >&2
        return 1
    fi
    if annotation_is_timeout <<<"$empty"; then
        echo "sh/alert.sh prove: no annotations was treated as a time limit" >&2
        return 1
    fi
}

expect_class() {
    local label=$1 messages=$2 want=$3 got
    got=$(annotation_class <<<"$messages") || {
        echo "sh/alert.sh prove: ${label} could not be classified" >&2
        return 1
    }
    if [[ $got != "$want" ]]; then
        echo "sh/alert.sh prove: ${label} got ${got}, want ${want}" >&2
        return 1
    fi
}

# The phrases GitHub writes, including the generic cancel line it pairs with
# a real reason. These do not go through the network.
prove_class() {
    expect_class "runner time limit" \
        '["The job running on runner GitHub Actions 2 has exceeded the maximum execution time of 360 minutes."]' \
        timeout
    expect_class "timeout-minutes" \
        '["The job has exceeded the maximum execution time of 59m0s"]' \
        timeout
    expect_class "waiting request" \
        '["Canceling since a higher priority waiting request for release exists"]' \
        replaced
    expect_class "waiting request beside the generic cancel" \
        '["The operation was canceled.","Canceling since a higher priority waiting request for release exists"]' \
        replaced
    expect_class "hand cancel" \
        '["The operation was canceled.","The run was canceled by @octocat."]' \
        other
    expect_class "generic cancel alone" '["The operation was canceled."]' generic
    expect_class "empty" '[]' generic
    expect_class "timeout beside a waiting request" \
        '["Canceling since a higher priority waiting request for release exists","The job running on runner GitHub Actions 4 has exceeded the maximum execution time of 360 minutes."]' \
        timeout
}

# discord under a stand-in for curl. A failing GET is tried three times. A
# cancellation that is still unclassified posts and exits 0. A confident
# non-timeout stays quiet. A Release posts for a hand cancel and a time limit,
# and stays quiet when the job never started or the only cancel annotation is
# a higher-priority waiting request.
prove_http() {
    local dir status=0
    dir=$(mktemp -d)
    prove_http_cases "$dir" || status=$?
    rm -rf "$dir"
    return "$status"
}

prove_http_cases() {
    local dir=$1
    # `|| return` so a failed fixture stops the rest even when this function
    # is reached from `||`, which turns set -e off.
    expect_discord "$dir" exhaust asan yes classify || return
    expect_discord "$dir" retry-empty Release no quiet || return
    expect_discord "$dir" retry-timeout asan yes posted || return
    expect_discord "$dir" hand asan no quiet || return
    expect_discord "$dir" hand Release yes posted || return
    expect_discord "$dir" waiting Release no quiet || return
    expect_discord "$dir" timeout Release yes posted || return
    expect_discord "$dir" unstarted Release no quiet || return
}

expect_discord() {
    local dir=$1 mode=$2 name=$3 want_post=$4 want_title=$5
    local status=0 out n posted
    rm -f "$dir/urls" "$dir/posted" "$dir/err"
    out=$(
        export GH_GET_ATTEMPTS=3 GH_GET_BACKOFF=0
        export RUN_REPO=kixel-ai/rind RUN_ID=9 RUN_ATTEMPT=1 GITHUB_TOKEN=t
        export DISCORD_WEBHOOK=https://discord.example/hook
        export RUN_CONCLUSION=cancelled RUN_NAME="$name" RUN_URL=https://example/run
        export RUN_TITLE=nightly RUN_REF=main RUN_EVENT=schedule RUN_ACTOR=octocat
        export STUB_MODE=$mode STUB_DIR=$dir
        exec 2>"$STUB_DIR/err"
        http_curl() {
            local arg url="" piece=""
            for arg in "$@"; do
                url=$arg
            done
            printf '%s\n' "$url" >>"$STUB_DIR/urls"
            case $url in
                *api.github.com*) stub_api "$url" ;;
                *)
                    for piece in "$@"; do
                        if [[ $piece == '{'* ]]; then
                            printf '%s\n' "$piece" >"$STUB_DIR/posted"
                        fi
                    done
                    ;;
            esac
        }
        stub_api() {
            local url=$1 n
            n=$(wc -l <"$STUB_DIR/urls")
            case $STUB_MODE in
                exhaust) return 22 ;;
                retry-empty)
                    if (( n < 3 )); then
                        return 22
                    fi
                    printf '%s\n' '{"total_count":0,"jobs":[]}'
                    ;;
                retry-timeout)
                    if [[ $url == *'/jobs?'* ]] && (( n == 1 )); then
                        return 22
                    fi
                    if [[ $url == *'/jobs?'* ]]; then
                        printf '%s\n' '{"total_count":1,"jobs":[{"id":42,"conclusion":"cancelled","started_at":"2026-11-15T00:00:00Z"}]}'
                        return 0
                    fi
                    printf '%s\n' '[{"message":"The job running on runner GitHub Actions 2 has exceeded the maximum execution time of 360 minutes."}]'
                    ;;
                unstarted)
                    if [[ $url == *'/jobs?'* ]]; then
                        printf '%s\n' '{"total_count":1,"jobs":[{"id":42,"conclusion":"cancelled","started_at":null}]}'
                        return 0
                    fi
                    printf '%s\n' '[{"message":"The run was canceled by @octocat."}]'
                    ;;
                *)
                    if [[ $url == *'/jobs?'* ]]; then
                        printf '%s\n' '{"total_count":1,"jobs":[{"id":42,"conclusion":"cancelled","started_at":"2026-11-15T00:00:00Z"}]}'
                        return 0
                    fi
                    case $STUB_MODE in
                        hand)
                            printf '%s\n' '[{"message":"The operation was canceled."},{"message":"The run was canceled by @octocat."}]'
                            ;;
                        waiting)
                            printf '%s\n' '[{"message":"The operation was canceled."},{"message":"Canceling since a higher priority waiting request for release exists"}]'
                            ;;
                        timeout)
                            printf '%s\n' '[{"message":"The job running on runner GitHub Actions 12 has exceeded the maximum execution time of 360 minutes."}]'
                            ;;
                        *)
                            echo "sh/alert.sh prove: unknown stub ${STUB_MODE}" >&2
                            return 2
                            ;;
                    esac
                    ;;
            esac
        }
        discord
    ) 2>"$dir/err" || status=$?
    if [[ $status -ne 0 ]]; then
        echo "sh/alert.sh prove: ${mode} ${name} exited ${status}: ${out} $(cat "$dir/err")" >&2
        return 1
    fi
    posted=no
    if [[ -f $dir/posted ]]; then
        posted=yes
    fi
    if [[ $posted != "$want_post" ]]; then
        echo "sh/alert.sh prove: ${mode} ${name} posted ${posted}, want ${want_post}: $(cat "$dir/err")" >&2
        return 1
    fi
    n=$(grep -c 'api.github.com' "$dir/urls")
    case $mode in
        exhaust | retry-empty | retry-timeout)
            if (( n != 3 )); then
                echo "sh/alert.sh prove: ${mode} tried the GET ${n} times, want 3" >&2
                return 1
            fi
            ;;
    esac
    if [[ $want_title == classify ]]; then
        if [[ $(cat "$dir/posted") != *'could not classify'* ]]; then
            echo "sh/alert.sh prove: ${mode} ${name} did not say the cancellation could not be classified" >&2
            return 1
        fi
    elif [[ $want_title == posted && $(cat "$dir/posted") == *'could not classify'* ]]; then
        echo "sh/alert.sh prove: ${mode} ${name} was titled as unclassified" >&2
        return 1
    fi
}

# discord() is the only poster. The fixtures never reach it unless it calls
# them; check does not run this.
prove_wires() {
    local body
    body=$(awk '/^discord\(\)/{p=1} p{print} p && /^}$/{exit}' "${BASH_SOURCE[0]}")
    if [[ $body != *should_post* || $body != *classify_run* || $body != *"could not classify"* ]]; then
        echo "sh/alert.sh prove: discord() does not classify a cancellation before posting" >&2
        return 1
    fi
}

# A run id or repository that is not a single path segment must fail before
# any request, so it cannot change which URL is fetched.
prove_ids() {
    local status err
    status=0
    err=$(
        RUN_REPO='../nope'
        RUN_ID=1
        RUN_ATTEMPT=1
        GITHUB_TOKEN=t
        classify_run 2>&1
    ) || status=$?
    if [[ $status -ne 2 || $err != *owner/name* ]]; then
        echo "sh/alert.sh prove: a repository of '../nope' was not rejected (status ${status}): ${err}" >&2
        return 1
    fi
    status=0
    err=$(
        RUN_REPO='kixel-ai/rind'
        RUN_ID='1;rm'
        RUN_ATTEMPT=1
        GITHUB_TOKEN=t
        classify_run 2>&1
    ) || status=$?
    if [[ $status -ne 2 || $err != *numbers* ]]; then
        echo "sh/alert.sh prove: a non-numeric run id was not rejected (status ${status}): ${err}" >&2
        return 1
    fi
}

prove() {
    prove_form
    prove_post
    prove_timeout
    prove_class
    prove_http
    prove_wires
    prove_ids
    echo "sh/alert.sh prove: parser, post policy, time-limit annotation, and classification"
}

case ${1:-} in
    discord) discord ;;
    check) check ;;
    prove) prove ;;
    *)
        echo "usage: sh/alert.sh discord|check|prove" >&2
        exit 2
        ;;
esac
