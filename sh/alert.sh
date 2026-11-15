#!/usr/bin/env bash
# Discord alerts for scheduled and release runs that stop with nobody watching,
# after moq-dev/moq's. A scheduled cancellation posts only when a job exceeded
# its time limit (GitHub reports that as cancelled, not timed_out). A Release
# or Dart release cancellation always posts: a newer push does not cancel them.
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
#   GITHUB_TOKEN      Required to classify a scheduled cancellation.
#   RUN_ID            workflow_run id, required for that classification.
#   RUN_ATTEMPT       workflow_run attempt, required for that classification.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
workflows=.github/workflows

# Names of the workflows whose cancellations always post. alert.yml's release
# arm must list these and no others; judge reads this array, and is_release
# reads it too, so the poster and the checker cannot drift.
release_names=(
    Release
    "Dart release"
)

# GitHub's check-run annotation when a job passes timeout-minutes (or the
# 360-minute default). A hand cancel and a concurrency cancel say
# "The operation was canceled." instead, so the match is this whole prefix.
timeout_re='^The job has exceeded the maximum execution time of .+$'

# Posts one embed, unless this is a scheduled cancellation that is not a job
# time limit. Release and Dart release cancellations always post.
discord() {
    : "${DISCORD_WEBHOOK:?DISCORD_WEBHOOK is required}"

    local timeout=no status=0
    if [[ ${RUN_CONCLUSION:-} == cancelled ]] && ! is_release "${RUN_NAME:-}"; then
        cancellation_is_timeout || status=$?
        case $status in
            0) timeout=yes ;;
            1) timeout=no ;;
            *) return "$status" ;;
        esac
    fi
    if ! should_post "${RUN_CONCLUSION:-}" "${RUN_NAME:-}" "$timeout"; then
        echo "sh/alert.sh: not posting ${RUN_NAME:-workflow} conclusion ${RUN_CONCLUSION:-}; a scheduled cancellation posts only when a job exceeded its time limit"
        return 0
    fi

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

is_release() {
    local name="$1" each
    for each in "${release_names[@]}"; do
        [[ $name == "$each" ]] && return 0
    done
    return 1
}

# should_post <conclusion> <workflow name> <yes if a job exceeded its time limit>
# A failure or timed_out always posts. A cancellation posts for Release and
# Dart release, and for any other workflow only when the third argument is yes.
should_post() {
    local conclusion="$1" name="$2" timeout="$3"
    case $conclusion in
        failure | timed_out) return 0 ;;
        cancelled)
            if is_release "$name"; then
                return 0
            fi
            [[ $timeout == yes ]]
            ;;
        *) return 1 ;;
    esac
}

gh_get() {
    curl -sS --fail-with-body \
        --connect-timeout 5 --max-time 20 \
        -H "Authorization: Bearer ${GITHUB_TOKEN}" \
        -H "Accept: application/vnd.github+json" \
        -H "X-GitHub-Api-Version: 2022-11-28" \
        -- "$1"
}

# stdin: a JSON array of annotation messages. Exit 0 when one is a job time limit.
annotation_is_timeout() {
    jq -e --arg re "$timeout_re" \
        'type == "array" and any(.[]; type == "string" and test($re))' >/dev/null
}

# Exit 0 when this job's annotations say it exceeded its time limit, 1 when
# they do not, and 2 when the response is incomplete or not a list.
job_timed_out() {
    local id="$1" page=1 notes count messages
    while (( page <= 5 )); do
        notes=$(gh_get "https://api.github.com/repos/${RUN_REPO}/check-runs/${id}/annotations?per_page=100&page=${page}")
        if ! jq -e 'type == "array"' <<<"$notes" >/dev/null; then
            echo "sh/alert.sh: annotations for job ${id} were not a list" >&2
            return 2
        fi
        messages=$(jq -c '[.[] | .message | select(type == "string")]' <<<"$notes")
        if annotation_is_timeout <<<"$messages"; then
            return 0
        fi
        count=$(jq -r 'length' <<<"$notes")
        if (( count < 100 )); then
            return 1
        fi
        page=$((page + 1))
    done
    echo "sh/alert.sh: too many annotations on job ${id}" >&2
    return 2
}

# Exit 0 when a cancelled job on this attempt exceeded its time limit, 1 when
# none did, and 2 when the run id is unusable or a page is missing.
cancellation_is_timeout() {
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

    local page=1 jobs total count scanned=0 cancelled_ids id status
    while (( page <= 10 )); do
        jobs=$(gh_get "https://api.github.com/repos/${RUN_REPO}/actions/runs/${RUN_ID}/attempts/${RUN_ATTEMPT}/jobs?per_page=100&page=${page}")
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
            # A run cancelled before it had jobs has nothing to annotate.
            if (( total == 0 )); then
                return 1
            fi
            echo "sh/alert.sh: jobs page was empty before the list ended" >&2
            return 2
        fi
        scanned=$((scanned + count))
        cancelled_ids=$(jq -r '.jobs[] | select(.conclusion == "cancelled") | (.id | tostring)' <<<"$jobs")
        while IFS= read -r id; do
            [[ -n $id ]] || continue
            if [[ ! $id =~ ^[0-9]+$ ]]; then
                echo "sh/alert.sh: bad job id" >&2
                return 2
            fi
            status=0
            job_timed_out "$id" || status=$?
            case $status in
                0) return 0 ;;
                1) ;;
                *) return "$status" ;;
            esac
        done <<<"$cancelled_ids"
        if (( scanned >= total )); then
            return 1
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
    local conclusion="$1" name="$2" timeout="$3" want="$4" got=no
    if should_post "$conclusion" "$name" "$timeout"; then
        got=yes
    fi
    if [[ $got != "$want" ]]; then
        echo "sh/alert.sh prove: should_post ${conclusion} ${name} timeout=${timeout} got ${got}, want ${want}" >&2
        return 1
    fi
}

# These outcomes are the post policy. They are not derived from a list the
# checker already required to equal the expected list, so a wrong branch fails.
prove_post() {
    expect_post failure asan no yes
    expect_post timed_out miri no yes
    expect_post cancelled mutants yes yes
    expect_post cancelled mutants no no
    expect_post cancelled asan no no
    expect_post success asan no no
    expect_post cancelled Release no yes
    expect_post cancelled "Dart release" no yes
    expect_post failure Release no yes
    expect_post timed_out "Dart release" no yes
    expect_post cancelled asan yes yes
    # conclusion values other than failure, timed_out, and cancelled do not post.
    expect_post skipped coverage no no
}

prove_timeout() {
    local hit='["The job has exceeded the maximum execution time of 360m0s"]'
    local minutes='["The job has exceeded the maximum execution time of 360 minutes."]'
    local hand='["The operation was canceled."]'
    local both='["The operation was canceled.","The job has exceeded the maximum execution time of 1m0s"]'
    local loose='["exceeded the maximum execution time"]'
    local empty='[]'
    if ! annotation_is_timeout <<<"$hit"; then
        echo "sh/alert.sh prove: a time-limit annotation was not recognized" >&2
        return 1
    fi
    if ! annotation_is_timeout <<<"$minutes"; then
        echo "sh/alert.sh prove: a time-limit annotation in minutes was not recognized" >&2
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
    if annotation_is_timeout <<<"$empty"; then
        echo "sh/alert.sh prove: no annotations was treated as a time limit" >&2
        return 1
    fi
}

# discord() is the only poster. The fixtures never reach it unless it calls
# them; check does not run this.
prove_wires() {
    local body
    body=$(awk '/^discord\(\)/{p=1} p{print} p && /^}$/{exit}' "${BASH_SOURCE[0]}")
    if [[ $body != *should_post* || $body != *cancellation_is_timeout* ]]; then
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
        cancellation_is_timeout 2>&1
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
        cancellation_is_timeout 2>&1
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
    prove_wires
    prove_ids
    echo "sh/alert.sh prove: parser, post policy, and time-limit annotation"
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
