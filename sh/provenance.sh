#!/usr/bin/env bash
# Print the SLSA v1 build provenance predicate actions/attest writes for this
# workflow run, but naming COMMIT, reached through REF, as the source built.
# A release run can publish from a commit older than the one that started it,
# such as a release PR's commit that landed with later ones, or pyrind's
# tag, and the run's own predicate would name only the newer commit, which
# stays listed second as the workflow's source.
#
# Usage: sh/provenance.sh COMMIT REF
set -euo pipefail

usage="usage: sh/provenance.sh COMMIT REF"
commit=${1:?$usage}
ref=${2:?$usage}
[[ "$commit" =~ ^[0-9a-f]{40}$ ]] || {
    echo "sh/provenance.sh: $commit is not a full commit SHA" >&2
    exit 2
}

server=${GITHUB_SERVER_URL:?} repository=${GITHUB_REPOSITORY:?}
workflow_ref=${GITHUB_WORKFLOW_REF:?}
jq -n \
    --arg repo "$server/$repository" \
    --arg commit "$commit" --arg ref "$ref" \
    --arg run_sha "${GITHUB_SHA:?}" --arg run_ref "${GITHUB_REF:?}" \
    --arg path "${workflow_ref#"$repository"/}" \
    --arg builder "$server/$workflow_ref" \
    --arg event "${GITHUB_EVENT_NAME:?}" \
    --arg repository_id "${GITHUB_REPOSITORY_ID:?}" \
    --arg owner_id "${GITHUB_REPOSITORY_OWNER_ID:?}" \
    --arg runner "${RUNNER_ENVIRONMENT:?}" \
    --arg invocation "$server/$repository/actions/runs/${GITHUB_RUN_ID:?}/attempts/${GITHUB_RUN_ATTEMPT:?}" '
    {
        buildDefinition: {
            buildType: "https://actions.github.io/buildtypes/workflow/v1",
            externalParameters: {workflow: {ref: $run_ref, repository: $repo, path: ($path | split("@")[0])}},
            internalParameters: {github: {
                event_name: $event, repository_id: $repository_id,
                repository_owner_id: $owner_id, runner_environment: $runner}},
            resolvedDependencies: [
                {uri: "git+\($repo)@\($ref)", digest: {gitCommit: $commit}},
                {uri: "git+\($repo)@\($run_ref)", digest: {gitCommit: $run_sha}}
            ]
        },
        runDetails: {builder: {id: $builder}, metadata: {invocationId: $invocation}}
    }'
