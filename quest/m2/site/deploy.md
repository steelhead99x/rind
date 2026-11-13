# [S] A merge to main deploys rind.kixel.ai

## Goal

`rind.kixel.ai` serves what `site/` builds from `main`, and every merge that changes the site or a file it reads deploys within the same CI run. The credential lives in a GitHub environment that only `main` can deploy to, so no pull request's workflow run can read it.

## Plan

Decided 2026-11-12 (maintainer, /quest-plan): ✅ Cloudflare, deployed by CI (rejected: `just deploy` by hand, as moq.dev does, which shows old numbers until someone remembers; GitHub Pages).

- A Cloudflare Worker that serves the build's static files, with `rind.kixel.ai` as its custom domain. kixel.ai's DNS is already on Cloudflare, and the name did not resolve on 2026-11-12, so nothing is displaced.
- The Worker serves each page's Markdown twin with a Markdown content type, and sets no cookie.
- The token is a secret of a `site` environment whose deployment branch rule allows `main` alone. The rule is what keeps it from a pull request, not the workflow's trigger: an environment's secrets go to any job that names it, a branch in this repository can add such a job to its own pull request, and the trigger is a line that pull request can edit. GitHub enforces the branch rule outside the workflow ([deployment branches and tags](https://docs.github.com/en/actions/reference/workflows-and-actions/deployments-and-environments#deployment-branches-and-tags)). A fork's pull request gets no secrets either way.
- Create the environment and its rule before the token exists, so it is never a secret without one: `gh api -X PUT repos/kixel-ai/rind/environments/site` with a custom deployment branch policy, then one policy named `main`. An agent with admin on the repository can do this step; only the secret's value needs the maintainer's Cloudflare login.
- Decided 2026-11-12 (maintainer, /quest-merge): ✅ the agent that does this quest creates the token itself, through the maintainer's signed-in browser (`agent-browser`), when it gets here (rejected: the maintainer creating it by hand). Not before: with no Worker and no `site` environment there is nowhere to put it, and a credential minted early only sits. Scope it to deploying this one Worker and attaching `rind.kixel.ai`, and add it with the account ID as the environment's secrets once the branch rule is in place. The value goes from Cloudflare's page to `gh secret set --env site` and nowhere else: not the PR, a log, or a file that outlives the command. If the browser is not signed in to Cloudflare, stop and ask.
- Check before the first deploy: `gh api repos/kixel-ai/rind/environments/site/deployment-branch-policies --jq '.branch_policies[].name'` prints `main` and nothing else, and `gh api repos/kixel-ai/rind/environments/site/secrets --jq '.secrets[].name'` lists both.
- The deploy job runs on a push to `main` and names that environment. It is the only job in any workflow that does, and it does nothing but build and deploy, so the token reaches no other step. Pull requests keep the build job [the landing page](/quest/m2/site/landing.md) added, which needs no secret.
- The deploy job has a `concurrency` group of its own with `cancel-in-progress: false`, so one deploy runs at a time, and it checks out `main` as it stands when the job starts, not the commit that started the run. The group alone orders nothing: it runs jobs in the order they began waiting, so a late or rerun job for an old commit would put its build back. Building `main`'s tip means whichever run goes last deploys the newest site.
- Deploy on any merge that changes `site/` or a file the build reads, and say in the workflow which files those are. If that list is hard to keep right, deploy on every merge: the build is small.
- A release redeploys too. [The migration pages](/quest/m2/site/migrate.md) print the versions crates.io holds, and release-plz's version bump merges to `main` before the crates publish, so the deploy that push starts can build too early. Run the deploy again when the release workflow finishes on `main`, and confirm the `site` environment's branch rule admits that run before relying on it.
- After the first deploy, fetch the site and its `llms.txt` from outside and put the result in the PR.

## Required

- [The landing page builds from the repository](/quest/m2/site/landing.md) - the `site/` project and its build job, which this deploys
