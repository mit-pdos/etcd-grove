# Lessons from review

One entry per critique of a run: date, PR, what the user said, the rule it became (in `SKILL.md`).
- 2026-10-16, first batch (raft PRs, etcd#22395): reproduction tests were left in the session scratchpad and in
  scratch worktrees of the fork, which do not outlive the session. The user: put all the relevant files, like
  tests, on the PR branch. Rule: step 8, everything the report relies on goes in `notes/pr-verify/<repo>-<n>/`
  on the branch, with a README (what, which revision, how to run); the report links there.
