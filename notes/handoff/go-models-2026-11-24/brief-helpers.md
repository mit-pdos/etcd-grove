# Go-model overlays, stages S2–S7: common helper brief

You are a helper of the lead for the rest of the Go-model overlays plan (perennial#692). You own ONE work unit
(named in your prompt). Report to the lead only (your final message). Upamanyu reviews everything at the end as one
packet; nothing trusted lands.

## Read first
- The approved plan: /home/ubuntu/.claude-E/jobs/b20ef685/tmp/plan-go-models.md (§1 survey row of your packages,
  §2 mechanism, §4 trust claim, §5 for sync, §6 stages).
- S1's PR body, the format your packet section copies: `GH_TOKEN=$(cat ~/.config/gh-token) gh api
  repos/mit-pdos/perennial/pulls/697 --jq .body` (use REST; `gh pr view` may fail).
- S1 on Perennial `lean` (54a29571e) is the worked example: `goose/model/overlay/**`, `Perennial/Code/{strings,
  internal/bytealg,internal/gomodel}.toml` (`[model]` tables, `blank_asm`), `Perennial/TrustedCode/internal/gomodel.lean`
  (`Choose`, `ChooseUint64`, `Stuck`, `StartRead`), `etc/model-tests.sh`, `etc/trusted-delta.py`, goose/README.md
  "Go model overlays", `.agents/skills/review-trusted/SKILL.md` (rule R12 for model Go), docs/PERENNIAL_PROOF_REFERENCE.md.
- etcd-grove units: also its CLAUDE.md, notes/STATUS.md, models/README.md, etc/tcb-report.py.

## Rules (from Upamanyu, via the coordinator; non-negotiable)
- **Translate the real Go wherever goose and the semantics can.** A model only for an irreducible primitive, shown by a
  goose run on the real source (record the goose error or the stuck construct). Prefer: real Go > Go model over
  primitives > hand-written Lean. Each model must be **never more defined than Go** (model ⊇ Go's behaviours; a stuck
  point covers everything). Every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the `MODEL:` doc comment.
- **No new Lean axioms. No new top-level premises** (spec premises of existing results count; a new hypothesis on a
  theorem, a `FieldAssumptions`-like binder, a bound like S1's Join `< 2^61`). If one seems needed, STOP that item and
  report it to the lead at once (concise: what, why, alternatives, recommendation). Spec statements stay exactly as
  they are, except removing premises/binders (strengthening). Never weaken or remove a theorem.
- No reflect semantics: reflection paths stay stuck (`pp.printValue` etc.), or avoid them by rewriting.
- Goose translator changes are as trusted as the Lean semantics: avoid; if you need one, report first.
- Semantics follow the Go spec; gc divergences are documented as known limitations.
- Proof workflow: (1) fix specs (interfaces), (2) design invariants/representation predicates, (3) prove pieces
  independently. A wrong spec goes back to (1), no local patching.

## Setup
- Your worktree and branch are named in your prompt. Perennial: `git -C /home/ubuntu/.claude-E/jobs/b20ef685/tmp/pgmRest
  worktree add <dir> -b <branch> origin/lean` (lean = 54a29571e, S1 included). etcd-grove: the lead gives you a ready
  worktree; never touch /home/ubuntu/etcd-grove's own checkout.
- Scratch: `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/gmr-<unit>/` (plan, logs, packet, resume notes).
- **Disk is tight** (`df -h /`; keep ≥ 8 GB free). Do NOT copy `.lake` into your worktree; build on the VM. No big files.
- Go: `PATH=/home/ubuntu/sdk/go1.26.11/bin:$PATH GOTOOLCHAIN=local`. Never reinstall ~/go/bin/goose. Build goose and
  proofgen from your worktree into your scratch: `cd <wt>/goose && GOPATH=<scratch>/gopath GOMODCACHE=$HOME/go/pkg/mod
  go install ./cmd/goose ./cmd/proofgen`, and regenerate with `etc/update-goose-new.py` (read its `--help`; its
  `--compile` installs into GOPATH, so set GOPATH to your scratch). After a regen, `git diff --stat Perennial/Code` and
  restore unrelated churn (S1 found lean's `Perennial/Code/strconv.lean` is not a go1.26.11 regeneration: restore it from
  origin/lean).
- Builds: `/shared/tmp/vm/vmlake build <Module>...` from your worktree root (README /shared/tmp/vm/README.md). Only 2 VM
  slots for everyone, so build targeted modules, batch several targets per call, and run long builds with
  `run_in_background`. Exit 75 = VM unavailable: build locally through /shared/tmp/lean-sched (read its README; never bare
  lake). Before you report done: every module that imports what you changed builds (for a low package like `sync`
  that is the whole `Perennial` library: build it in chunks of ≤800 modules; one call exceeds ARG_MAX).
- Git: commit only your own files (`git add <paths>`), commit messages end with
  ```
  Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01L1fRpegCx9fRqC2P36ayjN
  ```
  Push your branch: `GH_TOKEN=$(cat ~/.config/gh-token) git -c credential.https://github.com.helper='!gh auth
  git-credential' push origin <branch>` (never print the token). **Land nothing**: no `etc/land.sh push`, no
  `land-queue:`, no PRs (the lead opens the one draft PR), no GitHub comments.

## Phases
**A. Plan (then stop and return).** In `<scratch>/plan.md`, ≤ 40 lines: for every trusted declaration of your packages
(today's `trusted =` names with `.impl`s in TrustedCode, Lean glue, pasted goose output): **real** (translate; say what
makes it translatable now) / **model** (why irreducible: the goose error or stuck construct from an actual goose run on
the real source; the model's shape; its choice/stuck points) / **primitive** (stays Lean; new primitives with their
`.impl` or step rule). Then the specs whose proofs change, any spec premise or theorem binder that can be dropped, the
evidence (Go's own tests under the overlay, `etc/model-tests.sh` lines; difftests), anything that needs a decision.
Return the plan's path and a ≤ 10-line summary. The lead replies "go" (maybe with changes).

**B. Execute.** Models in `goose/model/overlay/<import path>/` (etcd-grove: `models/<import path>/`), `[model]` tables,
regenerate, delete the retired TrustedCode/glue, port the proofs, extend `etc/model-tests.sh` (add your packages; the
lead merges the other units' lines), run it, `go test ./goose/...`, build, then run the repository's review-trusted skill
in fix mode over your branch (`.agents/skills/review-trusted/SKILL.md`). Commit and push.

**C. Report.** Write `<scratch>/packet.md`, S1's format, concise (Upamanyu is a Perennial expert):
- per package: which functions became real translations; each model next to the real Go (`etc/trusted-delta.py` output
  in a `<details>`); the deleted trusted Lean (file, lines);
- new primitives with their `.impl` / step rule;
- premise and statement changes (removals only), with before/after;
- `#print axioms` of every touched top-level result / spec (`propext, Classical.choice, Quot.sound` expected);
- evidence: the Go tests run (and the ones left out, with reasons), builds.
Final message to the lead: branch + head commit, packet path, ≤ 15-line summary, open items.

If your context passes about 70%, stop cleanly: commit/push what builds, write `<scratch>/resume.md` (state, next
steps, commands), and report.

## Update (VM saturated, from the coordinator)
- Batch: fewer, larger vmlake calls with several targets each; don't run one module per call.
- vmlake's default is now -j 40 (cap 64).
- Small single-module checks may run locally through /shared/tmp/lean-sched (`lake env lean <file>`), but only if
  your worktree already has the needed build outputs; do NOT copy or fetch a .lake to get them (local disk floor 8 GB).
- Use the VM for cones too big for that.

## Takeover (2026-11-24, new lead; the previous lead and all helpers were stopped at a usage limit ~05:02Z)
- Your predecessor's state: `python3 /home/ubuntu/.claude-E/jobs/b20ef685/tmp/gmr-transcript.py <predecessor id> inbox`
  (its brief, and every reply/decision the lead sent it: those decisions stand), `... tail 60` (where it stopped),
  `... all` (its own messages). Its scratch dir (`gmr-<unit>/`: plan.md, resume.md, logs) is yours.
- The new lead committed every uncommitted file in your worktree as a `WIP (...)` commit and pushed the branch. Build
  on it; amend nothing that is pushed (add commits).
- Background shells, Monitors and VM builds of the old session are dead: re-run what you need.
- **Commit trailer is now** (replace the old one):
  ```
  Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_013q31eDXUNWQSCaPUSYn9eG
  ```
- **Do not spawn sub-agents** (the lead keeps ≤ 6 helpers running). Do the proof porting yourself.
- Shared hashes: Perennial `goose-model-overlay-rest-xtools` = 78d6ef937 (x/tools v0.51, asm_amd64.h allowlist,
  runtime push-linkname drop, CheckAPI ignoring parameter names); gomodel Choose/ChooseUint64 specs 634fd62a0 and
  CheckAPI 02ff0ea6c (on `goose-model-overlay-rest-time`); etcd-grove infra 9dac1834d6 (tcb-report "Go models",
  etc/model-tests.sh TESTS), netgo b68f8335b8, both on `go-models-rest/2026-11-24`.
- Decisions by Upamanyu (final): (1) timers read `time.Local` at fire time; time's init gives `time.Local ↦□ &localLoc`;
  timer specs take `isPkgInit time` (approved premise). (2) `net.OpError.Error/Timeout/Temporary` become the translated
  real Go, with a spec precondition on `Err` (net's own) and `Source`/`Addr` (nil or `*TCPAddr`). fmt stage 2
  (Errorf/Printf/...) is in S3; printValue/reflection paths stay stuck.
- Disk: 8 GB free at takeover. Keep your scratch small; delete build logs you no longer need.
- Report (your final message) to the new lead: branch + head, packet path, ≤ 15-line summary, open items.

## Update (~08:00Z, from Upamanyu via the coordinator)
- FINISH, don't stop at a review point: decide (per ~/coordinator-notes/RULES.md), record the decision in your packet, and complete the work (proved, built, pushed). Trusted pieces stay on the branch with proofs on top.
- Never idle waiting for a build: check it directly or work on independent files meanwhile.
- /tmp has a per-user quota (shared tmpfs) that ran out tonight: export `TMPDIR=GOTMPDIR=<your scratch dir>/tmp` (mkdir it) for go test/build and every tool; no logs or test dirs in /tmp; delete Go test temp dirs when done.
- Helper cap is 3 for the whole lead: do not spawn sub-agents.
- **Get goal states, not blind builds** (VM queue ~25 deep): run ONE `/shared/tmp/vm/vmlake --fetch build <the cone you edit>`
  early (it brings the .olean outputs back into your worktree's .lake; check `df -h /` first, keep >= 15 GB free), then
  iterate locally with `etc/lean-check.py FILE` (`--goal LINE` for the proof state; server class of the local Lean
  scheduler, no VM queue). Use the VM again only for the final cone build.
- **No permission prompts** (Upamanyu denies them; ~/coordinator-notes/overnight-brief.md "No permission prompts"): never
  `rm -rf` on a variable-built path (use a literal absolute path, one target per command, checked first, in a separate
  command); no force-push, no `git reset --hard` on shared branches, no settings edits, no commands outside your
  worktree/scratch. A denied action: don't retry verbatim; do it another way or leave it and note it in resume.md.
- **Builds: VM first, this machine lightly** (Upamanyu 15:30Z; overnight-brief "Builds: VM first"): every build of more than a
  handful of modules goes to the VM (`vmlake`), never locally while it is reachable. Locally only `etc/lean-check.py` of a file
  or two, one at a time, through the scheduler. If the VM is unreachable, WAIT for it (watch /shared/tmp/vm/host): no local
  `lake build` fallback (this supersedes "use the local scheduler" in your prompt).
