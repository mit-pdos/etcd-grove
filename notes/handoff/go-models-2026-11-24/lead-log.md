# go-models-rest lead: resume (refreshed 2026-11-24 by the account-F lead; supersedes the copy in ~/.claude-E/jobs/b20ef685/tmp/)

Role: lead of Go-model overlays S2–S7 (perennial#692), one combined review packet for Upamanyu; nothing trusted lands.
Old live notes (decisions log, still valid): /home/ubuntu/.claude-E/jobs/b20ef685/tmp/go-models-rest-resume.md (read its
"Decisions log"). Common helper brief: tmp/gmr-brief.md (+ "Takeover" section). Transcript reader for any old agent:
`python3 tmp/gmr-transcript.py <agent id> inbox|tail N|all`. (tmp = /home/ubuntu/.claude-E/jobs/b20ef685/tmp)

## Takeover actions (done)
- Committed all uncommitted helper work as WIP commits and pushed every unit branch:
  sync 68f0cdc43, rt 99facc7e7, split cedcc0138, time 9671c6119, fmt 54f7d2051 (was clean),
  eg-gmr fd7d0f18b6 (egrest) + e251433367 (egos; also holds egrest's Proof/internal/gomodel, gen-init.py, PkgTables).
  egnet: eg-gmr-net, branch go-models-rest-egnet/2026-11-24, 6bddc60db8 (WIP, pushed; no proofs ported).
- Trimmed ~/.cache/go-build (disk 6.9 → 8.1 GB).

## Units (account-F agent ids)
| unit | worktree / branch | state |
|---|---|---|
| sync | pgmR-sync / goose-model-overlay-rest-sync | DONE 66369f153 (Cond ticket notifyList; deadlock-detector KNOWN_LIMITATIONS; full Perennial builds; axioms std), packet tmp/gmr-sync/packet.md. At eg bump: port 7 eg files, DELETE backend/MutexLit.lean (axiom wp_mutexLit) + Proof/sync/MutexLitSemantics.lean |
| fmt | pgmR-fmt / goose-model-overlay-rest-fmt | respawned a6171356f2d72d645 |
| time | pgmR-time / goose-model-overlay-rest-time | DONE 8a70dee2a (docs + KNOWN_LIMITATIONS after review, lead), packet tmp/gmr-time/packet.md updated; Code/time.lean comment-only diff since 022db9a06, rebuilt at integration |
| rt | pgmR-rt / goose-model-overlay-rest-rt | DONE 41576f1cf (incl. lead's lean merge; runtime/os/log/syscall/gomodel cone builds, VM exit 0) (helper d5b625198 + lead's syscall.toml note), packet tmp/gmr-rt/packet.md; ChooseString isolated on goose-model-overlay-rest-gomodel-choosestring 1ba3cdff2 (sent to fmt); D3 crypto/rand.Int DEFERRED (branch -rt-rand c6d26e15a, not building); full-library rerun owed at integration; adv review pending |
| split | pgmR-split / goose-model-overlay-rest-split | DONE 8a6feff49 (importer build: rc 0 but truncated log; integration build is the check), packet tmp/gmr-split/packet.md (fix subject of 8a86dc88f 'strings.Split real' in PR text; review goose commits 867d5adb3, fb61fea3d) |
| egrest | eg-gmr / go-models-rest/2026-11-24 | DONE 14aa39bd7f, packet tmp/gmr-egrest/packet.md; cone build + tcb-report wait on egos; at pin bump drop local Proof/internal/gomodel + PERENNIAL_HERE entry |
| egos | eg-gmr (shared) | 4th helper ae6b3400ea01a31f2 stopped (58%), head cba985d9f0, nothing compiled; resume tmp/gmr-egos/resume.md (targets10.txt; open items 1-6); port less finished than thought. RESPAWN egos-5 queued after egnet-2 |
| egnet | eg-gmr-net / go-models-rest-egnet/2026-11-24 | helper ad1fd20be0117bf6c stopped (70%), head a3218fa167, resume tmp/gmr-egnet/resume.md (Session 3, "Learned from build6"): only Base builds; Errors pilot, ~30 net proofs, OpError proofs, Init, ~60 Read/Write clients, KvNet copy, builds, packet remain. RESPAWN egnet-2 queued |
Shared: xtools branch goose-model-overlay-rest-xtools 78d6ef937; integration clone tmp/pgmRest (branch goose-model-overlay-rest = lean 54a29571e, holds .lake).

## Next (lead)
1. As wave-1 units finish, spawn egos then egnet (respawn prompts: same shape as wave 1, see gmr-brief Takeover).
2. Per finished package: fresh adversarial reviewer (tmp/gmr-adv-brief.md) on model vs real Go.
3. Merge unit branches + xtools into goose-model-overlay-rest; regen; full vmlake build; model-tests; #print axioms; Perennial etc/trusted-delta.py.
4. etcd-grove: pin to that Perennial head on go-models-rest/2026-11-24; merge egnet branch; port the ~5 eg proofs (sync); tcb-report before/after.
5. One Perennial draft PR + one etcd-grove draft PR; packet = PR body; report to coordinator.
Mechanism follow-ups for the packet: GOMODCACHE overlay refusal (primitive.Mutex/Assume, J3); copyChecker reachability rule (a'); init-order caveat (crc32) as a review-trusted checklist line; Split option (a).

## Former pending decision (now decided overnight, see below)
- net `Conn.Read` (real Go compares err with io.EOF): needs `isPkgInit io` (or pure fact: io.EOF holds *errors.errorString) on Conn.Read.spec/specLc, plus internal/poll package fact strengthened to `*poll.DeadlineExceededError` (defs, no premise). ~20 clients of Conn.Read. Recommended: option 1. egnet continues the rest; Read proof in a separate "PENDING SIGN-OFF" commit. egnet branch head 47389d21ab; 7979b955cc forwarded to egos.
- Same decision extended to `Conn.Write` (real Go wraps only if err != nil; needs ed non-nil): `isPkgInit internal.poll` (or pure fact ed is *DeadlineExceededError); Read then takes `isPkgInit io ∗ isPkgInit internal.poll`. egnet wrote Proof/internal/poll/PkgInit.lean errDeadlineExceeded_of_pkgInit. Both in the PENDING SIGN-OFF commit.

## Decided overnight (2026-11-24, per overnight-brief.md; redo in the morning if wrong)
- net Conn.Read/Conn.Write premises: DECIDED option 1. Read/specLc take `isPkgInit io ∗ isPkgInit internal.poll`, Write takes
  `isPkgInit internal.poll`; poll's package fact strengthened (ErrDeadlineExceeded is *DeadlineExceededError, proved from the
  translated initializer). Why: RULES 3 (verify the real Go over keeping a Lean model) and 36 (per-function contracts as spec
  preconditions); no axiom; clients discharge isPkgInit from program init, so top-level statements are expected unchanged
  (to be checked with tcb-report --check; if a top-level premise would change, STOP and escalate per rule 7/17).
  Alternatives: pure premises on the error values (same trust, less reusable); keep Lean models of conn.Read/Write (more trust).
  The PENDING SIGN-OFF commit stays separate, so it can be dropped.

## Adversarial reviews (tmp/gmr-adv-brief.md; one at a time within the 6 cap)
- sync: a97bf181026ddc338 running. time: launched after time DONE. Queue: split (8a6feff49), egrest (14aa39bd7f), then rt/time/fmt/egos/egnet as they finish.
- sync adv review DONE (a97bf181026ddc338; tmp/gmr-adv-sync/). Finding 1 UNSOUND: notifyListWait no-op => Cond.Wait returns where Go blocks/deadlock-throws (plan §5's "early return is a Go schedule" is false). DECIDED overnight: faithful ticket notifyList (Add takes ticket from l.wait, Wait spins until l.notify passes it, Notify* advance l.notify); why: model ⊇ Go, pre-approved model change (RULES 16), no axiom; alt: stuck Wait (loses all Cond proofs). Deadlock detector (spin vs Go's "all goroutines asleep" throw; Mutex/Semacquire/primitive lock): framework-level gap, not a regression -> KNOWN_LIMITATIONS + Robust docs + packet, fix MODEL comments. Finding 3: primitive diff also deletes dead .impls (trylock, Assert, Exit, Sleep, TimeNow, AfterFunc, ResolveProph, Linearize, Millisecond, Second): say so in commit/packet. Finding 2 (nil Pool gc panic value): gc-only, note.
- time adv review DONE (a378315226b8d9c72; tmp/gmr-adv-time/). Nothing reachable today. Latent: makeTimerChan fixes cap at make, Go re-reads GODEBUG asynctimerchan on cap/len (witness capflip/). DECIDED overnight: runtime setenv hook (and Setenv/Unsetenv/Clearenv paths) stuck on key "GODEBUG" (rt in Perennial syscall, egos in eg syscall/os); time: MODEL comment + KNOWN_LIMITATIONS; runtimeTimerAlloc docstring (structFieldRef "timer" fresh address). Why: closes the gap at its source without an environment assumption; alt: assumption "GODEBUG constant" (needs Upamanyu). Time helper reopened for the docs.

## Helper cap: at most 3 concurrent (coordinator, 2026-11-24 night: etcd_safe needs agents)
- time told to stop (lead does its 2 doc fixes: makeTimerChan MODEL comment + KNOWN_LIMITATIONS + capflip witness; runtimeTimerAlloc docstring).
- rt told to wrap up after its axioms check (lead does the GODEBUG setenv-stuck item in Perennial syscall).
- sync ends after the Cond fix. Kept: fmt, egnet, egos. No new spawns until under 3; the split/egrest adversarial reviews are done by the lead itself (or queued after).
- rt decisions (overnight): callers = trusted 1-line .impl over translated callersModel (gc testing needs frames); D3 rand.Int deferred out of the packet (FIPS self-test + ~1.5k lines); GODEBUG: no new trusted hooks, Setenv/Unsetenv/Clearenv stay untranslated (stuck), rule in syscall.toml.

## Integration (lead)
- tmp/pgmRest, branch goose-model-overlay-rest (pushed): = lean 54a29571e + xtools + split + time + rt merged (6bafd0306). Conflicts resolved: gomodel Link.lean (union; gen-link --check ok), etc/model-tests.sh (time in ov, runtime/syscall/log in ovc).
- origin/lean moved 9 commits (callers 2^40 bound 523c4f740.., buildVersion opaque value 8e616d271.., KNOWN_LIMITATIONS angelic exit). Merge conflicts in runtime (Proof/runtime/Base, callers_, Spec/runtime/Version, TrustedCode/runtime; ~430 lines). ABORTED; queued unit "rt-lean".
  DECIDED: lean's designs win (approved by Upamanyu): buildVersion stays the trusted opaque `buildVersionValue` (eg's UTF-8 premise names it), rt's buildVersion Go model dropped; callersModel gets lean's 2^40 frame bound. rt-lean helper: merge origin/lean into goose-model-overlay-rest-rt, resolve so, rebuild runtime cone, push; then lead re-merges.
- Still to merge: sync (after Cond fix), fmt.
- egos decisions (overnight): ownFile gets `nonblock ↦□ false` (real File.fd() reads it; predicate change, no premise; 52 destructuring sites). x/sys/unix stays Lean (3 reasons in packet). Model's unlocked offset update in concurrent Write = extra outcomes, sound, documented.
- Not ours, blocks a full eg build: raft stepFollower heartbeat timeouts (build7/8) -> check against origin/lean at integration (maybe needs maxHeartbeats or is a lean regression); Net/Proof/net/Base (egnet WIP).
- Slot queue (cap 3): 1 egos-4, 2 adv reviews split/egrest/rt. rt-lean: LEAD does it (08:00Z update: no idling).
- 07:2x stall check: egnet build4 failed 06:44 (Net.Proof.net.Base), nudged. COLLISION: another session's UDP work (tmp/udp in job 03d8018a) edits Net/ManualProof/net.lean + Net/Proof/net/Udp*; egnet removes ManualProof/net.lean and net.FieldAssumptions -> reported to coordinator.
- Lead did rt-lean: pgmR-rt fd4d78e31 (merge origin/lean; buildVersion trusted again = lean's buildVersion.init, overlay extern.go deleted; callersModel 2^40 bound; callers_ proof merged). VM build of runtime/os/log/syscall/gomodel cone running (log tmp/gmr-rt/lead-build1.log); push after it passes, then re-merge rt into goose-model-overlay-rest and merge origin/lean there.
- Combined packet draft: tmp/gmr-packet.md (summary table, overnight decisions, reviews, follow-ups; PENDING markers).
- egos-4 spawn refused (account 20-agent cap) ~09:xx; prompt ready (resume items 1-5 + ownFile decision + stepFollower check). Retry on next completion; then egnet-2.
- egos-4 running: ae6b3400ea01a31f2. egnet-2 queued (next free slot).
- Integration pgmRest 11a2209e2 (pushed) = xtools+split+time+rt(41576f1cf)+origin/lean (incl. fmt stage 1.5, errors.As model, strings.Join premise discharge). fmt unit told to merge origin/lean first. Regen check (std-lib + models, goose from integration) running: log tmp/gmr-lead/regen.log.
- Regen check of integration 11a2209e2: consistent (only the known non-go1.26.11 strconv.lean differs; restored).
- fmt merged origin/lean (stage 1.5) cleanly (Results.lean union, Link regen); stage 1.5 touches no model decl; D1 models stay (specs still admit argsOk); building.
- Integration 11a2209e2 cone build (strings bytealg time runtime os syscall log gomodel context errors bytes): VM exit 0.
- Local build route: lean-sched big slots free; helpers to use vmlake --fetch once then etc/lean-check.py locally (brief updated).
- egnet-2 running: aa5049cd1efc93305. Lead queued VM build of egos targets10 + fetch into eg-gmr (log tmp/gmr-lead/egos-build10.log) so egos-5 gets errors + local .oleans for lean-check.
- Integration 9bd58c78a (pushed) = + sync. Full Perennial+PerennialMeta VM build (log gmr-lead/int-build2.log) and model-tests (gmr-lead/model-tests.log) running. egos-5 spawn refused by account cap again; retry on next completion (prompt ready: egos-4's + 'wait for egos-build10 fetch').
- VM sync dir c61dd42e08d7d686 (eg-gmr) had a corrupt perennial clone (no HEAD): renamed to perennial.broken-<ts> on the VM; egos prefetch re-queued (gmr-lead/egos-build11.log).
- Integration 9bd58c78a (lean+xtools+split+time+rt+sync): FULL Perennial+PerennialMeta VM build exit 0. model-tests: sync TestIssue40999 hangs under the overlay (sync-only too; GC-cleanup leak test) -> skipped with reason (uncommitted until rerun passes).

## After the account-limit stop (~09:55Z -> 15:10Z)
- Committed leftovers: egnet 812a7acc3a (OpError proofs WIP), pgmRest 6f1b3587b; fmt's stray FmtAxioms.lean moved to gmr-fmt/.
- ROOT CAUSE of the gc test hangs (sync TestIssue40999/TestOnceXGC, runtime/debug TestReadGCStats, likely time TestAfterFuncStarvation): rt's overlay model of runtime.Gosched (empty body) replaced it for the runtime's own callers too; runtime.GC loops on Gosched. DECIDED: Gosched trusted again (lean's Gosched.impl), rt 44504e9e1; the interim skips reverted (pgmRest b172100e8). Packet: general lesson for review-trusted: never replace a runtime function the runtime itself calls with a gc body that differs.
- Integration db5eeb2a5 (pushed) = + rt Gosched fix + origin/lean (6 more). Full build (gmr-lead/int-build3.log) + model-tests (model-tests5.log) running.
- Helpers: fmt a6171356f2d72d645 and egnet-2 aa5049cd1efc93305 resumed by message; egos-5 spawn refused (20-agent cap) -> retry; prompt ready (prefetched .lake 3.3G + build11 68-error worklist).
- fmt DONE 2cc4ef285 (packet gmr-fmt/packet.md; decision D-S3a: kindIs stays a stub = lean's, translation would need "interface values are never panic values" semantics fact -> follow-up; poll isInit keeps ErrNotPollable). Merged: integration 6c808ce7e (pushed) = ALL Perennial units + lean. Full build of it pending: VM unreachable (exit 75) since ~15:11Z; local big slots busy; pgmRest has no local build outputs.
- Follow-up note: fmt overlay has its own chooseString; swap for gomodel.ChooseString (rt) later.
- No-permission-prompts rules added to gmr-brief.md; told egnet. egos-5 spawn refused again (cap); retry on next completion.
- model-tests on integration db5eeb2a5: ALL PASS with the GC/fairness skips removed (confirms the Gosched root cause).
- egnet-2 stopped at 763a42430b (Errors.lean + 24 wrapper proofs over real Go, lean-check only; 1 sorry in OpError.Temporary Errno branch; gen-init Net syscall Init double-import bug). Spawned egos-5 a65174b2ae426e90a (also owns the gen-init bug) and egnet-3 acc297c953b0f9423.
- 15:30Z rule: builds VM-first (brief + egos-5/egnet-3 told). VM back at new IP. Full integration build of 6c808ce7e (all Perennial units) on VM: log gmr-lead/int-build4.log.
- fmt adversarial review running: a922b6c166192af9c (gmr-adv-fmt/). Remaining reviews queue: rt, split, egrest (then egos, egnet when done).
- egnet-3 7d5bebaf64: OpError.Temporary sorry gone (local go.NotInterface uintptr instance: Perennial gap -> follow-up), wp_OpError_Error over real Go with weaker opErrMsgOk. DECIDED (untrusted): Option A, resErr (some k) gains errStr e ∗ addrOrNil src ∗ addrOrNil addr (posts stronger; 17 wrappers prove it); http.ReadResponse.spec post strengthened to errStr err for DialHTTPPath. egnet-3 resumed.
- egnet-3 stopped at 60% before starting the decision (head 7d5bebaf64); egnet-4 spawned a355905e0d9fd4f76 (Option A, ReadResponse post, gen-init merge, clients, KvNet, builds, packet).
- fmt adv review DONE (a922b6c166192af9c; gmr-adv-fmt/demo): UNSOUND buffer aliasing (errorf skips the pool; model printer writes at the end vs Go directive by directive). DECIDED: reviewer's fix (errorf keeps newPrinter/free; model printer writes prefix + arbitrary chunks into p.buf before each user-method call; errorf reads string(p.buf); doc fixes incl. "invalid return from write" as environment assumption). Rest no divergence (15-case differential call log matched). fmt-fix helper spawned.
