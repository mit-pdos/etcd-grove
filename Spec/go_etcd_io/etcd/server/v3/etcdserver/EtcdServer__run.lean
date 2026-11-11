/-
`(*EtcdServer).run()` (`server.go`), translated with its body: the apply loop over the raft
wrapper's `applyc`, with the FIFO scheduler, the ready handler and the shutdown. Lean-first (the
request path's unit 4c, 2026-10-13); see `InvRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.run()`**, the server's apply loop (a goroutine body: `start`'s `go s.run()`), in both auth
modes (the auth component's stage 2, 2026-11-04): with what `isServerRunC` lists in the component
`C`, the environment's (and the receipts' bound, R6, 2026-11-07: in both modes, `applyAll`'s since
strict M1, the log's smallness coming from the writer's receipt; until then `acReceiptOk`, with
auth on only), it starts the raft
wrapper's loop, then receives each batch of committed entries raft hands it (`applyc`) and
schedules its `applyAll` on a FIFO scheduler, the apply thread's resources flowing from job to job.
The write budget is the receipt-backed `srvWTPool E` (D19b), from which `apply` takes one token per
entry. Its exit `errorc` is never taken in the runs covered (D19m: nothing is sent on it,
`srvRunFieldsAt`'s bag with predicate `False`). On `stop` it receives stop requests (`srvStopReq`,
what `HardStop` sends: the evidence that the bootstrap log was applied, `srvBootApplied`; the stop's
scope, `srvStop.scope`; the data directory `dd`, `srvDataDir`; the store's readers of the serving
stocks); on one it returns and its deferred shutdown runs: `close(stopping)`, `cancel()`,
`sched.Stop()` (the pending `applyAll` jobs run, the last one's post `applyRes` at the log handed to
the apply thread), `s.wg.Wait()`, `s.r.stop()` (`raftNode.stop.spec`, with the stop's slot that
`isServerRunC` carries, `srvStop.slot`), `Cleanup()` (the backend closed), and `close(done)`, which
announces the image of member `γn.id`'s data directory `dd` at the request names `ρ`, escrowed for
the stop right's claim `c` (`srvDoneInv`).

One spec (R2c-4, the R2b-2 review's F4; until then `spec`, whose callers never stopped the server,
with `done` announcing `True` and no request ever sent, and the draft `specStop`, with the shutdown's
resources and the scope as premises). The `errorc` path stays closed.

**Scope** (R2d'a swap batch 5, 2026-11-07: one spec for a first start and a restart, through
`isServerRunC`'s `srvRunRestartR`, which a first start gives, `srvRunRestartR_first`): `σ.b = 0`
only, a restart before the WAL's first snapshot (`ai₀ = 0`, `γn.pre = []`): the backend's ghost log
`A₀ = γn.a0` is replayed through the window `(0, |A₀|]` (a first start is `A₀ = []`). `σ.b > 0` is
R2d'b's.

**The restart-only premises** (`notes/restart-plan.md`, "R2d'a restart-only premises"; each
proved or vacuous at a first start; R2s removes 1; S1, 2026-11-11: rows 2-3 replaced by two facts):
* `srvWinPend` (`isServerRunC`'s `Hwpend`, A7): no merged snapshot sent at a new raft term while the
  replay window is pending. **False whenever the restarted member is later elected and snapshots a
  follower** (its `n` is free and its token never consumed; corrected 2026-11-07); R2d'b restates
  it, R2s removes it (by following the merged snapshot in the ghost).
* (S1; until then `rnWinInstallAbove`, row 2, a premise) a snapshot a `Ready` installs inside the
  window is above the backend's log: **derived** (`rnRestartOk_winAbove`), from raft's (a snapshot
  is above the hard state's commit, `readyRest_snap`), the loop's fact below and the names' fact.
* (S1; until then `rnWalCommitAbove`, row 3, which was false at the start of most restarts) the
  names' fact `snap0 ≤ |a0| ≤ commit0` (`rnRestartOk`'s restart disjunct): the backend's log between
  the restored records' snapshot index and commit, true of every graceful stop's image
  (`raftNode.stop.spec`'s post gives `|a0| ≤ σ.commit`); graceful-only (after a power loss the
  backend can be ahead of the WAL's synced commit).
* (S1) the loop's fact `commit0 ≤ p.Commit'` (`rnLoopTokP`, in `isServerRunC`'s loop token): raft's
  commit never below the restored one, proved through the loop (`readyRest_commit_mono`), and `0 ≤ _`
  at a first start; at a restart R2d'b's `RestartNode` gives it (the driver starts at the restored
  hard state, whose commit is `commit0`). Crash-proof.
* `rnSnapTermAbove` (`rnRestartOk`'s): every `MsgSnap` a `Ready` carries has a term above the
  incarnation's start term.
* `ai₀ + |A₀| + 1 < 2^64` (`srvRunRestartR`'s): room past the replayed log.
* every entry of `A₀` has `typ` 0 or 1 (`EntryNormal`/`EntryConfChange`, no `EntryConfChangeV2`;
  `srvRunRestartR`'s): etcd proposes only v1 `ConfChange`s (`configure`'s `ProposeConfChange`).
* `srvRLogLb γ.srv γ.a0` (`rnRestartOk`'s restart disjunct): the backend's log `A₀` is
  cluster-committed.

What it rests on (S1: the 2026-11-07 vacuity sentence, `pbEnc_ok` and the grpc message models,
dropped as stale): the stop branch rests on the three axioms of the image's configuration
(`apply.memberKey_inj`, `apply.memberEnc_id_learner`, `membership.membersOf_decode`, through
`stop_imageConf`), so every result over `run` does, including those whose callers never stop the server (approved by the user,
2026-11-06). (revoke-open, 2026-11-06, Q8 (a)) `run` holds a thread token, which it returns
(`start` forks it with `wp_fork_tok_body`): its expiry arm starts goroutines whose reader slots are
backed by it (`isServerRunC`'s `#Hrvk`). -/
abbrev EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (dd : GoString) (c : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq s E ρ dd)
        (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
