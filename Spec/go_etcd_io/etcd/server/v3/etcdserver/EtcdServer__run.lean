/-
`(*EtcdServer).run()` (`server.go`), translated with its body: the apply loop over the raft
wrapper's `applyc`, with the FIFO scheduler, the ready handler and the shutdown. Lean-first (the
request path's unit 4c, 2026-10-13); see `InvRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

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

/-- **`s.run()`**, the server's apply loop (a goroutine body: `start`'s `go s.run()`), with what
`isServerRun` lists: it starts the raft wrapper's loop (with the ready handler, whose
`updateCommittedIndex` raises the committed index's ghost lower bounds), then receives each batch
of committed entries raft hands it (`applyc`) and schedules its `applyAll` on a FIFO scheduler,
the apply thread's resources flowing from job to job (`applyRes`). Its two exits, `errorc` and
`stop` (after which it would shut down: close `stopping`, cancel the server's context, stop the
scheduler, wait for `GoAttach`'s goroutines, stop raft, `Cleanup`, close `done`), are never taken
in the runs covered (D19m, 2026-10-18): nothing is sent on either (`srvRunFieldsAt`: bags with
predicate `False`), so it never returns; until then the shutdown was proved, with `Cleanup` a false
trust-boundary axiom (it closes the backend and the stores that request goroutines still use). The write
budget is the store's write tokens (the backend's unit 6: one token per applied entry), since D19b
(2026-10-18) in the receipt-backed budget `srvWTPool E` (`isServerRun`), from which `apply` takes
one per entry. Until D19b `run` held `txn.storeWTs E.γ N` and handed each batch's share to its
job, under the lifetime premise `srvLifeBound ρ.raft N` (D14g: every committed log has at most `N`
entries; until 2026-10-17, `2 ^ 64 ≤ N`). -/
abbrev EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerRun s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}


/-- **`spec` in the auth mode `on`** (the auth plan's E3q, 2026-10-27): `run` from `isServerRunOn`
(the apply thread's mode-`on` rows; the environment's mode `on γa`), its jobs `applyAll.specOn`'s
(the receipts' bound theirs). -/
abbrev EtcdServer.run.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (γa : auth.AuthNames),
  E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerRunOn s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

/-- (DRAFT, R2b-2, 2026-11-02; `notes/restart-plan.md`, "R2b: the stop") **`run` of a server that
may be stopped**: `spec`'s, with stop requests on `stop` (its bag's predicate `True`: `HardStop`
sends one) and `done`'s close announcing the image of member `id`'s data directory `dd` at the
request names `ρ`, escrowed for the stop right's claim `c` (`srvDoneInv`), `id` the raft node's;
with what the shutdown
needs besides (`srvShutdownPre`). On a stop request `run` returns and its deferred shutdown runs:
`close(stopping)`, `cancel()`, `sched.Stop()` (the pending `applyAll` jobs run, the last one's post
`applyRes` at the log handed to the apply thread), `s.wg.Wait()`, `s.r.stop()`
(`raftNode.stop.specStop`), `Cleanup()` (the backend closed), and `close(done)` with the image in the
escrow (R2b-3: assembled from those posts). -/
abbrev EtcdServer.run.specStop : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (id : w64) (dd : GoString) (c : GName),
  γn.id = id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerRun s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ iprop(True)
        (srvDoneInv ρ.rd.raft.raft ρ id dd c) ∗
      srvShutdownPre s γn dd }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
