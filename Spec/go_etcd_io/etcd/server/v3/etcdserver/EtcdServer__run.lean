/-
`(*EtcdServer).run()` (`server.go`), translated with its body: the apply loop over the raft
wrapper's `applyc`, with the FIFO scheduler, the ready handler and the shutdown. Lean-first (the
request path's unit 4c, 2026-10-13); see `InvRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.run()`**, the server's apply loop (a goroutine body: `start`'s `go s.run()`), with what
`isServerRun` lists: it starts the raft wrapper's loop (with the ready handler, whose
`updateCommittedIndex` raises the committed index's ghost lower bounds), then receives each batch
of committed entries raft hands it (`applyc`) and schedules its `applyAll` on a FIFO scheduler,
the apply thread's resources flowing from job to job (`applyRes`); it returns on `errorc` or
`stop`, after its shutdown (closing `stopping`, cancelling the server's context, stopping the
scheduler, waiting for `GoAttach`'s goroutines, stopping raft, `Cleanup`, closing `done`). The write
budget is the store's write tokens (`txn.storeWTs E.γ N`, the backend's unit 6: one token per
applied entry), each batch's share going with its job to `applyAll`; `N ≥ 2 ^ 64` covers every
index (the indices `srvC` allows are below `2 ^ 64`), so the budget never runs out. -/
abbrev EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat),
  2 ^ 64 ≤ N →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerRun s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ N }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
