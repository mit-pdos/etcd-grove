/-
`backend.run` (`backend.go`). `b.run()`, the periodic committer goroutine: until `stopc` closes, every `batchInterval` a commit if something is pending (unpaid: its half of `γ.used`, at most one such commit after each write-back); at the stop, `CommitAndStop` with the clients' half of the open token (from the stop invariant, for its `runTok`) and its quarter; then `donec` closed. Stated at `HasLC.hasLC` (the timer and the broadcast channels are).
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `b.run()`, the periodic committer goroutine: until `stopc` closes, every `batchInterval` a commit if something is pending (unpaid: its half of `γ.used`, at most one such commit after each write-back); at the stop, `CommitAndStop` with the clients' half of the open token (from the stop invariant, for its `runTok`) and its quarter; then `donec` closed. Stated at `HasLC.hasLC` (the timer and the broadcast channels are). -/
abbrev backend.backend.run.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (sc dc : GoChan) (γsc γdc : ChanNames)
    (u : Nat) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗
      isStopChansAt γ b sc dc γsc γdc ∗ bF go!"batchInterval" b ↦□ d ∗
      ownBroadcastChan dc γdc iprop(True) .Pending ∗ runTok γ ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ ghostVar γ.used (1 : Qp).half u }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
