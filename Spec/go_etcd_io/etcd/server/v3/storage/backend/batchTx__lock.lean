/-
`batchTx.lock` (`batch_tx.go`). `t.lock()`: the batch lock, free state and the client's resources `W ∗ Pk` (the backend open: a share of the open token at `false`).
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.lock()`: the batch lock, free state and the client's resources `W ∗ Pk` (the backend open: a share of the open token at `false`). -/
abbrev backend.batchTx.lock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (qo : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ dghostVar γ.opn (DFrac.own qo) false }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"lock")) (Val #()))
  {{ RET #(); ∃ st : BSess, batchLocked γ P b st ∗ ⌜freeOk P st ∧ st.cnt.p0 = sint.nat st.pend⌝ ∗ (W ∗ Pk) ∗
      dghostVar γ.opn (DFrac.own qo) false }}

end spec

end EtcdGrove
end Perennial
