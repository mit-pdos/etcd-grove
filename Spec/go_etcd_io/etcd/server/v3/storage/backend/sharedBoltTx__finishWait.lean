/-
`sharedBoltTx.finishWait` (the backend, `read_tx.go`; added by etcd#22215). `st.finishWait()`: `st.txWg.Done()`, a reader leaving the interval: its share given back, for its budget token.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

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

/-- `st.finishWait()`: `st.txWg.Done()`, a reader leaving the interval: its share given back, for its budget token. -/
abbrev backend.sharedBoltTx.finishWait.spec : Prop :=
  ∀ (γ : BNames) (st : Loc) (dq : DFrac) (rtx wg : Loc) (γw γo γt : GName) (k : Nat) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rwgOf st ↦{dq} wg ∗ □ wgInv γ rtx wg γw γo γt ∗ rdShare rtx γo k q }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"finishWait")) (Val #()))
  {{ RET #(); rwgOf st ↦{dq} wg ∗ ownToks γ.rdt 1 }}

end spec

end EtcdGrove
end Perennial
