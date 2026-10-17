/-
`sharedBoltTx.addWait` (the backend, `read_tx.go`; added by etcd#22215). `st.addWait()`: `st.txWg.Add(1)`, a reader joining the interval of the `WaitGroup` `wg` (open at `q`): its share of the bbolt transaction `rtx`, for a budget token.
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

/-- `st.addWait()`: `st.txWg.Add(1)`, a reader joining the interval of the `WaitGroup` `wg` (open at `q`): its share of the bbolt transaction `rtx`, for a budget token. -/
abbrev backend.sharedBoltTx.addWait.spec : Prop :=
  ∀ (γ : BNames) (st : Loc) (dq : DFrac) (rtx wg : Loc) (γw γo γt : GName) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rwgOf st ↦{dq} wg ∗ □ wgInv γ rtx wg γw γo γt ∗ wgOpen γw q ∗ ownToks γ.rdt 1 }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"addWait")) (Val #()))
  {{ RET #(); ∃ (k : Nat) (q' : Qp), rwgOf st ↦{dq} wg ∗ wgOpen γw q ∗ rdShare rtx γo k q' }}

end spec

end EtcdGrove
end Perennial
