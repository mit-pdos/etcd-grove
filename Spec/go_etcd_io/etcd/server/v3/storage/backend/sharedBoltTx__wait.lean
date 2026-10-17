/-
`sharedBoltTx.wait` (the backend, `read_tx.go`; added by etcd#22215). `st.wait()` (unused): `st.txWg.Wait()` of an ended interval: once its readers are done, the whole bbolt read transaction.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadSide

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

/-- `st.wait()` (unused): `st.txWg.Wait()` of an ended interval: once its readers are done, the whole bbolt read transaction. -/
abbrev backend.sharedBoltTx.wait.spec : Prop :=
  ∀ (γ : BNames) (st : Loc) (dq : DFrac) (rtx wg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rwgOf st ↦{dq} wg ∗ rollbackRes γ rtx wg }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"wait")) (Val #()))
  {{ RET #(); ∃ D : Data, rwgOf st ↦{dq} wg ∗ txLive rtx 1 ∗ rtxSnap rtx D }}

end spec

end EtcdGrove
end Perennial
