/-
`sharedBoltTx.setTx` (the backend, `read_tx.go`; added by etcd#22215). `st.setTx(tx)`: the bbolt transaction field set.
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

/-- `st.setTx(tx)`: the bbolt transaction field set. -/
abbrev backend.sharedBoltTx.setTx.spec : Prop :=
  ∀ (st tx0 tx : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rtxOf st ↦ tx0 }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"setTx")) (Val #tx))
  {{ RET #(); rtxOf st ↦ tx }}

end spec

end EtcdGrove
end Perennial
