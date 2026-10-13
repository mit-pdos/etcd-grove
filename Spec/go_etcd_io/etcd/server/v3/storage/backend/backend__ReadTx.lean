/-
`ReadTx` (the backend). `b.ReadTx()`: the shared read transaction, `b.readTx`.
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

/-- `b.ReadTx()`: the shared read transaction, `b.readTx`. -/
abbrev backend.backend.ReadTx.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"ReadTx")) (Val #()))
  {{ (rt : Loc), RET #(interface.mkOk (go.GoType.PointerType readTx.ty) #rt);
      bF go!"readTx" b ↦□ rt }}

end spec

end EtcdGrove
end Perennial
