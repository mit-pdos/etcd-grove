/-
`OnPreCommitUnsafe` (the backend). `h.OnPreCommitUnsafe(tx)`: its function on `tx`.
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

/-- `h.OnPreCommitUnsafe(tx)`: its function on `tx`. -/
abbrev backend.hooks.OnPreCommitUnsafe.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (h : hooks) (st : BSess),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ hookFnSpec γ P Pk b t h.onPreCommitUnsafe' ∗ batchLocked γ P b st ∗ Pk ∗ ⌜hookPre P st⌝ }}
    (App (Val (h @!! hooks.ty @!! go!"OnPreCommitUnsafe"))
      (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
  {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ ⌜hookStep P st st'⌝ }}

end spec

end EtcdGrove
end Perennial
