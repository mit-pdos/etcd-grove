/-
`RUnlock` (the backend). `crt.RUnlock()`: its share of the interval given back (`txWg.Done()`), and its tokens.
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

/-- `crt.RUnlock()`: its share of the interval given back (`txWg.Done()`), and its tokens. -/
abbrev backend.concurrentReadTx.RUnlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (crt rtx : Loc) (rv : RView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ crtSnap γ P b crt rtx rv }}
    (App (Val (crt @!! go.GoType.PointerType concurrentReadTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); crTok γ b }}

end spec

end EtcdGrove
end Perennial
