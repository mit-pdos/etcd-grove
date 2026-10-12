/-
`ConcurrentReadTx` (the backend). `b.ConcurrentReadTx()`: a read transaction over the readers' view now (its committed data
and a copy of the read buffer, the cache's when current), with the reader's token's `txMu` slot
and budget token, which its `RUnlock` gives back.
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

/-- `b.ConcurrentReadTx()`: a read transaction over the readers' view now (its committed data
and a copy of the read buffer, the cache's when current), with the reader's token's `txMu` slot
and budget token, which its `RUnlock` gives back. -/
abbrev backend.backend.ConcurrentReadTx.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (q qo : Qp) (vd : VData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ rdTok γ P b ∗ bView γ q vd ∗ bOpen γ qo }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"ConcurrentReadTx")) (Val #()))
  {{ (crt rtx : Loc) (rv : RView), RET #(interface.mk (go.GoType.PointerType concurrentReadTx.ty) #crt);
      crtSnap γ P b crt rtx rv ∗ ⌜vData P rv = vd⌝ ∗ (crTok γ b -∗ rdTok γ P b) ∗ bView γ q vd ∗
      bOpen γ qo }}

end spec

end EtcdGrove
end Perennial
