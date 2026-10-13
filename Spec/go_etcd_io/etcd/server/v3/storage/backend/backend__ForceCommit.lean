/-
`ForceCommit` (the backend). `b.ForceCommit()`: the batch transaction committed (the readers' view unchanged).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
(2026-10-12: a write-back's budget token pays for the commit: a commit leaves the hook's
puts in the write buffer, and the token budget bounds how many accumulate before a write-back.)
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

/-- `b.ForceCommit()`: the batch transaction committed (the readers' view unchanged). -/
abbrev backend.backend.ForceCommit.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (qo : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bOpen γ qo ∗ wbTok γ }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"ForceCommit")) (Val #()))
  {{ RET #(); bOpen γ qo }}

end spec

end EtcdGrove
end Perennial
