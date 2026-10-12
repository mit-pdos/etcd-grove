/-
`bucketBuffer.dedupe` (`tx_buffer.go`). `bb.dedupe()`: the entries sorted stably by key, the newest of each key kept: their
canonical form.
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

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

/-- `bb.dedupe()`: the entries sorted stably by key, the newest of each key kept: their
canonical form. -/
abbrev backend.bucketBuffer.dedupe.spec : Prop :=
  ∀ (bb : Loc) (es : List Ent),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownBB bb es }}
    (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"dedupe")) (Val #()))
  {{ RET #(); ownBB bb (canon es) }}

end spec

end EtcdGrove
end Perennial
