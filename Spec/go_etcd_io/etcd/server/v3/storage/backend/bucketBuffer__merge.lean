/-
`bucketBuffer.merge` (`tx_buffer.go`). `bb.merge(src)` of two sorted buffers: `src`'s entries added, then the buffer
deduplicated unless it is already sorted: the canonical form of the entries followed by `src`'s.
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

/-- `bb.merge(src)` of two sorted buffers: `src`'s entries added, then the buffer
deduplicated unless it is already sorted: the canonical form of the entries followed by `src`'s. -/
abbrev backend.bucketBuffer.merge.spec : Prop :=
  ∀ (bb : Loc) (es : List Ent) (src : Loc) (es2 : List Ent),
  entsSorted es → entsSorted es2 → es.length + es2.length < bufBound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownBB bb es ∗ ownBB src es2 }}
    (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"merge")) (Val #src))
  {{ RET #(); ownBB bb (canon (es ++ es2)) ∗ ownBB src es2 }}

end spec

end EtcdGrove
end Perennial
