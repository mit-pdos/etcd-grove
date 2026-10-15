/-
`bucketBuffer.add` (`tx_buffer.go`). `bb.add(k, v)`: the entry appended (the buffer grown to `3/2` of its length when full;
the slices kept, read-only).
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

/-- `bb.add(k, v)`: the entry appended (the buffer grown to `3/2` of its length when full;
the slices kept, read-only). -/
abbrev backend.bucketBuffer.add.spec : Prop :=
  ∀ (bb : Loc) (es : List Ent) (k v : GoSlice) (kb vb : GoString),
  es.length < bufBound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownBB bb es ∗ k ↦*□ kb ∗ v ↦*□ vb }}
    (App (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"add")) (Val #k)) (Val #v))
  {{ RET #(); ownBB bb (es ++ [(kb, vb)]) }}

end spec

end EtcdGrove
end Perennial
