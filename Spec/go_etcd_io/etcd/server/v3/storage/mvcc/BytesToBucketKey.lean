/-
`BytesToBucketKey` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `BytesToBucketKey(bytes)` decodes the 17 bytes of a revision `r` with at most one byte after
them (any other length, another separator or a negative revision panics): the bucket key of `r`,
a tombstone iff the byte after is the mark. -/
abbrev mvcc.BytesToBucketKey.spec : Prop :=
  ∀ (s : GoSlice) (r : mvcc.Rev) (rest : List w8) (dq : DFrac),
  rest.length ≤ 1 → 0 ≤ sint.Z r.main → 0 ≤ sint.Z r.sub →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s ↦*{dq} (mvcc.revBytes r false ++ rest) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.BytesToBucketKey)) (Val #s))
  {{ RET #(BucketKey.mk (mvcc.revVal r) (decide (rest = [mvcc.markTomb])));
      s ↦*{dq} (mvcc.revBytes r false ++ rest) }}

end spec

end EtcdGrove
end Perennial
