/-
`BucketKeyToBytes` (`revision.go`). Lean-first (no Rocq counterpart); see `RevBytes.lean`.
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

/-- `BucketKeyToBytes(rev, bytes)` writes the 17 bytes of `rev` into `bytes`, a buffer of 17 or
18 bytes (the caller's `NewRevBytes()`), and, for a tombstone, the mark after them (appended if
the buffer has 17 bytes, else over its 18th); it returns the buffer. -/
abbrev mvcc.BucketKeyToBytes.spec : Prop :=
  ∀ (bk : BucketKey) (s : GoSlice) (bs : List w8), bs.length = 17 ∨ bs.length = 18 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.BucketKeyToBytes)) (Val #bk))
      (Val #s))
  {{ (s' : GoSlice), RET #s';
      s' ↦* mvcc.bucketKeyBytes (mvcc.revOf bk.Revision') bk.tombstone' (bs.drop 17) ∗
      ownSliceCap w8 s' (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
