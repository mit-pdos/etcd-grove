/-
`BucketKeyToBytes(rev, bytes)` (`revision.go:83`) into a 17- or 18-byte slice (shorter panics; a
longer one would keep its tail unmarked: not used): the bytes, `t` appended (17) or set (18) for a
tombstone. Internal (`delete`, `RevToBytes`). **Changes**: over `bucketKeyBytes`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `BucketKeyToBytes(bk, bytes)`. -/
def BucketKeyToBytes.spec : Prop :=
  ∀ (bk : BucketKey) (s : GoSlice) (bs : List w8),
  {{ pkgInit ∗ ⌜bs.length = 17 ∨ bs.length = 18⌝ ∗ s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.BucketKeyToBytes)) (Val #bk))
      (Val #s))
  {{ (s' : GoSlice), RET #s';
      s' ↦* bucketKeyBytes (revOf bk.Revision') bk.tombstone' (bs.drop 17) ∗
      ownSliceCap w8 s' (DFrac.own 1) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
