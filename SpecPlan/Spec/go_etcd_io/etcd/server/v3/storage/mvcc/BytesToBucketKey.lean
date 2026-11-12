/-
`BytesToBucketKey(bytes)` (`revision.go:98`): the bucket key of parsable bytes (`revOfBytes`: a
length of 17 or 18, `_` at 8, non-negative main and sub; it panics otherwise). Internal (the hasher,
`BytesToRev`). **Changes**: over `revOfBytes`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

/-- `BytesToBucketKey(bytes)` of parsable bytes. -/
def BytesToBucketKey.spec : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (dq : DFrac) (r : Rev) (t : Bool),
  {{ pkgInit ∗ ⌜revOfBytes bs = some (r, t)⌝ ∗ s ↦*{dq} bs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.BytesToBucketKey)) (Val #s))
  {{ RET #({ Revision' := revVal r, tombstone' := t } : BucketKey); s ↦*{dq} bs }}

end spec
end Mvcc
end EtcdGrove
end Perennial
