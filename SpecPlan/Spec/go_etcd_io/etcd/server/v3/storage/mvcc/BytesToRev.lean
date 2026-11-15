/-
`BytesToRev(bytes)` (`revision.go:58`): `BytesToBucketKey(bytes).Revision`; the bytes must parse
(`revOfBytes`: `BytesToBucketKey` panics otherwise). Internal (`restore`, the hasher, the
compaction). **Changes**: over `revOfBytes` (any parsable bytes, a tombstone's too).
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

/-- `BytesToRev(bytes)` of parsable bytes. -/
def BytesToRev.spec : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (dq : DFrac) (r : Rev) (t : Bool),
  {{ pkgInit ∗ ⌜revOfBytes bs = some (r, t)⌝ ∗ s ↦*{dq} bs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev)) (Val #s))
  {{ RET #(revVal r); s ↦*{dq} bs }}

end spec
end Mvcc
end EtcdGrove
end Perennial
