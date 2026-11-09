/-
`RevToBytes(rev, bytes)` (`revision.go:54`): a non-tombstone bucket key's bytes written into
`bytes` (at least 17 long: `PutUint64` and `bytes[8]` panic otherwise), the same slice returned.
Internal (`restore`, `put`, `rangeKeys`, the compaction keys). **Changes**: any length `≥ 17`
(the bytes past the 17th unchanged), no capacity needed (no append).
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

/-- `RevToBytes(rev, bytes)`. -/
def RevToBytes.spec : Prop :=
  ∀ (rev : Revision) (s : GoSlice) (bs : List w8),
  {{ pkgInit ∗ ⌜17 ≤ bs.length⌝ ∗ s ↦* bs }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes)) (Val #rev)) (Val #s))
  {{ RET #s; s ↦* (revBytes (revOf rev) false ++ bs.drop 17) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
