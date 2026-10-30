module
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]
-- `hash.Hash64`'s type (its underlying interface): `internal/common` reaches `hash` only
-- through `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `m.Write(p)`: the meta goes onto the meta page `p` (its id `txid % 2`, its type meta),
with its checksum set (in `m` too). It panics if the root bucket or the freelist page is at
or above the high-water mark. -/
abbrev Meta.Write.spec : Prop :=
  ∀ (l p : Loc) (v : Meta) (pg : Page) (w : Meta),
  l.locCar ≠ 0 → uint.Z v.root'.root' < uint.Z v.pgid' →
  (uint.Z v.freelist' < uint.Z v.pgid' ∨ v.freelist' = W64 18446744073709551615) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v ∗ p ↦ pg ∗ (p +ₗ 16) ↦ w }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Write")) (Val #p))
  {{ RET #();
      l ↦ ({ v with checksum' := fnv64a ((metaBytes v).take 56) } : Meta) ∗
      p ↦ ({ pg with id' := v.txid' % W64 2, flags' := W16 4 } : Page) ∗
      (p +ₗ 16) ↦ ({ v with checksum' := fnv64a ((metaBytes v).take 56) } : Meta) }}

end spec

end bbolt
end EtcdGrove
end Perennial
