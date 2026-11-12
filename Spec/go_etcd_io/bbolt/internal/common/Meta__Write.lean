/-
`(*Meta).Write`'s spec (`internal/common/meta.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Model.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `m.Write(p)`: sets `m`'s checksum (`metaSum`), the page header's id to `txid % 2` and its flags
to `MetaPageFlag` (4), and copies `*m` into the meta after the header (`p.Meta()`, 16 bytes past
`p`). It panics if the root bucket's page or the freelist page (unless `PgidNoFreelist`) is at or
above the high-water mark `pgid`: the premises exclude both. -/
abbrev Meta.Write.spec : Prop :=
  ∀ (l p : Loc) (v : Meta) (hdr : Page) (w : Meta),
  uint.Z v.root'.root' < uint.Z v.pgid' →
  (uint.Z v.freelist' < uint.Z v.pgid' ∨ v.freelist'.toNat = pgidNoFreelist) →
  0 < l.addr → 0 < p.addr → p.addr + 16 ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v ∗ p ↦ hdr ∗ (p +ₗ 16) ↦ w }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Write")) (Val #p))
  {{ RET #();
      l ↦ ({ v with checksum' := metaSum v } : Meta) ∗
      p ↦ ({ hdr with id' := v.txid' % W64 2, flags' := W16 4 } : Page) ∗
      (p +ₗ 16) ↦ ({ v with checksum' := metaSum v } : Meta) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
