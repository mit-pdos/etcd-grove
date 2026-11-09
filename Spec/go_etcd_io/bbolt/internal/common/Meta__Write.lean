/-
## `(*Meta).Write(p)` (`internal/common/meta.go`)

**Users.** tx.go:609 (`Tx.writeMeta`... `tx.meta.Write(p)` into a page-pool buffer, then `WriteAt` at slot `txid % 2`). Snippet `ReqMetaRoundTrip`.
**Proof sketch.** the two checks (premises), `SetId`/`SetFlags` on the page, `Sum64`, a store of the checksum, `Copy` to `p.Meta()` through `meta_view`.
**Changes.** from `specs-ref`'s file of the same name: the page as its bytes (`withHdr`, `withMeta`) instead of a typed header and a typed meta after it.
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `m.Write(p)`: sets `m`'s checksum (`metaSummed`), the page header's id to `txid % 2` and its flags to `MetaPageFlag`, and copies the meta after the header. It panics if the root bucket's page, or the freelist page (unless `PgidNoFreelist`), is at or above the high-water mark: the premise excludes both. -/
def Meta.Write.spec : Prop :=
  ∀ (l p : Loc) (v : Meta) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v ∗ bytesPointsto p (DFrac.own 1) bs ∗
      ⌜0 < l.addr ∧ pageHeaderSize + metaSize ≤ bs.length ∧
        uint.Z v.root'.root' < uint.Z v.pgid' ∧
        (uint.Z v.freelist' < uint.Z v.pgid' ∨ v.freelist' = pgidNoFreelist)⌝ }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Write")) (Val #p))
  {{ RET #(); l ↦ metaSummed v ∗
      bytesPointsto p (DFrac.own 1)
        (withMeta (withHdr bs { hdrOf bs with id' := v.txid' % W64 2, flags' := metaPageFlag })
          (metaSummed v)) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
