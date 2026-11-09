/-
`db.getPageSizeFromSecondMeta()` (`db.go`): page 1's meta, at offsets the fork reads only after page 0 was read.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `ReadAt` of 4 KiB over OsFs into a local array; `pageInBuffer(buf, 0)`
(id 0: any page size); 4d's `Page.Meta` (`metaLoc`), `meta_view`, `Meta.Validate` (`metaErr`); a valid
meta's `PageSize` is 4096 by `dbRaw`'s file invariant (every valid meta of the file records 4096;
the probes at 1 KiB, 2 KiB find the zero tail of meta page 0, at 4 KiB meta page 1).

**Changes** (integration I7): the post's page size is promised on `err = nil`, not on the
`metaCanRead` flag (which is `true` with `ErrInvalid` when the read succeeded and the meta does not
validate: the old post was false there).
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) its page size (4096) if its meta is valid (`err = nil`); `ok`: the meta could be read. -/
def DB.getPageSizeFromSecondMeta.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"getPageSizeFromSecondMeta")) (Val #()))
  {{ (z : w64) (ok : Bool) (err : GoInterface), RET (PairV #z (PairV #ok #err)); dbRaw db γ M ∗ ⌜err = GoInterface.nil → uint.nat z = 4096⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
