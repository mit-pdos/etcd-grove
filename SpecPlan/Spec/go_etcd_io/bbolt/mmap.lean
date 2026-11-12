/-
`mmap(db, sz)` (`bolt_unix.go`): `unix.Mmap` read-only shared (`MmapFlags`), `madvise`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) mapped `sz` bytes, or an error. -/
def mmap.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM) (sz : w64),
  {{ dbRaw (GF := GF) db γ M }}
    (App (App (Val (@! go_etcd_io.bbolt.mmap)) (Val #db)) (Val #sz))
  {{ (err : GoInterface), RET #err; ∃ M' : DbM, dbRaw db γ M' ∗ ⌜err = GoInterface.nil → M'.dataSz = uint.nat sz⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
