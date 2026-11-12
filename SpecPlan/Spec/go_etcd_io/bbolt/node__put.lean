/-
`n.put(old, new, v, pgid, flags)` (`node.go`): panics on a page id at or above the high-water mark or an empty key. Users: `Bucket.Put`, `CreateBucket`, `node.spill` (the parent's key), `Bucket.spill`.
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

/-- (internal) the inode at `old` replaced or inserted (`NodeR.put`); the key and value kept by reference. -/
def node.put.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (old new v : GoSlice) (ob nb vb : GoString) (d1 d2 d3 : DFrac) (pg : w64) (fl : w32),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ old ↦*{d1} ob ∗ new ↦*{d2} nb ∗ v ↦*{d3} vb ∗ ⌜uint.nat pg < uint.nat C.hwm ∧ ob ≠ [] ∧ nb ≠ []⌝ }}
    (App (App (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"put")) (Val #old)) (Val #new)) (Val #v)) (Val #pg)) (Val #fl))
  {{ RET #(); old ↦*{d1} ob ∗ wtxCore tx γ { C with nodes := fun x => if x = n then some (N.put ob nb vb pg fl) else C.nodes x } }}

end spec

end Bbolt
end EtcdGrove
end Perennial
