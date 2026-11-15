/-
`cloneBytes(v)` (`bucket.go`): a fresh copy of `v` (`make` and `copy`). (internal, mirrors the code)

**Users.** `Put`, `CreateBucket*`, `DeleteBucket` (the key they keep). **Proof sketch.**
Perennial's `make` and `copy`. **Changes.** Unchanged.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- (internal) `cloneBytes(v)`: a fresh slice holding `v`'s bytes. -/
def cloneBytes.spec : Prop :=
  ∀ (v : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ v ↦*{dq} bs }}
    (App (Val (@! go_etcd_io.bbolt.cloneBytes)) (Val #v))
  {{ (c : GoSlice), RET #c; c ↦* bs ∗ v ↦*{dq} bs }}

end spec

end Bbolt
end EtcdGrove
end Perennial
