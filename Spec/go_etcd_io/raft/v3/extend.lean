/-
## `extend(dst, vals)` (internal)

**Users**: `slice` (`log.go`: the storage's part, then the unstable part). **Proof sketch**: `need :=
len + len` (an `int`: below `2^63` by the premise); in place into `dst`'s capacity (owned), or a
fresh exact allocation. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/extend.lean`: the in-place case admitted (with
`dst`'s capacity), the `int` bound made explicit (it was unproved).
**Margin**: none.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) `dst ++ vals`, appended in place if `dst`'s capacity allows, else in a fresh exact slice. -/
def extend.spec : Prop :=
  ∀ (dst vals : GoSlice) (k : Nat) (ds vs : List LogEntry),
  ds.length + vs.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entriesRO dst k ds ∗ entriesRO vals (k + ds.length) vs ∗
      (⌜sint.Z dst.cap < (ds.length : Int) + (vs.length : Int)⌝ ∨ ownSliceCap Loc dst (DFrac.own 1)) }}
    (App (App (Val (@! go_etcd_io.raft.v3.extend)) (Val #dst)) (Val #vals))
  {{ (s : GoSlice), RET #s; entriesRO s k (ds ++ vs) ∗ ownSliceCap Loc s (DFrac.own 1) }}

end spec
end Raft
end EtcdGrove
end Perennial
