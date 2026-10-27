/-
`k8s.io/utils/buffer`'s growing ring buffer (`ring_growing.go`, `TypedRingGrowing[any]`, the
listeners' `pendingNotifications`): its ownership predicate. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the processor and listeners).

* `ownRing r q`: the ring at `r` holds the values `q`, oldest first: its storage `data` (`n`
  elements), the first readable element at `beg`, `readable` of them, wrapping around; `n < 2^62`
  (so that doubling it, `WriteOne`'s growth, does not overflow).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace buffer

open Iris Iris.BI k8s_io.utils.buffer

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.buffer.Assumptions]

/-- The values a ring's storage holds from `beg`, `rd` of them, wrapping around at `n`. -/
def ringVals (data : List GoInterface) (n beg rd : Nat) : List GoInterface :=
  (List.range rd).map (fun i => data.getD ((beg + i) % n) interface.nil)

/-- **The ring at `r` holds `q`**, oldest first. -/
def ownRing (r : Loc) (q : List GoInterface) : IProp GF :=
  iprop(∃ (sl : GoSlice) (data : List GoInterface) (n beg rd : Nat),
    r ↦ (TypedRingGrowing.mk sl (W64 n) (W64 beg) (W64 rd) : TypedRingGrowing GoInterface) ∗
    sl ↦* data ∗ ownSliceCap GoInterface sl (DFrac.own 1) ∗
    ⌜data.length = n ∧ n < 2 ^ 62 ∧ (n = 0 → beg = 0) ∧ (0 < n → beg < n) ∧ rd ≤ n ∧
      q = ringVals data n beg rd⌝)

end defs

end buffer
end EtcdGrove
end Perennial
