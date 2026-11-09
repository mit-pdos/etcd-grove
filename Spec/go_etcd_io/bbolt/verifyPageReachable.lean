/-
`verifyPageReachable(...)` (`tx_check.go`): reports a page past the high-water mark, reached twice, or freed.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). 4d's `Page.Id`, `Page.Overflow`, `Page.IsBranchPage`,
`Page.IsLeafPage` on the page's bytes; the map operations on `reachable` and `freed`. The
premises are the "nothing to report" case, so the channel and the stack are never touched.

**Changes** (integration I7): was any nine `val`s, post `True`: false of ill-typed arguments (a map
lookup on a non-map) and of a report (a send on a channel with no resource). Now the arguments
typed, the page's bytes and the maps owned, and a well-formed page: in bounds, its run not yet
reached, not freed, a branch or a leaf.
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

/-- (internal) on a page of a well-formed tree (in bounds, its run of `1 + overflow` ids not yet
reached, not freed, a branch or leaf page): nothing reported, the run recorded as reached. -/
def verifyPageReachable.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (hwm : w64) (stack : GoSlice) (reach freed : Loc)
    (R : GMap w64 Loc) (Fd : GMap w64 Bool) (df : DFrac) (ch : val),
  (BboltCommon.pageHeaderSize ≤ bs.length ∧
    uint.nat (BboltCommon.hdrOf bs).id' ≤ uint.nat hwm ∧
    uint.nat (BboltCommon.hdrOf bs).id' + uint.nat (BboltCommon.hdrOf bs).overflow' < 2 ^ 64 ∧
    (∀ i : Nat, i ≤ uint.nat (BboltCommon.hdrOf bs).overflow' →
      R.lookup ((BboltCommon.hdrOf bs).id' + W64 (i : Int)) = none) ∧
    Fd.lookup (BboltCommon.hdrOf bs).id' ≠ some true ∧
    ((BboltCommon.hdrOf bs).flags' = BboltCommon.branchPageFlag ∨
      (BboltCommon.hdrOf bs).flags' = BboltCommon.leafPageFlag)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bytesPointsto p dq bs ∗
      ownMap reach (DFrac.own 1) R ∗ ownMap freed df Fd }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.bbolt.verifyPageReachable)) (Val #p)) (Val #hwm)) (Val #stack)) (Val #reach)) (Val #freed)) (Val ch))
  {{ RET #(); bytesPointsto p dq bs ∗ ownMap freed df Fd ∗
      ownMap reach (DFrac.own 1)
        ((List.range (uint.nat (BboltCommon.hdrOf bs).overflow' + 1)).foldl
          (fun m (i : Nat) => m.insert ((BboltCommon.hdrOf bs).id' + W64 (i : Int)) p) R) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
