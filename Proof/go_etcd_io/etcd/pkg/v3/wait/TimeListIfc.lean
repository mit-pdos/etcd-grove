/-
`pkg/wait`'s `WaitTime` contract for a `*timeList` (`wait_time.go`): `isWaitTime` of the interface
value from `isTimeList`, by the specs of `Wait` and `Trigger`. Lean-first (no Rocq counterpart);
the request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Wait
public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Trigger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A `*timeList` is a `WaitTime`** (as an interface value), from the specs of its methods. -/
theorem isWaitTime_of_timeList (hW : wait.timeList.Wait.spec (GF := GF) (hG := hG))
    (hT : wait.timeList.Trigger.spec (GF := GF) (hG := hG)) (tl : Loc) (P : w64 → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ isTimeList tl P ⊢
      isWaitTime (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty) #tl) P := by
  iintro ⟨#Hpkg, #Htl⟩
  iunfold isWaitTime
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty, #tl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %d %Φ !> - HΦ
    wp_apply hW tl P d $$ []
    · iframe #
    iexact HΦ
  · iintro !> %d %Φ !> #HP HΦ
    wp_apply hT tl P d $$ []
    · iframe #
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
