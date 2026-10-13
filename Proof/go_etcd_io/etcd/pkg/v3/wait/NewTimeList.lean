/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/NewTimeList.lean`. Lean-first (no Rocq counterpart); the
request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.NewTimeList

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
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.NewTimeList.wp_proof : wait.NewTimeList.spec (GF := GF) (hG := hG) := by
  intro P
  wp_start as ⟨#HP0, #Hmono, #Hcl⟩
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %mref Hm
  wp_alloc tl as Htl
  iStructNamed Htl
  ipersist m
  imod sync.init_Mutex (timeListR tl mref P) ⊤ (tlLockAddr tl) $$ l [lastTriggerDeadline Hm] with #Hmu
  · inext
    iunfold timeListR
    iexists (0 : w64), ∅
    iframe lastTriggerDeadline Hm
    isplitr
    · rw [show (0 : w64) = W64 0 from rfl]; iexact HP0
    iapply BigSepM.bigSepM_empty.2
    itrivial
  (try wp_auto)
  iapply HΦ
  iunfold isTimeList
  iexists mref
  iframe #

end proof

end EtcdGrove
end Perennial
