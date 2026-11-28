/-
The proof of `Spec/time/Until.lean`, from Perennial's translated body, as Perennial's
`time.Since.wp_proof` (its callees' specs are Perennial's).
-/
module

public import Spec.time.Until
public import Perennial.Spec.time.runtimeIsBubbled
public import Perennial.Spec.time.runtimeNano
public import Perennial.Spec.time.subMono
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Sub
public import Perennial.Proof.time.PtrMethods

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

open _root_.Perennial.time in
theorem time.Until.wp_proof
    (wp_runtimeIsBubbled : _root_.Perennial.time.runtimeIsBubbled.spec (GF := GF) (hG := hG))
    (wp_runtimeNano : _root_.Perennial.time.runtimeNano.spec (GF := GF) (hG := hG))
    (wp_subMono : _root_.Perennial.time.subMono.spec (GF := GF) (hG := hG))
    (wp_Now : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (wp_Time_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG)) :
    time.Until.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨⟨%sn, #Hsn⟩, ⟨%loc, #Hloc⟩, -⟩
  wp_auto
  repeat' (first | wp_if_destruct |
    (wp_apply wp_runtimeIsBubbled as %b -; cases b <;> (try wp_auto)) |
    wp_apply wp_runtimeNano as %x - | wp_apply wp_subMono as %d - |
    wp_apply wp_Now as %now - | wp_apply wp_Time_Sub as %d - |
    wp_apply Time.wp_ptr_Sub_of wp_Time_Sub $$ [$t] as %d t)
  all_goals wp_end

end proof

end EtcdGrove
end Perennial
