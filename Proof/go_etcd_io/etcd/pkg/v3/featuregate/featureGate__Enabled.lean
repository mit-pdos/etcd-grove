/-
`(*featureGate).Enabled` (see its spec): two `Load`s of persistently held `Value`s, a type assertion
each, two map lookups in read-only maps; the panic is unreachable (the feature is set or registered).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.featureGate__Enabled
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.Assumptions]

theorem featuregate.featureGate.Enabled.wp_proof :
    featuregate.featureGate.Enabled.spec (GF := GF) (hG := hG) := by
  intro p K E f Hf
  unfold featuregate.isGate
  wp_start
  icases Hpre with ⟨%km, %em, #Hk, #HK, #He, #HE⟩
  wp_auto
  wp_apply_core sync.atomic.Value.wp_Load _ DFrac.discard $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe He
  iintro -
  imod Hcl with -
  imodintro
  wp_auto
  wp_apply wp_map_lookup2 $$ HE as -
  cases hE : E !! f with
  | some b =>
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    have hv : featuregate.gateValue K E f = b := by simp [featuregate.gateValue, hE]
    rw [hv]
    iapply HΦ
    itrivial
  | none =>
    simp only [Option.isSome_none, _root_.decide_false, Option.getD_none, Bool.false_eq_true]
    wp_auto
    wp_apply_core sync.atomic.Value.wp_Load _ DFrac.discard $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists _
    iframe Hk
    iintro -
    imod Hcl with -
    imodintro
    wp_auto
    wp_apply wp_map_lookup2 $$ HK as -
    cases hK : K !! f with
    | some sp =>
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      have hv : featuregate.gateValue K E f = sp.Default' := by simp [featuregate.gateValue, hE, hK]
      rw [hv]
      iapply HΦ
      itrivial
    | none =>
      exfalso
      rw [hE, hK] at Hf
      simp at Hf

end proof

end EtcdGrove
end Perennial
