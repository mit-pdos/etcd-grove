/-
The selection predicate's lemmas and the specs of `mlistMatches` and `mlistPCT` (`labelSelOk_driver`,
`sel_answer`, `predOk_driver`, ...), out of `PredOk.lean`'s proofs so that `WRun.lean` (which specs
import) imports them without the proofs (import tiers, 2026-11-18).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel__Matches
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel__Matches
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel__Empty
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel__Empty
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__Matches
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__Empty
public import Spec.k8s_io.apiserver.pkg.storage.PrepareContinueToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RefineList
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem labelSelOk_driver
    (wp_M : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_E : labelSel.Empty.spec (GF := GF) (hG := hG)) (x : Input) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      k8s.labelSelOk (predV x).Label' (labelSelL x).all' (lmL (labelSelL x)) := by
  iintro #Hp
  unfold k8s.labelSelOk
  iexists ⟨_, #(labelSelL x)⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %Ψ HΨ
    wp_apply (wp_E (labelSelL x))
    iexact HΨ
  · imodintro
    iintro %m %M %Ψ #Hm HΨ
    wp_apply (wp_M (labelSelL x) m M) $$ [$Hm]
    iexact HΨ

theorem fieldSelOk_driver
    (wp_M : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_E : fieldSel.Empty.spec (GF := GF) (hG := hG)) (x : Input) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      k8s.fieldSelOk (predV x).Field' (decide ((fieldSelForL x).n' = W64 0)) (fmL (fieldSelForL x)) := by
  iintro #Hp
  unfold k8s.fieldSelOk
  iexists ⟨_, #(fieldSelForL x)⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %Ψ HΨ
    wp_apply (wp_E (fieldSelForL x))
    iexact HΨ
  · imodintro
    iintro %m %M %Ψ #Hm HΨ
    wp_apply (wp_M (fieldSelForL x) m M) $$ [$Hm]
    iexact HΨ

/-- A model object at a pointer, at any fraction. -/
def objAtPtr (dq : DFrac) (x : GoInterface) (o : Obj) : IProp GF :=
  iprop(∃ p : Loc, ⌜x = interface.mkOk
    (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p⌝ ∗ p ↦{dq} o)

theorem getAttrsOk_ptr (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) (dq : DFrac) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      getAttrsOk (objAtPtr dq) (functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs [])
        labMapL fldMapL := by
  iintro #Hp
  unfold getAttrsOk
  imodintro
  iintro %x %o %Ψ Ho HΨ
  unfold objAtPtr
  icases Ho with ⟨%p, %hx, Ho⟩
  subst hx
  wp_apply (wp_GA p dq o) $$ [$Ho] as %lm %fm ⟨Ho, #Hl, #Hf⟩
  ihave Hobj : (∃ p' : Loc, ⌜interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p =
      interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p'⌝ ∗
      p' ↦{dq} o) $$ [Ho]
  · iexists p; iframe Ho; ipureintro; rfl
  iapply HΨ $$ Hobj Hl Hf

/-- What a predicate of the driver answers: `selOkL`, whichever way `Matches` decides it. -/
theorem sel_answer (x : Input) (o : Obj) :
    Bool.or ((labelSelL x).all' && decide ((fieldSelForL x).n' = W64 0))
      (lmL (labelSelL x) (labMapL o) && fmL (fieldSelForL x) (fldMapL o)) = selOkL x o := by
  rw [lmL_labMapL, fmL_fldMapL]
  unfold selOkL
  by_cases ha : (labelSelL x).all' = true <;> by_cases hn : (fieldSelForL x).n' = W64 0
  · have h1 : labelSelOk (labelSelL x) o = true := by simp [labelSelOk, ha]
    have h2 : fieldSelOk (fieldSelForL x) o = true := by
      simp [fieldSelOk, hn, show sint.Z (W64 0) = 0 from rfl]
    simp [ha, hn, h1, h2]
  · have hn' : ¬ (fieldSelForL x).n' = 0#64 := hn
    simp [ha, hn']
  all_goals simp [ha]

/-- `predicate(in).Matches(&o)` on a model object at a pointer: `selOkL x o` (what `mlist` calls;
7e-3b's hypothesis, #22, with the driver's package initialization in place of `storage`'s). -/
abbrev mlistMatches.spec : Prop :=
  ∀ (pp : Loc) (x : Input) (op : Loc) (o : Obj) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      pp ↦ predV x ∗ op ↦{dq} o }}
    (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
      @!! go!"Matches")) (Val #(interface.mkOk
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op)))
  {{ RET (PairV #(selOkL x o) #GoInterface.nil); pp ↦ predV x ∗ op ↦{dq} o }}
theorem getAttrsOk_D (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) (rv : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      getAttrsOk (fun x o => objAtD x o rv)
        (functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs [])
        (fun o : DObj => labMapL (o.toObj (W64 0))) (fun o => fldMapL (o.toObj (W64 0))) := by
  iintro #Hp
  unfold getAttrsOk
  imodintro
  iintro %x %o %Ψ Ho HΨ
  unfold objAtD
  icases Ho with ⟨%p, %n, %h, Ho⟩
  obtain ⟨hx, hnn, hrv⟩ := h
  subst hx
  wp_apply (wp_GA p (DFrac.own 1) (o.toObj n)) $$ [$Ho] as %lm %fm ⟨Ho, #Hl, #Hf⟩
  ihave Hobj : (∃ (p' : Loc) (n' : w64), ⌜interface.mkOk (go.GoType.PointerType objTyD) #p =
      interface.mkOk (go.GoType.PointerType objTyD) #p' ∧ p' ≠ null ∧ rv = rvStr n'⌝ ∗
      p' ↦ o.toObj n') $$ [Ho]
  · iexists p, n; iframe Ho; ipureintro; exact ⟨rfl, hnn, hrv⟩
  have hl : labMapL (o.toObj n) = labMapL (o.toObj (W64 0)) := rfl
  have hf : fldMapL (o.toObj n) = fldMapL (o.toObj (W64 0)) := rfl
  rw [hl, hf]
  iapply HΨ $$ Hobj Hl Hf

/-- **`predicate(in)` selects by `selD x` and is empty iff `predEmptyL x`** (the Draft's
`predOk_driver`, its callee specs as premises). -/
theorem predOk_driver
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_Empty : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) (x : Input) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      selPredOk driverSpec (predV x) (selD x) (predEmptyL x) := by
  iintro #Hpkg
  ihave #Hl := labelSelOk_driver wp_LM wp_LE x $$ Hpkg
  ihave #Hf := fieldSelOk_driver wp_FM wp_FE x $$ Hpkg
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  unfold selPredOk
  isplitr
  · ipureintro
    refine ⟨rfl, fun he o => ?_⟩
    have := sel_answer x (o.toObj (W64 0))
    unfold predEmptyL at he
    simp only [selD]
    rw [← this, he]
  isplitr
  · imodintro
    iintro %pp %dq %x' %o %rv %Ψ Hp Ho HΨ
    rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl]
    ihave #Hg0 := getAttrsOk_D wp_GA rv $$ Hpkg
    ihave #Hg : getAttrsOk (fun x o => objAtD x o rv) (predV x).GetAttrs'
        (fun o : DObj => labMapL (o.toObj (W64 0))) (fun o => fldMapL (o.toObj (W64 0))) $$ []
    · simp only [predV]; iexact Hg0
    wp_apply (wp_Matches DObj (fun x o => objAtD x o rv) pp dq (predV x) _ _ _ _ _ _ x' o rfl)
      $$ [$Hp $Hl $Hf $Hg $Ho] as ⟨Hp, Ho⟩
    have hs := sel_answer x (o.toObj (W64 0))
    simp only [selD]
    rw [← hs]
    iapply HΨ $$ Hp Ho
  · imodintro
    iintro %pp %dq %Ψ Hp HΨ
    wp_apply (wp_Empty pp dq (predV x) _ _ _ _ rfl) $$ [$Hp $Hl $Hf] as Hp
    simp only [predEmptyL]
    iapply HΨ $$ Hp

/-- `storage.PrepareContinueToken` at a list's options (7e-3b's hypothesis, #22, with the driver's
package initialization in place of `storage`'s): what `mlist` calls. -/
abbrev mlistPCT.spec : Prop :=
  ∀ (kl kp : GoString) (rv cnt : w64) (more : Bool) (x : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.PrepareContinueToken))
      (Val #kl)) (Val #kp)) (Val #rv)) (Val #cnt)) (Val #more)) (Val #(listOptsV x)))
  {{ (c : GoString) (rem : Loc) (err : GoInterface), RET (PairV (PairV #c #rem) #err);
      if more then
        (if encOkL (kl ++ [W8 0]) kp then
          ⌜err = GoInterface.nil ∧ c = encL (kl ++ [W8 0]) kp rv⌝ ∗
            (if predEmptyL x then rem ↦ (cnt - x.Limit') else ⌜rem = null⌝)
        else ⌜err ≠ GoInterface.nil⌝)
      else ⌜c = [] ∧ rem = null ∧ err = GoInterface.nil⌝ }}

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
