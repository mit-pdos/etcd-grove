/-
Lean-first (no Rocq counterpart).

# The driver's predicates select by `selOkL` (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.3, §6)

From the driver's selector and attribute specs: `predicate(in)`'s label and field selectors meet
`labelSelOk`/`fieldSelOk` (`labelSelOk_driver`, `fieldSelOk_driver`), `getAttrs` meets `getAttrsOk` for
a `*Obj` at any fraction (`getAttrsOk_ptr`) and for the store's objects (`getAttrsOk_D`), and with
`SelectionPredicate`'s general specs the predicate selects by `selD x` and is empty iff
`predEmptyL x` (`predOk_driver`, the Draft's fact; its callee specs as premises), and on a model
object at a pointer answers `selOkL x` (`matches_ptr`, what `mlist` calls).
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOkDefs

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

theorem mlistMatches.wp_proof
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    mlistMatches.spec (GF := GF) (hG := hG) := by
  intro pp x op o dq
  iintro %Φ ⟨#Hpkg, Hp, Ho⟩ HΦ
  ihave #Hl := labelSelOk_driver wp_LM wp_LE x $$ Hpkg
  ihave #Hf := fieldSelOk_driver wp_FM wp_FE x $$ Hpkg
  ihave #Hg0 := getAttrsOk_ptr wp_GA dq $$ Hpkg
  ihave #Hg : getAttrsOk (objAtPtr dq) (predV x).GetAttrs' labMapL fldMapL $$ []
  · simp only [predV]; iexact Hg0
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave Hobj : objAtPtr dq (interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op) o $$ [Ho]
  · unfold objAtPtr; iexists op; iframe Ho; ipureintro; rfl
  wp_apply (wp_Matches Obj (objAtPtr dq) pp (DFrac.own 1) (predV x) _ _ _ _ labMapL fldMapL _ o rfl)
    $$ [$Hp $Hl $Hf $Hg $Hobj] as ⟨Hp, Hobj⟩
  rw [sel_answer]
  iapply HΦ
  iframe Hp
  unfold objAtPtr
  icases Hobj with ⟨%p', %hp', Ho⟩
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hp'
  have hpe : op = p' := go.intoVal_inj hp'
  subst hpe
  iexact Ho

theorem mlistPCT.wp_proof
    (wp_PCT : storage.PrepareContinueToken.spec (GF := GF) (hG := hG))
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_Empty : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    mlistPCT.spec (GF := GF) (hG := hG) := by
  intro kl kp rv cnt more x
  iintro %Φ #Hpkg HΦ
  ihave #Hsel0 := predOk_driver wp_Matches wp_Empty wp_LM wp_LE wp_FM wp_FE wp_GA x $$ Hpkg
  ihave #Hsel : selPredOk driverSpec (listOptsV x).Predicate' (selD x) (predEmptyL x) $$ []
  · simp only [listOptsV]; iexact Hsel0
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  wp_apply (wp_PCT DObj driverSpec kl kp rv cnt more (listOptsV x) (selD x) (predEmptyL x))
    $$ [$Hsel] as %c %rem %err Hr
  iapply HΦ $$ Hr

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
