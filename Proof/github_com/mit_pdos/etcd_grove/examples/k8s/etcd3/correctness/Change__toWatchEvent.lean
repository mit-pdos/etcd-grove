/-
Lean-first (no Rocq counterpart).

The proof of `Change.toWatchEvent`: `chgOk` rules out the panic; the predicate's answers on the object
and the one before it are `selOkL`'s (`mlistMatchesW`); a Deleted event's object is a fresh copy of the
one before, at the change's resource version, made read-only.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change__toWatchEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__UpdateObject
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- No event. -/
local macro "twe_none" : tactic => `(tactic| (
  iapply HΦ
  isplitl [] <;> ipureintro <;> rfl))

set_option hygiene false in
/-- An Added or Modified event: the change's object. -/
local macro "twe_obj" : tactic => `(tactic| (
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists _
  iframe
  unfold evRep evObjRep
  isplitr
  · ipureintro; rfl
  rw [hop]
  simp only [optObjD]
  iexact Ho0))

theorem Change.toWatchEvent.wp_proof
    (wp_Matches : mlistMatchesW.spec (GF := GF) (hG := hG))
    (wp_DC : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_UO : k8s_etcd3.versioner.UpdateObject.spec (GF := GF) (hG := hG)) :
    Change.toWatchEvent.spec (GF := GF) (hG := hG) := by
  intro cv c x hc
  have hpw : predWV x x.Bookmarks' = { predV x with AllowWatchBookmarks' := x.Bookmarks' } := rfl
  wp_start as #Hc
  iunfold changeVRep at Hc
  icases Hc with ⟨%hkr, #Ho, #Hp⟩
  wp_auto
  cases hobj : c.obj with
  | none =>
    cases hprev : c.prev with
    | none => exfalso; unfold chgOk at hc; simp [hobj, hprev] at hc
    | some po =>
      isimp only [hobj, optObjD] at Ho
      iunfold deepRep at Ho
      icases Ho with %hon
      ihave #Hp0 := Hp
      isimp only [hprev, optObjD] at Hp
      iunfold deepRep at Hp
      icases Hp with ⟨%pp, %hpp, #Hpp⟩
      rw [hon]
      wp_auto
      rw [hpp]
      wp_auto
      rw [hon]
      wp_auto
      rw [hpp]
      wp_auto
      rw [hpp]
      isimp only [hpw] at pred
      wp_apply (wp_Matches pred_ptr x x.Bookmarks' pp po DFrac.discard) $$ [$Hpkg2 $pred $Hpp] as ⟨pred, -⟩
      (try wp_auto)
      have hte : toWatchEventL x c =
          (if selOkL x po then some ⟨evDeleted, .obj { po with ResourceVersion' := c.rv }⟩ else none) := by
        simp only [toWatchEventL, hobj, hprev, Option.any_some, Option.any_none, Option.map_some]
        simp
      rw [hte]
      rw [show (zero_val Bool) = false from rfl]
      cases hs2 : selOkL x po
      all_goals simp only [↓reduceIte, Bool.false_eq_true]
      all_goals (try wp_auto)
      · twe_none
      · rw [hpp]
        iapply wp_fupd
        wp_auto
        wp_apply (wp_DC pp DFrac.discard po) $$ [$Hpkg2 $Hpp] as %cp ⟨-, Hcp⟩
        rw [hkr.2]
        wp_apply (wp_UO cp po c.rv) $$ [$Hpkg2 $Hcp] as Hcp
        ipersist Hcp
        ihave #Hd : deepRO (GF := GF) (interface.mkOk
            (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #cp)
            (.obj { po with ResourceVersion' := c.rv }) $$ []
        · iunfold deepRep
          iexists cp
          iframe Hcp
          ipureintro; rfl
        imodintro
        iapply HΦ
        isplitr
        · ipureintro; rfl
        iexists _
        iframe
        unfold evRep evObjRep
        isplitr
        · ipureintro; rfl
        simp only [optObjD]
        iexact Hd
  | some o =>
    ihave #Ho0 := Ho
    isimp only [hobj, optObjD] at Ho
    iunfold deepRep at Ho
    icases Ho with ⟨%op, %hop, #Hop⟩
    rw [hop]
    wp_auto
    rw [hop]
    wp_auto
    rw [hop]
    isimp only [hpw] at pred
    wp_apply (wp_Matches pred_ptr x x.Bookmarks' op o DFrac.discard) $$ [$Hpkg2 $pred $Hop] as ⟨pred, -⟩
    (try wp_auto)
    cases hprev : c.prev with
    | none =>
      isimp only [hprev, optObjD] at Hp
      iunfold deepRep at Hp
      icases Hp with %hpn
      rw [hpn]
      wp_auto
      rw [show (zero_val Bool) = false from rfl]
      have hte : toWatchEventL x c =
          (if selOkL x o then some ⟨evAdded, .obj o⟩ else none) := by
        simp only [toWatchEventL, hobj, hprev, Option.any_some, Option.any_none, Option.map_some]
        simp
      rw [hte]
      cases hs1 : selOkL x o
      all_goals simp only [↓reduceIte, Bool.false_eq_true]
      all_goals (try wp_auto)
      · twe_none
      · twe_obj
    | some po =>
      isimp only [hprev, optObjD] at Hp
      iunfold deepRep at Hp
      icases Hp with ⟨%pp, %hpp, #Hpp⟩
      rw [hpp]
      wp_auto
      rw [hpp]
      wp_apply (wp_Matches pred_ptr x x.Bookmarks' pp po DFrac.discard) $$ [$Hpkg2 $pred $Hpp] as ⟨pred, -⟩
      (try wp_auto)
      have hte : toWatchEventL x c = (if selOkL x o && selOkL x po then some ⟨evModified, .obj o⟩
          else if selOkL x o then some ⟨evAdded, .obj o⟩
          else if selOkL x po then some ⟨evDeleted, .obj { po with ResourceVersion' := c.rv }⟩ else none) := by
        simp only [toWatchEventL, hobj, hprev, Option.any_some, Option.map_some]
      rw [hte]
      cases hs1 : selOkL x o <;> cases hs2 : selOkL x po
      all_goals simp only [Bool.and_true, Bool.and_false, ↓reduceIte, Bool.false_eq_true]
      all_goals (try wp_auto)
      · twe_none
      · rw [hpp]
        iapply wp_fupd
        wp_auto
        wp_apply (wp_DC pp DFrac.discard po) $$ [$Hpkg2 $Hpp] as %cp ⟨-, Hcp⟩
        rw [hkr.2]
        wp_apply (wp_UO cp po c.rv) $$ [$Hpkg2 $Hcp] as Hcp
        ipersist Hcp
        ihave #Hd : deepRO (GF := GF) (interface.mkOk
            (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #cp)
            (.obj { po with ResourceVersion' := c.rv }) $$ []
        · iunfold deepRep
          iexists cp
          iframe Hcp
          ipureintro; rfl
        imodintro
        iapply HΦ
        isplitr
        · ipureintro; rfl
        iexists _
        iframe
        unfold evRep evObjRep
        isplitr
        · ipureintro; rfl
        simp only [optObjD]
        iexact Hd
      · twe_obj
      · twe_obj

end proof

end k8s_correctness
end EtcdGrove
end Perennial
