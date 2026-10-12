/-
Proof of `Spec/.../mvcc/watcherGroup__chooseAll.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__chooseAll

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watcherGroup.chooseAll.wp_proof :
    mvcc.watcherGroup.chooseAll.spec (GF := GF) (hG := hG) := by
  intro wg W ST curRev compactRev
  wp_start as ⟨Hg, HST, %Hdom, %Hst⟩
  icases mvcc.ownWatcherGroup_watchers wg W $$ Hg with ⟨%v, Hwg, Hws, Hback⟩
  iunfold mvcc.ownWatcherSet at Hws
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (m : w64) (wv : Loc),
      "minRev" ∷ minRev_ptr ↦ m ∗ "w" ∷ w_ptr ↦ wv ∗ "HST" ∷ mvcc.ownStates ST ∗
      "curRev" ∷ curRev_ptr ↦ curRev ∗ "compactRev" ∷ compactRev_ptr ↦ compactRev ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ sint.Z m = mvcc.minRevL ST (keys.take i.toNat)⌝)) $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [minRev w HST curRev compactRev]
  · iexists _, _
    simp only [named]
    iframe
    ipureintro
    exact ⟨Int.le_refl _, by simp [mvcc.minRevL]; decide⟩
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    obtain ⟨st, hst⟩ : ∃ st, ST !! key = some st := by
      have h := Hdom key (by
        have := (GMap.lookup_fmap (fun _ => ()) W key ▸ Hu : (W !! key).map (fun _ => ()) = some ())
        cases hW : W !! key with
        | none => rw [hW] at this; cases this
        | some _ => rfl)
      exact Option.isSome_iff_exists.1 h
    obtain ⟨hc1, hc2, hc3⟩ := Hst key st hst
    iunfold mvcc.ownStates at HST
    icases (BigSepM.bigSepM_lookup_acc hst).1 $$ HST with ⟨Hw, HST⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    wp_auto
    rw [_root_.decide_eq_false (show ¬ sint.Z curRev < sint.Z st.minRev by omega)]
    wp_auto
    rw [_root_.decide_eq_false (show ¬ sint.Z st.minRev < sint.Z compactRev by omega)]
    wp_auto
    have Hstep : mvcc.minRevL ST (keys.take (i + 1).toNat) =
        min (mvcc.minRevL ST (keys.take i.toNat)) (sint.Z st.minRev) := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
      simp only [Option.toList_some]
      rw [mvcc.minRevL_snoc]; unfold mvcc.minRevStep; rw [hst]
    wp_if_destruct
    · (try wp_auto)
      ihave HST := HST $$ [Hmin Hvic Hcomp Hres Hch]
      · iunfold mvcc.watcherOwn; iframe
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iunfold mvcc.ownStates
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Hstep]; omega
    · (try wp_auto)
      ihave HST := HST $$ [Hmin Hvic Hcomp Hres Hch]
      · iunfold mvcc.watcherOwn; iframe
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iunfold mvcc.ownStates
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Hstep]; omega
  iintro HP Hws
  iNamed HP
  wp_auto
  iapply HΦ
  iframe HST
  isplitl [Hwg Hws Hback]
  · iapply Hback $$ Hwg
    iunfold mvcc.ownWatcherSet; iexact Hws
  ipureintro
  rw [Hi.2, show (((GMap.size (domSet W)) : Int)).toNat = keys.length by omega, List.take_length]
  exact mvcc.minRevL_eq ST _ keys Hknodup Hkset

end proof

end EtcdGrove
end Perennial
