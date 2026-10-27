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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  -- the states after the first `i` keys: those members' restore flags cleared if above `curRev`
  -- (D22 receiver epochs, S6)
  let STi : List Loc → Nat → GMap Loc mvcc.WatcherSt := fun keys n =>
    mvcc.gmapMapK (fun w st => if w ∈ keys.take n then mvcc.rstClear curRev st else st) ST
  have hSTi : ∀ keys n w, STi keys n !! w =
      (ST !! w).map (fun st => if w ∈ keys.take n then mvcc.rstClear curRev st else st) :=
    fun _ _ _ => rfl
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (m : w64) (wv : Loc),
      "minRev" ∷ minRev_ptr ↦ m ∗ "w" ∷ w_ptr ↦ wv ∗ "HST" ∷ mvcc.ownStates (STi keys i.toNat) ∗
      "curRev" ∷ curRev_ptr ↦ curRev ∗ "compactRev" ∷ compactRev_ptr ↦ compactRev ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ sint.Z m = mvcc.minRevL ST (keys.take i.toNat)⌝)) $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [minRev w HST curRev compactRev]
  · iexists _, _
    simp only [named]
    iframe
    isplitl [HST]
    · have h0 : STi keys (0 : Int).toNat = ST := by
        refine GMap.ext (fun k => ?_)
        show STi keys 0 !! k = ST !! k
        rw [hSTi]; cases ST !! k <;> simp
      rw [h0]; iexact HST
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
    obtain ⟨hc1, hc2⟩ := Hst key st hst
    have hnot := not_mem_take_of_nodup Hknodup Hkey
    have hsti : STi keys i.toNat !! key = some st := by
      rw [hSTi, hst]; simp [hnot]
    have hstep : Iris.Std.PartialMap.insert (STi keys i.toNat) key (mvcc.rstClear curRev st) =
        STi keys (i + 1).toNat := by
      refine GMap.ext (fun k => ?_)
      show (<[key := mvcc.rstClear curRev st]> (STi keys i.toNat)) !! k = STi keys (i + 1).toNat !! k
      have htk : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      rw [hSTi, htk]
      by_cases hk : key = k
      · subst hk; rw [GMap.lookup_insert, hst]; simp
      · rw [GMap.lookup_insert_ne _ _ hk, hSTi]
        have : (k ∈ keys.take i.toNat ++ [key]) ↔ k ∈ keys.take i.toNat := by
          simp [Ne.symm hk]
        simp only [this]
    iunfold mvcc.ownStates at HST
    icases (BigSepM.bigSepM_insert_acc (show Iris.Std.PartialMap.get? (STi keys i.toNat) key = some st
      from hsti)) $$ HST with ⟨Hw, HST⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    wp_auto
    by_cases hgt : sint.Z curRev < sint.Z st.minRev
    · -- above `curRev`: restoring (`watchableStore.Restore`), the flag cleared
      have hres : st.restore = true := by
        rcases hc2 with h | h
        · omega
        · exact h
      rw [_root_.decide_eq_true hgt]
      wp_auto
      rw [hres]
      wp_auto
      have hrc : mvcc.rstClear curRev st = { st with restore := false } := by
        unfold mvcc.rstClear; rw [ite_eq_left hgt]
      rw [_root_.decide_eq_false (show ¬ sint.Z st.minRev < sint.Z compactRev by omega)]
      wp_auto
      have Hstep : mvcc.minRevL ST (keys.take (i + 1).toNat) =
          min (mvcc.minRevL ST (keys.take i.toNat)) (sint.Z st.minRev) := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
        simp only [Option.toList_some]
        rw [mvcc.minRevL_snoc]; unfold mvcc.minRevStep; rw [hst]
      wp_if_destruct
      · (try wp_auto)
        ihave HST := HST $$ %(mvcc.rstClear curRev st) [Hmin Hvic Hcomp Hres Hch]
        · rw [hrc]; iunfold mvcc.watcherOwn; iframe
        rw [hstep]
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
        ihave HST := HST $$ %(mvcc.rstClear curRev st) [Hmin Hvic Hcomp Hres Hch]
        · rw [hrc]; iunfold mvcc.watcherOwn; iframe
        rw [hstep]
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
    rw [_root_.decide_eq_false hgt]
    have hrc : mvcc.rstClear curRev st = st := by unfold mvcc.rstClear; rw [ite_eq_right hgt]
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
      ihave HST := HST $$ %(mvcc.rstClear curRev st) [Hmin Hvic Hcomp Hres Hch]
      · rw [hrc]; iunfold mvcc.watcherOwn; iframe
      rw [hstep]
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
      ihave HST := HST $$ %(mvcc.rstClear curRev st) [Hmin Hvic Hcomp Hres Hch]
      · rw [hrc]; iunfold mvcc.watcherOwn; iframe
      rw [hstep]
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
  have hfin : STi keys (GMap.size (domSet W) : Int).toNat = mvcc.chooseRst curRev (domSet W) ST := by
    refine GMap.ext (fun k => ?_)
    show STi keys _ !! k = mvcc.chooseRst curRev (domSet W) ST !! k
    rw [hSTi, show (((GMap.size (domSet W)) : Int)).toNat = keys.length by omega, List.take_length]
    unfold mvcc.chooseRst; rw [mvcc.gmapMapK_lookup]
    cases ST !! k with
    | none => rfl
    | some st =>
      simp only [Option.map_some]
      by_cases hk : k ∈ keys
      · rw [if_pos hk, if_pos ((Hkset k).1 hk)]
      · rw [if_neg hk, if_neg (fun h => hk ((Hkset k).2 h))]
  rw [hfin]
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
