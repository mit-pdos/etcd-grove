/-
Proof of `Spec/.../mvcc/watcherGroup__chooseAll.lean`. Lean-first (no Rocq counterpart). Since
2026-11-01 (watches across a compaction) the loop sends a member behind `compactRev` its
compaction response (`cmp_send_inner`) and deletes it from the group on a send: the loop runs over
the group's set as it shrinks (`wp_map_for_range_gen`; Go's range skips keys deleted during it), the
invariant carrying the group's rest at the current members.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__chooseAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__delete

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

namespace mvcc

/-- The group at `ws`, its struct lent (to read its fields). -/
theorem ownWatcherGroupAt_struct (wg : Loc) (W : GMap Loc WatchRange) (ws : GoMap) :
    ownWatcherGroupAt (GF := GF) wg W ws ⊢
      ∃ v : watcherGroup, wg ↦ v ∗ ⌜v.watchers' = ws⌝ ∗ (wg ↦ v -∗ ownWatcherGroupAt wg W ws) := by
  iintro H
  unfold ownWatcherGroupAt
  icases H with ⟨%km, %t, %KM, %L, H⟩
  iNamed H
  iexists _
  iframe Hwg
  isplitr
  · ipureintro; rfl
  iintro Hwg
  iexists km, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact HL

/-- The members not yet compacted (not in `cm`). -/
def wNotCm (W : GMap Loc WatchRange) (cm : List Loc) : GMap Loc WatchRange :=
  Iris.Std.PartialMap.filter (fun w _ => !(regMap cm !! w).isSome) W

/-- The states after the first `n` keys, with `cm` compacted. -/
def stAfter (curRev : w64) (ST : GMap Loc WatcherSt) (keys : List Loc) (n : Nat) (cm : List Loc) :
    GMap Loc WatcherSt :=
  chooseCmp (regMap cm)
    (gmapMapK (fun w st => if w ∈ keys.take n then rstClear curRev st else st) ST)

end mvcc

theorem mvcc.watcherGroup.chooseAll.wp_proof (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.chooseAll.spec (GF := GF) (hG := hG) := by
  intro γ ql wg W ST curRev compactRev
  wp_start as ⟨Hg, HST, Hsp, %Hdom, %Hst⟩
  icases (mvcc.ownWatcherGroup_at wg W 1).1 $$ Hg with ⟨%ws, Hg⟩
  icases mvcc.ownWatcherGroupAt_struct wg W ws $$ Hg with ⟨%v, Hwg, %Hv, Hgb⟩
  wp_auto
  ihave Hg := Hgb $$ Hwg
  icases mvcc.ownWatcherGroupAt_set wg W ws 1 $$ Hg with ⟨Hws, Hrest⟩
  iunfold mvcc.ownWatcherSet at Hws
  rw [Hv]
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  have hW0 : mvcc.wNotCm W [] = W := by
    refine GMap.ext (fun k => ?_)
    unfold mvcc.wNotCm
    show Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter _ W) k = _
    rw [Iris.Std.LawfulPartialMap.get?_filter]
    show (W !! k).bind _ = W !! k
    cases W !! k <;> simp [mvcc.regMap]
  have hST0 : ∀ keys, mvcc.stAfter curRev ST keys 0 [] = ST := by
    intro keys
    refine GMap.ext (fun k => ?_)
    unfold mvcc.stAfter mvcc.chooseCmp
    rw [mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup]
    cases ST !! k <;> simp [mvcc.regMap]
  iapply wp_map_for_range_gen (fun (keys : List Loc) (i : Nat) (m' : GMap Loc Unit) =>
      iprop(∃ (cm : List Loc) (mr : w64) (wv : Loc),
        "minRev" ∷ minRev_ptr ↦ mr ∗ "w" ∷ w_ptr ↦ wv ∗
        "curRev" ∷ curRev_ptr ↦ curRev ∗ "compactRev" ∷ compactRev_ptr ↦ compactRev ∗
        "wgp" ∷ wg_ptr ↦ wg ∗
        "HST" ∷ mvcc.ownStates (mvcc.stAfter curRev ST keys i cm) ∗
        "Hrest" ∷ (mvcc.ownWatcherSet ws (domSet (mvcc.wNotCm W cm)) -∗
          mvcc.ownWatcherGroupAt wg (mvcc.wNotCm W cm) ws) ∗
        "Hsp" ∷ ([∗map] w ↦ st ∈ ST, if decide (sint.Z st.minRev < sint.Z compactRev) then
          mvcc.cmpSendPre γ w st.ch ql else iprop(True)) ∗
        "%Hi" ∷ ⌜(∀ w ∈ cm, w ∈ keys.take i ∧
            ∃ st, ST !! w = some st ∧ sint.Z st.minRev < sint.Z compactRev) ∧ cm.Nodup ∧
          m' = domSet (mvcc.wNotCm W cm) ∧
          sint.Z mr = mvcc.minRevL ST ((keys.take i).filter (mvcc.notBehind ST compactRev))⌝))
    $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [minRev w HST curRev compactRev wg Hrest Hsp]
  · iexists [], _, _
    simp only [named]
    iframe
    rw [hST0 keys, hW0]
    iframe
    ipureintro
    refine ⟨fun w h => by simp at h, List.nodup_nil, rfl, by simp [mvcc.minRevL]; decide⟩
  isplitr
  · -- a key of the set, still in it
    imodintro
    iintro %i %key %u %m' ⟨%Hkey, %Hu⟩ HP Hws
    iNamed HP
    obtain ⟨hcm, hcmnd, hm', hmr⟩ := Hi
    subst hm'
    have hnot := not_mem_take_of_nodup Hknodup Hkey
    have hk : key ∈ keys := List.mem_of_getElem? Hkey
    have hW : (W !! key).isSome := by
      have := (Hkset key).1 hk
      rw [GMap.domSet, GMap.lookup_fmap] at this; cases h : W !! key <;> simp_all
    have hncm : key ∉ cm := fun h => hnot (hcm key h).1
    obtain ⟨st, hst⟩ : ∃ st, ST !! key = some st := Option.isSome_iff_exists.1 (Hdom key hW)
    obtain ⟨hc0, hc2⟩ := Hst key st hst
    have hregk : (mvcc.regMap cm !! key).isSome = false := by
      cases h : (mvcc.regMap cm !! key).isSome
      · rfl
      · exact absurd ((mvcc.regMap_lookup cm key).1 h) hncm
    have hsti : mvcc.stAfter curRev ST keys i cm !! key = some st := by
      unfold mvcc.stAfter mvcc.chooseCmp
      rw [mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, hst]
      simp [hnot, hregk]
    -- the state after the key's step: its restore flag cleared, maybe compacted
    have htk : keys.take (i + 1) = keys.take i ++ [key] := by
      rw [List.take_add_one, Hkey]; rfl
    have hstep : ∀ (cm' : List Loc) (st' : mvcc.WatcherSt),
        (∀ w, w ≠ key → ((mvcc.regMap cm' !! w).isSome ↔ (mvcc.regMap cm !! w).isSome)) →
        st' = (if (mvcc.regMap cm' !! key).isSome then
          { mvcc.rstClear curRev st with compacted := true } else mvcc.rstClear curRev st) →
        Iris.Std.PartialMap.insert (mvcc.stAfter curRev ST keys i cm) key st' =
          mvcc.stAfter curRev ST keys (i + 1) cm' := by
      intro cm' st' hcm' hst'
      refine GMap.ext (fun k => ?_)
      show (<[key := st']> (mvcc.stAfter curRev ST keys i cm)) !! k = _
      by_cases hkk : key = k
      · subst hkk
        rw [GMap.lookup_insert]
        unfold mvcc.stAfter mvcc.chooseCmp
        rw [mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, hst, htk, hst']
        simp
      · rw [GMap.lookup_insert_ne _ _ hkk]
        unfold mvcc.stAfter mvcc.chooseCmp
        rw [mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup,
          htk]
        have h1 : (k ∈ keys.take i ++ [key]) ↔ k ∈ keys.take i := by simp [Ne.symm hkk]
        have h2 := hcm' k (Ne.symm hkk)
        cases ST !! k with
        | none => rfl
        | some st0 =>
          simp only [Option.map_some, h1]
          by_cases hr : (mvcc.regMap cm !! k).isSome
          · rw [ite_eq_left hr, ite_eq_left (h2.2 hr)]
          · rw [ite_eq_right hr, ite_eq_right (fun h => hr (h2.1 h))]
    iunfold mvcc.ownStates at HST
    icases (BigSepM.bigSepM_insert_acc (show Iris.Std.PartialMap.get? (mvcc.stAfter curRev ST keys i cm) key = some st
      from hsti)) $$ HST with ⟨Hw, HST⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    wp_auto
    -- the restore step: `st1`, the state with the restore flag cleared if above `curRev`
    obtain ⟨st1, hst1, hm1, hch1, hv1, hcp1⟩ : ∃ st1, mvcc.rstClear curRev st = st1 ∧
        st1.minRev = st.minRev ∧ st1.ch = st.ch ∧ st1.victim = st.victim ∧
        st1.compacted = st.compacted :=
      ⟨_, rfl, by simp, by unfold mvcc.rstClear; split <;> rfl, by unfold mvcc.rstClear; split <;> rfl,
        by unfold mvcc.rstClear; split <;> rfl⟩
    by_cases hgt : sint.Z curRev < sint.Z st.minRev
    all_goals first
      | (have hres : st.restore = true := by
            rcases hc2 with h | h
            · omega
            · exact h
         rw [_root_.decide_eq_true hgt]
         wp_auto
         rw [hres]
         wp_auto
         have hr1 : st1.restore = false := by
           rw [← hst1]; unfold mvcc.rstClear; rw [ite_eq_left hgt]
         irevert Hres; rw [← hr1]; iintro Hres)
      | (rw [_root_.decide_eq_false hgt]
         wp_auto
         have hr1 : st1.restore = st.restore := by
           rw [← hst1]; unfold mvcc.rstClear; rw [ite_eq_right hgt]
         irevert Hres; rw [← hr1]; iintro Hres)
    all_goals
      have hnb : mvcc.notBehind ST compactRev key = decide (sint.Z compactRev ≤ sint.Z st.minRev) := by
        unfold mvcc.notBehind; rw [hst]
      by_cases hlt : sint.Z st.minRev < sint.Z compactRev
      · -- behind the compaction revision: the compaction response, sent without blocking
        have hcr0 : compactRev ≠ W64 0 := by
          intro h; rw [h] at hlt; have : sint.Z (W64 0 : w64) = 0 := rfl; omega
        have hnbf : mvcc.notBehind ST compactRev key = false := by rw [hnb]; simp; omega
        have Hstep : (keys.take (i + 1)).filter (mvcc.notBehind ST compactRev) =
            (keys.take i).filter (mvcc.notBehind ST compactRev) := by
          rw [htk, List.filter_append]
          simp only [List.filter_cons, hnbf, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
            List.append_nil]
        rw [_root_.decide_eq_true hlt]
        icases (BigSepM.bigSepM_lookup_acc (show Iris.Std.PartialMap.get? ST key = some st from hst))
          $$ Hsp with ⟨Hcs, Hspb⟩
        simp only [_root_.decide_eq_true hlt, ↓reduceIte]
        iunfold mvcc.cmpSendPre at Hcs
        icases Hcs with ⟨%γw, %r, %fcs, #Hmeta, #Hfix, #Hfok, #Hwc, Hlive⟩
        ihave #Hfix' := Hfix
        iunfold mvcc.watcherFixed at Hfix'
        icases Hfix' with ⟨-, %ks, %es, -, -, -, -, -, #Hid, -⟩
        ihave #Hwc' := Hwc
        iunfold mvcc.watcherChan at Hwc'
        icases Hwc' with ⟨#Hisch, -, -⟩
        wp_auto
        -- the members after the send: `key` compacted too
        have hdel : GMap.delete key (mvcc.wNotCm W cm) = mvcc.wNotCm W (cm ++ [key]) := by
          refine GMap.ext (fun k => ?_)
          unfold mvcc.wNotCm
          by_cases hkk : key = k
          · subst hkk
            rw [GMap.lookup_delete]
            show none = Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter _ W) key
            rw [Iris.Std.LawfulPartialMap.get?_filter]
            have : (mvcc.regMap (cm ++ [key]) !! key).isSome = true :=
              (mvcc.regMap_lookup _ _).2 (List.mem_append_right _ (List.mem_singleton_self _))
            show none = (W !! key).bind _
            cases W !! key <;> simp [this]
          · rw [GMap.lookup_delete_ne _ hkk]
            show Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter _ W) k =
              Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter _ W) k
            rw [Iris.Std.LawfulPartialMap.get?_filter, Iris.Std.LawfulPartialMap.get?_filter]
            have : (mvcc.regMap (cm ++ [key]) !! k).isSome = (mvcc.regMap cm !! k).isSome := by
              apply Bool.eq_iff_iff.2
              rw [mvcc.regMap_lookup, mvcc.regMap_lookup]
              simp [Ne.symm hkk]
            show (W !! k).bind _ = (W !! k).bind _
            cases W !! k <;> simp [this]
        have hcm' : ∀ w, w ≠ key →
            ((mvcc.regMap (cm ++ [key]) !! w).isSome ↔ (mvcc.regMap cm !! w).isSome) := by
          intro w hw; rw [mvcc.regMap_lookup, mvcc.regMap_lookup]; simp [hw]
        have hkreg : (mvcc.regMap (cm ++ [key]) !! key).isSome = true :=
          (mvcc.regMap_lookup _ _).2 (List.mem_append_right _ (List.mem_singleton_self _))
        wp_bind (App (Val (GoInstruction SelectStmt)) _)
        iapply chan.wp_select_nonblocking
        isplit
        · iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.nonblockingClausePre]
            iexists WatchResponse, inferInstance, inferInstance, inferInstance, inferInstance, st.ch, γw.wc.ch, ({ WatchID' := r.id, Events' := slice.nil, Revision' := 0, CompactRevision' := compactRev } : WatchResponse)
            isplit
            · ipureintro; exact ⟨rfl, rfl⟩
            isplit
            · iexact Hisch
            unfold nonblockingSendAu
            isplit
            · iapply (mvcc.cmp_send_inner γ key γw r fcs st.ch ql _ compactRev ⟨rfl, rfl, rfl, rfl⟩
                hcr0)
              iframe Hmeta Hfix Hwc Hlive
              isplitr
              · iexact Hfok
              iintro Hlive
              wp_auto
              ihave Hcs : mvcc.cmpSendPre γ key st.ch ql $$ [Hlive]
              · iunfold mvcc.cmpSendPre; iexists γw, r, fcs; iframe #; iframe Hlive
              ihave Hsp := Hspb $$ Hcs
              ihave Hg := Hrest $$ [Hws]
              · iunfold mvcc.ownWatcherSet; iexact Hws
              wp_apply hDel wg (mvcc.wNotCm W cm) ws key r fcs $$ [$Hg] as Hg
              · iframe #
              irevert Hg; rw [hdel]; iintro Hg
              icases mvcc.ownWatcherGroupAt_set wg _ ws 1 $$ Hg with ⟨Hws, Hrest⟩
              (try wp_auto)
              ihave HST := HST $$ %({ st1 with compacted := true } : mvcc.WatcherSt) [Hmin Hvic Hcomp Hres Hch]
              · iunfold mvcc.watcherOwn; simp only; rw [hm1, hch1, hv1]; iframe
              rw [hstep (cm ++ [key]) _ hcm' (by simp [hkreg, hst1])]
              unfold forMapPostcondition
              ileft
              isplitr
              · ipureintro; rfl
              iexists _
              isplitl [Hws]
              · iunfold mvcc.ownWatcherSet at Hws; iexact Hws
              iexists cm ++ [key], _, _
              simp only [named]
              iunfold mvcc.ownStates
              iframe
              ipureintro
              refine ⟨fun w hw => ?_, List.nodup_append.2 ⟨hcmnd, List.pairwise_singleton _ _,
                fun a ha b hb => by simp at hb; subst hb; intro h; subst h; exact hncm ha⟩,
                by first | rfl | trivial, by rw [Hstep]; exact hmr⟩
              rcases List.mem_append.1 hw with h | h
              · exact ⟨by rw [htk]; exact List.mem_append_left _ (hcm w h).1, (hcm w h).2⟩
              · simp at h; subst h
                exact ⟨by rw [htk]; exact List.mem_append_right _ (List.mem_singleton_self _),
                  st, hst, hlt⟩
            · itrivial
          · iapply BigAndL.bigAndL_nil.2; itrivial
        · -- the channel full: the member stays, retried by the next sync
          wp_auto
          ihave Hcs : mvcc.cmpSendPre γ key st.ch ql $$ [Hlive]
          · iunfold mvcc.cmpSendPre; iexists γw, r, fcs; iframe #; iframe Hlive
          ihave Hsp := Hspb $$ Hcs
          ihave HST := HST $$ %st1 [Hmin Hvic Hcomp Hres Hch]
          · iunfold mvcc.watcherOwn; rw [hm1, hch1, hv1, hcp1]; iframe
          rw [hstep cm st1 (fun _ _ => Iff.rfl) (by simp [hregk, hst1])]
          unfold forMapPostcondition
          ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hws
          iexists cm, _, _
          simp only [named]
          iunfold mvcc.ownStates
          iframe
          ipureintro
          refine ⟨fun w hw => ⟨by rw [htk]; exact List.mem_append_left _ (hcm w hw).1, (hcm w hw).2⟩,
            hcmnd, by first | rfl | trivial, by rw [Hstep]; exact hmr⟩
      rw [_root_.decide_eq_false hlt]
      wp_auto
      have Hstep : mvcc.minRevL ST ((keys.take (i + 1)).filter (mvcc.notBehind ST compactRev)) =
          min (mvcc.minRevL ST ((keys.take i).filter (mvcc.notBehind ST compactRev))) (sint.Z st.minRev) := by
        rw [htk, List.filter_append]
        have : mvcc.notBehind ST compactRev key = true := by rw [hnb]; simp; omega
        simp only [List.filter_cons, this, ↓reduceIte, List.filter_nil]
        rw [mvcc.minRevL_snoc]; unfold mvcc.minRevStep; rw [hst]
      wp_if_destruct
      all_goals
        (try wp_auto)
        ihave HST := HST $$ %st1 [Hmin Hvic Hcomp Hres Hch]
        · iunfold mvcc.watcherOwn; rw [hm1, hch1, hv1, hcp1]; iframe
        rw [hstep cm st1 (fun _ _ => Iff.rfl) (by simp [hregk, hst1])]
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hws
        iexists cm, _, _
        simp only [named]
        iunfold mvcc.ownStates
        iframe
        ipureintro
        refine ⟨fun w hw => ⟨by rw [htk]; exact List.mem_append_left _ (hcm w hw).1, (hcm w hw).2⟩,
          hcmnd, by first | rfl | trivial, ?_⟩
        rw [Hstep]; omega
  isplitr
  · -- a key no longer in the set: impossible (only the current key is deleted)
    imodintro
    iintro %i %key %m' ⟨%Hkey, %Hnone⟩ HP
    iNamed HP
    exfalso
    obtain ⟨hcm, -, hm', -⟩ := Hi
    subst hm'
    have hnot := not_mem_take_of_nodup Hknodup Hkey
    have hk : key ∈ keys := List.mem_of_getElem? Hkey
    have hW : (W !! key).isSome := by
      have := (Hkset key).1 hk
      rw [GMap.domSet, GMap.lookup_fmap] at this; cases h : W !! key <;> simp_all
    have hncm : key ∉ cm := fun h => hnot (hcm key h).1
    rw [GMap.domSet, GMap.lookup_fmap] at Hnone
    unfold mvcc.wNotCm at Hnone
    have : (Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter
        (fun w _ => !(mvcc.regMap cm !! w).isSome) W) key) = none := by
      cases h : (Iris.Std.PartialMap.filter (fun w _ => !(mvcc.regMap cm !! w).isSome) W : GMap Loc _) !! key
      · exact h
      · rw [h] at Hnone; cases Hnone
    rw [Iris.Std.LawfulPartialMap.get?_filter] at this
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    have hr' : Iris.Std.PartialMap.get? (M := GMap Loc) W key = some r := hr
    rw [hr'] at this
    have hreg : (mvcc.regMap cm !! key).isSome = false := by
      cases h : (mvcc.regMap cm !! key).isSome
      · rfl
      · exact absurd ((mvcc.regMap_lookup cm key).1 h) hncm
    simp [hreg] at this
  · -- the loop's end
    iintro %m' HP Hws
    iNamed HP
    obtain ⟨hcm, hcmnd, hm', hmr⟩ := Hi
    subst hm'
    ihave Hg := Hrest $$ [Hws]
    · iunfold mvcc.ownWatcherSet; iexact Hws
    wp_auto
    iapply HΦ
    iexists mvcc.regMap cm
    have htk : keys.take keys.length = keys := List.take_length
    rw [htk] at hmr hcm
    have hkW : ∀ w, w ∈ keys ↔ (W !! w).isSome := by
      intro w; rw [Hkset w, GMap.domSet, GMap.lookup_fmap]; cases W !! w <;> simp
    isplitr
    · ipureintro
      intro w hw
      obtain ⟨hk, st, hs, hlt⟩ := hcm w ((mvcc.regMap_lookup cm w).1 hw)
      exact ⟨(hkW w).1 hk, st, hs, hlt⟩
    isplitl [Hg]
    · iapply (mvcc.ownWatcherGroup_at wg _ 1).2
      iexists ws; iunfold mvcc.wNotCm at Hg; iexact Hg
    isplitl [HST]
    · have hfin : mvcc.stAfter curRev ST keys keys.length cm =
          mvcc.chooseCmp (mvcc.regMap cm) (mvcc.chooseRst curRev (domSet W) ST) := by
        refine GMap.ext (fun k => ?_)
        unfold mvcc.stAfter mvcc.chooseCmp mvcc.chooseRst
        rw [mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, mvcc.gmapMapK_lookup, htk]
        cases ST !! k with
        | none => rfl
        | some st =>
          simp only [Option.map_some]
          have : (k ∈ keys) = ((domSet W !! k).isSome = true) := propext (Hkset k)
          simp only [this]
      rw [hfin]; iexact HST
    iframe Hsp
    ipureintro
    rw [hmr]
    apply mvcc.minRevL_eq ST _ _ (List.Pairwise.filter _ Hknodup)
    intro w
    rw [List.mem_filter, Hkset w]
    show _ ↔ (Iris.Std.PartialMap.get? (M := GMap Loc) (Iris.Std.PartialMap.filter _ (domSet W)) w).isSome
    rw [Iris.Std.LawfulPartialMap.get?_filter]
    show _ ↔ ((domSet W !! w).bind _).isSome
    cases domSet W !! w <;> simp

end proof

end EtcdGrove
end Perennial
