/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__ApplySimpleConfChange`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ApplySimpleConfChange
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__IsJointConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__applyConfigUpdate
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Union
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Has

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

set_option hygiene false in
/-- After the leader branch: the members of entry `k`'s configuration, `t.mut(i)`, the loop dropping the
progress outside them, the result (`Ht : stateOwn tq S M`, `Hev` the Lean's successor over `S`). -/
local macro "asc_tail" S:term "," M:term : tactic => `(tactic| (
  -- the members of entry `k`'s configuration
  have hK1 : sint.Z (mv - W64 1) = (K : Int) - 1 := by rw [← hkK]; word
  have hiK : 0 ≤ sint.Z (mv - W64 1) ∧ sint.Z (mv - W64 1) < sint.Z gs.Log'.len := by
    rw [hK1, hlen]; constructor <;> omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hiK)]
  have hnK : (sint.Z (mv - W64 1)).toNat < es.length := by rw [Hell, hK1]; omega
  obtain ⟨xe, Hxe⟩ : ∃ x, es[(sint.Z (mv - W64 1)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hnK⟩
  obtain ⟨ye, Hye⟩ : ∃ y, (st.s (uint.nat i)).log[(sint.Z (mv - W64 1)).toNat]? = some y :=
    ⟨_, List.getElem?_eq_getElem (Hell ▸ hnK)⟩
  have hKi : (sint.Z (mv - W64 1)).toNat = K - 1 := by rw [hK1]; omega
  rw [hKi] at Hye
  ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hxe (hKi ▸ Hye) $$ Hel
  iunfold entryRO at Hxy
  icases Hxy with ⟨-, #Hval⟩
  icases ownSlice_elem_acc _ xe _ _ es hiK.1 Hxe $$ Hes with ⟨#Hxe', -⟩
  icases typedPointsto_split _ _ _ $$ Hxe' with Hxef
  simp only [TypedPointsto.typedPointstoDef]
  icases Hxef with ⟨-, -, #E3, -⟩
  icases typedPointsto_split _ _ _ $$ E3 with E3f
  simp only [TypedPointsto.typedPointstoDef]
  icases E3f with ⟨-, -, #W3, #W4, -⟩
  obtain ⟨nc, ln, hncl⟩ : ∃ nc ln, (match ye.value with | .conf nc ln => (nc, ln) | _ => ([], [])) = (nc, ln) :=
    ⟨_, _, rfl⟩
  ihave #Hcfg : iprop(setRO (GF := GF) xe.Value'.NewConf' nc ∗ setRO xe.Value'.Learners' ln) $$ [Hval]
  · cases hv : ye.value with
    | val n =>
      simp only [hv, Prod.mk.injEq] at hncl
      obtain ⟨rfl, rfl⟩ := hncl
      iunfold valueRO at Hval
      icases Hval with ⟨-, #H1, #H2⟩
      iframe H1 H2
    | emptySeq =>
      simp only [hv, Prod.mk.injEq] at hncl
      obtain ⟨rfl, rfl⟩ := hncl
      iunfold valueRO at Hval
      icases Hval with ⟨-, #H1, #H2⟩
      iframe H1 H2
    | conf a b =>
      simp only [hv, Prod.mk.injEq] at hncl
      obtain ⟨rfl, rfl⟩ := hncl
      iunfold valueRO at Hval
      icases Hval with ⟨-, #H1, #H2⟩
      iframe H1 H2
  icases Hcfg with ⟨#Hnc, #Hln⟩
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true hiK)]
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Union_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Union _ nc _ ln $$ [Hnc Hln] as %u #Hu
  · iframe Hnc Hln
  try wp_auto
  obtain ⟨stA, hstA⟩ : ∃ s, s = $S := ⟨_, rfl⟩
  rw [← hstA]
  rw [← hstA] at Hev
  have Hi : uint.nat i ∈ stA.server := by rw [hstA]; exact Hi
  mut_open tq, stA, $M, i, Ht
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut_keys (fun (keys : List w64) (n : Nat) (m' : GMap w64 w64) =>
      iprop(∃ jv : w64, "j" ∷ j_ptr ↦ jv ∗ "w" ∷ w_ptr ↦ cp ∗ "members" ∷ members_ptr ↦ u ∗
        "MatchIndex" ∷ structFieldRef github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server
          go!"MatchIndex" cp ↦ gc.MatchIndex' ∗
        "%Hm'" ∷ ⌜∀ x, m' !! x = if x ∈ keys.take n ∧ uint.nat x ∉ nc.union ln then none else mc !! x⌝)) $$ Hcm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [j w members MatchIndex]
  · iexists _
    iframe
    ipureintro; intro x; simp
  isplitr
  · imodintro
    iintro %n %key %v0 %m' ⟨%Hkey, %Hv, %Hagree⟩ HP Hmap
    iNamed HP
    have Hnot : key ∉ keys.take n := by
      intro hm
      obtain ⟨j0, hj, e⟩ := List.mem_iff_getElem.1 hm
      simp only [List.length_take, List.getElem_take] at hj e
      have := list_nodup_getElem?_inj keys Hknodup j0 n key
        (by rw [List.getElem?_eq_getElem (by omega), e]) Hkey
      omega
    have Htake : keys.take (n + 1) = keys.take n ++ [key] := by
      rw [List.take_add_one, Hkey]; rfl
    have hmk : m' !! key = mc !! key := by rw [Hm' key]; simp [Hnot]
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Has_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Has u (nc.union ln) key $$ [Hu]
    · iexact Hu
    by_cases hmem : uint.nat key ∈ nc.union ln
    · rw [decide_eq_true hmem]
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists m'
      iframe Hmap
      isplitl
      · iexists _
        iframe
        ipureintro
        intro x
        rw [Hm' x, Htake]
        by_cases hx : x = key
        · subst hx; simp [hmem, Hnot]
        · simp [hx]
      · ipureintro
        intro k _; rfl
    · rw [decide_eq_false hmem]
      try wp_auto
      wp_apply wp_mapDelete $$ [Hmap] as Hmap
      · iexact Hmap
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists (GMap.delete key m')
      iframe Hmap
      isplitl
      · iexists _
        iframe
        ipureintro
        intro x
        rw [Htake]
        by_cases hx : x = key
        · subst hx; rw [GMap.lookup_delete]; simp [hmem]
        · rw [GMap.lookup_delete_ne _ (Ne.symm hx), Hm' x]; simp [hx]
      · ipureintro
        intro k hk
        exact GMap.lookup_delete_ne _ (Ne.symm hk)
  iintro %m' HP Hmap
  iNamed HP
  rw [List.take_length] at Hm'
  have Hcmi'' : ∀ x : w64, sint.Z ((m' !! x).getD (W64 0)) =
      (if (nc.union ln).contains (uint.nat x) then sint.Z ((mc !! x).getD (W64 0)) else 0) := by
    intro x
    rw [Hm' x]
    by_cases hx : x ∈ keys
    · by_cases hmx : uint.nat x ∈ nc.union ln
      · simp [hx, hmx]
      · simp [hx, hmx]
    · have hnone : mc !! x = none := by
        cases h : mc !! x with
        | none => rfl
        | some _ => exact absurd ((Hkset x).2 (by simp [h])) hx
      simp [hx, hnone]
  have Hcmi' : ∀ x : w64, sint.Z ((m' !! x).getD (W64 0)) =
      (if (nc.union ln).contains (uint.nat x) then
        (stA.s (uint.nat i)).matchIndex (uint.nat x) else 0) := by
    intro x; rw [Hcmi'' x, Hcmi x]
  ihave Hcp : cp ↦ (gc : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex VotesResponded
      VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hc := serverOwn_intro cp gc m'
      ((fun w : Server => { w with matchIndex := fun j => if (nc.union ln).contains j then w.matchIndex j else 0 })
        (stA.s (uint.nat i))) Hcf Hcmi' $$ [Hcp Hmap]
  · iframe Hcp Hmap Hcl Hcr Hcg Hcc Hcd
  ihave Hs := stateOwnHole_close_upd _ _ _ _ _
      (fun w : Server => { w with matchIndex := fun j => if (nc.union ln).contains j then w.matchIndex j else 0 })
      Hi $$ [Hh Hc]
  · iframe
  imod stateOwn_persist $$ Hs with #Hs
  try wp_auto
  rw [Hye] at Hev
  simp only [Option.map_some] at Hev
  have Ho : o = some (stA.upd (uint.nat i)
      (fun w : Server => { w with matchIndex := fun j => if (nc.union ln).contains j then w.matchIndex j else 0 })) := by
    rw [← Except.ok.inj Hev]
    congr 1
    obtain ⟨yv, hv⟩ : ∃ yv, ye.value = yv := ⟨_, rfl⟩
    cases yv <;> simp only [hv, Prod.mk.injEq] at hncl <;> obtain ⟨rfl, rfl⟩ := hncl <;> simp only [hv] <;> rfl
  subst Ho
  iapply HΦ
  iexact Hs))

theorem State.ApplySimpleConfChange.wp_proof (wp_IsJointConfig : State.IsJointConfig.spec (GF := GF) (hG := hG))
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_applyConfigUpdate : State.applyConfigUpdate.spec (GF := GF) (hG := hG))
    (wp_Union : Set.Union.spec (GF := GF) (hG := hG))
    (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    State.ApplySimpleConfChange.spec (GF := GF) (hG := hG) := by
  intro p st i o
  wp_start as ⟨#Hst, %Hi, %Hlog, %Hrc0, %Hev⟩
  wp_auto
  wp_apply wp_IsJointConfig p st i $$ [Hst]
  · iframe Hst; ipureintro; exact Hi
  cases hj : st.isJointConfig (uint.nat i)
  rotate_left
  · wp_auto
    have : o = none := by
      unfold State.applySimpleConfChange at Hev
      simp [hj, Pure.pure, Except.pure] at Hev; exact Hev.symm
    subst this
    iapply HΦ; ipureintro; rfl
  read_server
  wp_auto
  lookup_server
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hci : (st.s (uint.nat i)).commitIndex ≤ (st.s (uint.nat i)).log.length := by
    by_cases h : (st.s (uint.nat i)).commitIndex > (st.s (uint.nat i)).log.length
    · unfold State.applySimpleConfChange at Hev
      simp [hj, h, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at Hev
    · omega
  rw [decide_eq_false (show ¬ sint.Z gs.Log'.len < sint.Z gs.CommitIndex' by rw [hlen, Hf.2.2.2.2.1]; omega)]
  wp_auto
  let f : Nat → Nat → Nat := fun acc n =>
    if ((st.s (uint.nat i)).log[n]?.map Entry.type) == some .config then n + 1 else acc
  have hcZ := Hf.2.2.2.2.1
  ihave IH : iprop(∃ (k mv : w64),
      "n" ∷ n_ptr ↦ k ∗ "k" ∷ k_ptr ↦ mv ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ max (st.s (uint.nat i)).commitIndex 0 + 1 ∧
        sint.Z mv = ((List.range (sint.nat k - 1)).foldl f 0 : Nat)⌝) $$ [n k]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 1) - 1 = 0 from rfl]; rfl
  wp_for IH
  obtain ⟨hk1, hk2, hkm⟩ := Hk
  wp_if_destruct
  · have hk0 : 0 ≤ sint.Z (k - W64 1) := by clear hkm; word
    have hkk : sint.Z (k - W64 1) = sint.Z k - 1 := by clear hkm; word
    have Hlt : sint.nat (k - W64 1) < es.length := by rw [Hesl.1]; clear hkm; word
    obtain ⟨e, He⟩ : ∃ e, es[sint.nat (k - W64 1)]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, (st.s (uint.nat i)).log[sint.nat (k - W64 1)]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Hell ▸ Hlt)⟩
    ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hel
    iunfold entryRO at Hex
    icases Hex with ⟨%Hex, -⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gs.Log'.len from
      ⟨hk0, by clear hkm; word⟩))]
    icases ownSlice_elem_acc _ e _ _ es hk0 He $$ Hes with ⟨He', -⟩
    icases typedPointsto_split _ _ _ $$ He' with Hef
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hef
    wp_auto
    have hk' : sint.nat (k + W64 1) - 1 = (sint.nat k - 1) + 1 := by clear hkm; word
    have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by clear hkm; word
    have hfold : (List.range (sint.nat (k + W64 1) - 1)).foldl f 0 =
        f ((List.range (sint.nat k - 1)).foldl f 0) (sint.nat k - 1) := by
      rw [hk', List.range_succ, List.foldl_append]; rfl
    rw [hkn] at Hx
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hkm; word, by clear hkm; word, ?_⟩
      rw [hfold]
      have hty : x.type = .config := by
        cases hxt : x.type
        · exfalso; rw [hxt] at Hex; simp only at Hex; rw [Hex.2] at Hif; simp at Hif
        · rfl
      have : f ((List.range (sint.nat k - 1)).foldl f 0) (sint.nat k - 1) = sint.nat k := by
        simp only [f, Hx, Option.map_some, hty, beq_self_eq_true, ite_true]
        show (sint.Z k).toNat - 1 + 1 = (sint.Z k).toNat; omega
      rw [this]; clear hkm; word
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hkm; word, by clear hkm; word, ?_⟩
      rw [hfold, hkm]
      have hty : x.type ≠ .config := by
        intro h; rw [h] at Hex; exact Hif Hex.2
      simp only [f, Hx, Option.map_some]
      cases hxt : x.type
      · rfl
      · exact absurd hxt hty
  try wp_auto
  have hkfin : sint.nat k - 1 = (st.s (uint.nat i)).commitIndex.toNat := by
    have h1 : ((sint.nat k : Nat) : Int) = sint.Z k := by clear hkm; word
    rw [hcZ] at Hif
    clear hkm; omega
  rw [hkfin] at hkm
  obtain ⟨K, hK⟩ : ∃ K, K = (List.range (st.s (uint.nat i)).commitIndex.toNat).foldl
      (fun (acc : Nat) n => if (((st.s (uint.nat i)).log[n]?).map Entry.type) == some .config then n + 1 else acc) 0 :=
    ⟨_, rfl⟩
  have hkK : sint.Z mv = (K : Int) := by rw [hK]; exact hkm
  clear hkm
  have hnc : ¬ (st.s (uint.nat i)).commitIndex > ((st.s (uint.nat i)).log.length : Int) := by omega
  unfold State.applySimpleConfChange at Hev
  simp only [hj, hnc, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at Hev
  rw [← hK] at Hev
  by_cases hk0 : 0 < K
  rotate_left
  · rw [decide_eq_false (show ¬ (sint.Z (W64 0) < sint.Z mv) by rw [hkK]; word)]
    wp_auto
    have : o = none := by simp [hk0] at Hev; exact Hev.symm
    subst this
    iapply HΦ; ipureintro; rfl
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z mv by rw [hkK]; word)]
  wp_auto
  by_cases hkc : (K : Int) ≤ (st.s (uint.nat i)).commitIndex
  rotate_left
  · rw [decide_eq_false (show ¬ (sint.Z mv ≤ sint.Z gs.CommitIndex') by rw [hkK, hcZ]; exact hkc)]
    wp_auto
    have : o = none := by simp [hk0, hkc] at Hev; exact Hev.symm
    subst this
    iapply HΦ; ipureintro; rfl
  rw [decide_eq_true (show sint.Z mv ≤ sint.Z gs.CommitIndex' by rw [hkK, hcZ]; exact hkc)]
  simp only [hk0, hkc, decide_true, Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at Hev
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %tq Ht
  · iexact Hst
  try wp_auto
  wp_apply wp_applyConfigUpdate tq st [] i mv $$ [Ht] as Ht
  · iframe Ht; ipureintro; exact ⟨Hi, by rw [hkK]; omega, by rw [hkK]; omega⟩
  have hmvK : sint.nat mv = K := by
    have : ((sint.nat mv : Nat) : Int) = sint.Z mv := by word
    omega
  rw [hmvK]
  try wp_auto
  rw [decide_strRel Hf.2.1 strRel_leader]
  by_cases hl : (st.s (uint.nat i)).state = leader ∧ (K : Int) ≤ (st.s (uint.nat i)).pendingConfChangeIndex
  · obtain ⟨hl1, hl2⟩ := hl
    have hcond : ((st.s (uint.nat i)).state == leader &&
        decide ((st.s (uint.nat i)).pendingConfChangeIndex ≥ ↑K)) = true := by simp [hl1, hl2]
    simp only [hcond, ↓reduceIte] at Hev
    rw [decide_eq_true hl1]
    wp_auto
    rw [decide_eq_true (show sint.Z mv ≤ sint.Z gs.PendingConfChangeIndex' by rw [hkK, Hf.2.2.2.2.2]; exact hl2)]
    wp_auto
    iunfold stateOwn at Ht
    icases Ht with ⟨%g2, %sm2, Hp2, #Hsrv2, Hm2, %Hkeys2, %Hnd2, Hsrvs2, #Hb12, #Hb22, %Hrc2⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hp2 with ⟨Hp2, %Hp2nn⟩
    icases typedPointsto_split _ _ _ $$ Hp2 with Hp2f
    simp only [TypedPointsto.typedPointstoDef]
    icases Hp2f with ⟨T1, T2, T3, T4, T5, T6, T7, -⟩
    wp_auto
    ihave Hp2 : tq ↦ ({ g2 with ReconfigCount' := g.ReconfigCount' + W64 1 } : G.State) $$ [T1 T2 T3 T4 T5 T6 T7]
    · iapply typedPointsto_combine _ _ _ Hp2nn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Ht : stateOwn (GF := GF) tq
        { st.applyConfigUpdate (uint.nat i) K with reconfigCount := st.reconfigCount + 1 } [uint.nat i]
        $$ [Hp2 Hm2 Hsrvs2]
    · iunfold stateOwn
      iexists ({ g2 with ReconfigCount' := g.ReconfigCount' + W64 1 } : G.State), sm2
      isplitl [Hp2]
      · iexact Hp2
      isplitr
      · iexact Hsrv2
      isplitl [Hm2]
      · iexact Hm2
      isplitr
      · ipureintro; exact Hkeys2
      isplitr
      · ipureintro; exact Hnd2
      isplitl [Hsrvs2]
      · iexact Hsrvs2
      isplitr
      · iexact Hb12
      isplitr
      · iexact Hb22
      ipureintro
      refine ⟨?_, Hrc2.2.1, Hrc2.2.2⟩
      show sint.Z (g.ReconfigCount' + W64 1) = st.reconfigCount + 1
      rw [← Hrc.1] at Hrc0 ⊢; word
    obtain ⟨stR, hstR⟩ : ∃ s, s = ({ st.applyConfigUpdate (uint.nat i) K with reconfigCount := st.reconfigCount + 1 } : State) :=
      ⟨_, rfl⟩
    rw [← hstR]
    rw [← hstR] at Hev
    have Hi : uint.nat i ∈ stR.server := by rw [hstR]; exact Hi
    mut_open tq, stR, [uint.nat i], i, Ht
    try wp_auto
    ihave Hcp : cp ↦ ({ gc with PendingConfChangeIndex' := W64 0 } : G.Server) $$ [CurrentTerm State VotedFor Lead Log
        CommitIndex VotesResponded VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc := serverOwn_intro cp ({ gc with PendingConfChangeIndex' := W64 0 } : G.Server) mc
        ((fun v : Server => { v with pendingConfChangeIndex := 0 }) (stR.s (uint.nat i)))
        ⟨Hcf.1, Hcf.2.1, Hcf.2.2.1, Hcf.2.2.2.1, Hcf.2.2.2.2.1, rfl⟩ Hcmi $$ [Hcp Hcm]
    · iframe Hcp Hcm Hcl Hcr Hcg Hcc Hcd
    ihave Ht := stateOwnHole_close_upd _ _ _ _ _ (fun v : Server => { v with pendingConfChangeIndex := 0 }) Hi $$ [Hh Hc]
    · iframe
    try wp_auto
    asc_tail (stR.upd (uint.nat i) (fun v : Server => { v with pendingConfChangeIndex := 0 })), [uint.nat i, uint.nat i]
  have hcond : ((st.s (uint.nat i)).state == leader &&
      decide ((st.s (uint.nat i)).pendingConfChangeIndex ≥ ↑K)) = false := by
    by_cases h1 : (st.s (uint.nat i)).state = leader
    · have h2 : ¬ (K : Int) ≤ (st.s (uint.nat i)).pendingConfChangeIndex := fun h => hl ⟨h1, h⟩
      simp [h2]
    · simp [h1]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte] at Hev
  by_cases h1 : (st.s (uint.nat i)).state = leader
  · rw [decide_eq_true h1]
    wp_auto
    have h2 : ¬ (K : Int) ≤ (st.s (uint.nat i)).pendingConfChangeIndex := fun h => hl ⟨h1, h⟩
    rw [decide_eq_false (show ¬ (sint.Z mv ≤ sint.Z gs.PendingConfChangeIndex') by rw [hkK, Hf.2.2.2.2.2]; exact h2)]
    wp_auto
    asc_tail (st.applyConfigUpdate (uint.nat i) K), [uint.nat i]
  rw [decide_eq_false h1]
  wp_auto
  asc_tail (st.applyConfigUpdate (uint.nat i) K), [uint.nat i]

end proof

end Etcdraft
end EtcdGrove
end Perennial
