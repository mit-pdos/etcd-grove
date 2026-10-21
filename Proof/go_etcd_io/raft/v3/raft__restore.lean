/-
Port of `election_proof/proof_raft__restore.v`.

raft v3.7 (stage R4): the snapshot is a pointer, owned (`ownSnapE sp 1 sv`). It is opened into
its conf state and the rest (`snapRest`, `LemmasSendRD.lean`); the getters chains
(`s.GetMetadata().GetIndex()`, `.GetConfState()`, `.GetTerm()`) are run on the fields, from the
getters' bodies (`wp_Snapshot_GetMetadata_field`, ...), so that `cs` is the snapshot's own conf
state pointer `pc` (the getters' specs do not say which pointer they return). `cs` is set (it has
`id`, so the `nil` case of `GetConfState` is dead), `pb.EnsureConfState` makes its `AutoLeave`
non-`nil` in place. The `found` search reads `cs`'s three slices (owned, lent one at a time,
`found_slice_acc`). `raftLog.restore(s)` gets half of the snapshot; the other half keeps the
pointers, ties the returned half to them (`ownSnapM_tie`) and lends `cs` to `confchange.Restore`
and `assertConfStatesEquivalent`; the halves are put back together at the end.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__restore
public import Proof.go_etcd_io.raft.v3.LemmasConfState
public import Spec.go_etcd_io.raft.v3.raftLog__matchTerm
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftLog__restore
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Proof.go_etcd_io.raft.v3.InvApplyConfC
public import Proof.go_etcd_io.raft.v3.LemmasSendRD
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A list without repeats is a permutation of the elements of its set. -/
private theorem perm_elements_listToSet (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

private theorem gset_size_union_le (X Y : GSet w64) :
    GMap.size (X ∪ Y) ≤ GMap.size X + GMap.size Y := by
  rw [GMap.size_union_alt]
  have := GMap.subseteq_size (GMap.difference_subseteq Y X)
  omega

/-- The progress map `Restore` builds for the lists `cl` has at most as many entries as the
lists have ids. -/
private theorem restore_prs_size (cl : CSLists) (Hvnd : cl.voters.Nodup) (Hlnd : cl.learners.Nodup)
    (Hond : cl.outgoing.Nodup)
    (Hsz : (cl.voters.length + cl.learners.length + cl.outgoing.length + cl.learnersNext.length :
      Int) ≤ 2 ^ 62)
    (prs : GMap w64 Loc) (al : Bool)
    (Hprs : domSet prs =
      domSet (cfgStateC (csCfgM cl.outgoing cl.voters cl.learners cl.learnersNext al)).prs) :
    (GMap.size prs : Int) ≤ 2 ^ 62 := by
  have Hd : domSet prs = (GMap.listToSet cl.voters ∪ GMap.listToSet cl.outgoing) ∪
      GMap.listToSet cl.learners := by
    rw [Hprs]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom']
    simp only [cfgStateC, csCfgM, CfgM.voters]
    rw [cfgFlags_mem]
    simp only [GMap.elem_of_union]
  have h1 := GMap.size_dom prs
  rw [Hd] at h1
  have h2 := gset_size_union_le (GMap.listToSet cl.voters ∪ GMap.listToSet cl.outgoing)
    (GMap.listToSet cl.learners)
  have h3 := gset_size_union_le (GMap.listToSet cl.voters) (GMap.listToSet cl.outgoing)
  rw [GMap.size_list_to_set _ Hvnd, GMap.size_list_to_set _ Hond] at h3
  rw [GMap.size_list_to_set _ Hlnd] at h2
  have : (0 : Int) ≤ cl.learnersNext.length := by omega
  omega

/-- What `confchange.Restore` builds for a `ConfState` denoting `c`, as `switchToConfig` takes
it (`ownConfigC`): its `Progress` values are some `pvs` whose learner flags are `c`'s. -/
private theorem ownConfigC_of_restore (c : CfgM) (cfgv : tracker.Config) (prsm : Loc)
    (prs : GMap w64 Loc) (Hinv : CfgInv (cfgStateC c))
    (Hdom : domSet prs = domSet (cfgStateC c).prs) (Hsz : (GMap.size prs : Int) ≤ 2 ^ 62)
    (P : w64 → Progress → Prop) (HP : ∀ k p, P k p → (cfgStateC c).prs !! k = some p.learner) :
    ⊢ ownCfgCC (GF := GF) cfgv (DFrac.own 1) c -∗ prsm ↦$□ prs -∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜P k p⌝) -∗
      ∃ pvs, ownConfigC c cfgv prsm prs pvs := by
  iintro Hc #Hprsm Hprogs
  ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner⌝) $$ [Hprogs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
    intro k pr _
    iintro ⟨%p, Hp, %Hpk⟩
    iexists p
    iframe Hp
    ipureintro; exact HP k p Hpk
  icases bigSepM_exist_sepM2 prs
    (fun k pr (p : Progress) => iprop(ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner⌝))
    $$ Hprogs with ⟨%pvs, Hprogs⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ Hprogs with ⟨Hprogs, Hfl⟩
  ihave %Hfl := BigSepM2.bigSepM2_pure_intro $$ Hfl
  -- the learner flags of `pvs` are the configuration's
  have Htf : trkFlags pvs = (cfgStateC c).prs := by
    apply GMap.map_eq; intro k
    rw [trkFlags_lookup]
    cases hp : pvs !! k with
    | some p =>
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1
        ((Hiff k).2 (by show (pvs !! k).isSome = true; rw [hp]; rfl))
      exact (Hfl k pr p hpr hp).symm
    | none =>
      cases hc : (cfgStateC c).prs !! k with
      | none => rfl
      | some b =>
        exfalso
        have hk : k ∈ domSet prs := by
          rw [Hdom, GMap.elem_of_dom', GMap.mem_iff, hc]; rfl
        rw [GMap.elem_of_dom', GMap.mem_iff] at hk
        have h2 : (pvs !! k).isSome = true := (Hiff k).1 hk
        rw [hp] at h2
        exact absurd h2 (by decide)
  iexists pvs
  unfold ownConfigC
  iframe Hc Hprsm Hprogs
  ipureintro
  refine ⟨?_, ?_, ?_, Hsz⟩
  · rw [Htf]; exact Hinv
  · rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom']
    simp only [cfgStateC, CfgM.ids]
    rw [cfgFlags_mem, GMap.elem_of_union]
  · intro k p hp
    have h1 : (cfgStateC c).prs !! k = some p.learner := by
      rw [← Htf, trkFlags_lookup, hp]; rfl
    simp only [cfgStateC] at h1
    rw [cfgFlags_lookup] at h1
    by_cases hv : k ∈ c.voters
    · rw [ite_eq_left hv] at h1
      have hl : k ∉ c.learners := by
        intro hl
        obtain ⟨ho, hi, -⟩ := Hinv.2.2.1 k hl
        unfold CfgM.voters at hv
        rcases (GMap.elem_of_union _ _ _).1 hv with h | h
        · exact hi h
        · exact ho h
      rw [← Option.some.inj h1]; simp [hl]
    · rw [ite_eq_right hv] at h1
      by_cases hl : k ∈ c.learners
      · rw [ite_eq_left hl] at h1; rw [← Option.some.inj h1]; simp [hl]
      · rw [ite_eq_right hl] at h1; cases h1

/-- `restore`'s `found` search has not met `id` in the first `k` of its three sets
(`[Voters, Learners, VotersOutgoing]`). -/
private def FoundBefore (cl : CSLists) (id : w64) (k : Nat) : Prop :=
  ∀ (j : Nat) (L : List w64), j < k → [cl.voters, cl.learners, cl.outgoing][j]? = some L →
    id ∉ L

private theorem foundBefore_zero (cl : CSLists) (id : w64) : FoundBefore cl id 0 :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

private theorem foundBefore_succ {cl : CSLists} {id : w64} {k : Nat} {L : List w64}
    (H : FoundBefore cl id k) (HL : [cl.voters, cl.learners, cl.outgoing][k]? = some L)
    (Hn : id ∉ L) : FoundBefore cl id (k + 1) := by
  intro j L' hj hL'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
  · exact H j L' h hL'
  · subst h; rw [HL] at hL'; cases hL'; exact Hn

private theorem foundBefore_three {cl : CSLists} {id : w64} (H : FoundBefore cl id 3)
    (Hin : id ∈ cl.voters ∨ id ∈ cl.learners ∨ id ∈ cl.outgoing) : False := by
  rcases Hin with h | h | h
  · exact H 0 _ (by decide) rfl h
  · exact H 1 _ (by decide) rfl h
  · exact H 2 _ (by decide) rfl h

/-- (D22 S-b) An id `found` meets in one of the three sets is one of the `ConfState`'s. -/
private theorem found_has {cl : CSLists} {id : w64} {k : Nat} {L : List w64} (hk : k < 3)
    (HL : [cl.voters, cl.learners, cl.outgoing][k]? = some L) (Hin : id ∈ L) : cl.Has id := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at HL <;>
    subst HL <;> simp [CSLists.Has, Hin]

/-- The `k`-th set `found` searches, lent out of the three. -/
private theorem found_slice_acc (sv sl so : GoSlice) (dq : DFrac) (cl : CSLists) (k : Nat)
    (hk : k < 3) :
    (sv ↦*{dq} cl.voters ∗ sl ↦*{dq} cl.learners ∗ so ↦*{dq} cl.outgoing : IProp GF) ⊢
      ∃ (s' : GoSlice) (L : List w64),
        ⌜[sv, sl, so][k]? = some s' ∧ [cl.voters, cl.learners, cl.outgoing][k]? = some L⌝ ∗
        s' ↦*{dq} L ∗
        (s' ↦*{dq} L -∗ sv ↦*{dq} cl.voters ∗ sl ↦*{dq} cl.learners ∗ so ↦*{dq} cl.outgoing) := by
  iintro ⟨Hv, Hl, Ho⟩
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · iexists sv, cl.voters
    iframe Hv
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iintro Hv; iframe
  · iexists sl, cl.learners
    iframe Hl
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iintro Hl; iframe
  · iexists so, cl.outgoing
    iframe Ho
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iintro Ho; iframe

/-- (D22 S-b) Once `found` meets `id`, `EnsureConfState`'s conf state `q` is the snapshot's `pc`:
an implication kept opaque, so that `word` does not unfold it. -/
private def FoundQ (cl : CSLists) (id : w64) (q pc : Loc) : Prop := cl.Has id → q = pc

private theorem ownCfgCC_cast (cfgv : tracker.Config) (dq : DFrac) (c1 c2 : CfgM) (h : c1 = c2) :
    ownCfgCC (GF := GF) cfgv dq c1 ⊢ ownCfgCC cfgv dq c2 := h ▸ .rfl

set_option hygiene false in
/-- The snapshot closed again (`ownSnapE`) from its parts and its conf state `Hcs` (`csOptA`). -/
local macro "snap_close" : tactic => `(tactic| (
  ihave Hsnap : ownSnapE sp (DFrac.own 1) sv $$ [HD Hd HM HC HI HT Hcs]
  · iapply ownSnapE_close sp pm pc
    iframe Hcs
    iunfold snapRest
    iexists ds, pi, pt, uf, ufm
    iframe
    iframe cI cT Hpb Hpbm
    ipureintro; exact ⟨Hspn, Hpmn⟩))

/-- The body's exits in order (`raft.restore.impl`):

- `Index <= committed`: `false`;
- `state != StateFollower`: dead (`s.role = .follower`);
- the `found` search over `[Voters; Learners; VotersOutgoing]`: `id` is in one of them
  (since 2026-10-14, stage B8; until then among the voters): if it is, the inner loop breaks in
  some set and the outer loop right after it (`FoundBefore`: no earlier set has it); if not
  (D22 S-b, D22j: until then excluded by a premise), the three sets run out and the `!found` exit
  logs a warning and returns `false` (`RestoreResult`'s first case). `EnsureConfState` of a `nil`
  conf state is a fresh empty one, in which nothing is found (`wp_EnsureConfState_opt`);
- `matchTerm(id)`: `lastEntryID`, an `Infof`, `commitTo(Index)` (in range: `Index` has
  a term in the log) and `false`;
- otherwise `raftLog.restore(s)`; the tracker replaced by the empty one
  `MakeProgressTracker` builds -- `ownRaftPhys` at the empty configuration, as in
  `newRaft` (`ownRaftPhysC_retrack`, `ownTracker_empty`; the tally was already empty,
  `s.votes = ∅`); `confchange.Restore` on it, its `v0` read back out of the empty
  tracker; then `switchToConfig` to the snapshot's configuration and `assertConfStatesEquivalent`;
  `lastEntryID`, an `Infof` and `true`. -/
theorem raft.restore.wp_proof
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_restore : raftLog.restore.spec (GF := GF) (hG := hG))
    (wp_MakeProgressTracker : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG))
    (wp_confchange_Restore : confchange.Restore.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (wp_assertConfStatesEquivalent : assertConfStatesEquivalent.spec (GF := GF) (hG := hG))
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    raft.restore.spec (GF := GF) (hG := hG) := by
  intro c r id s sp sv cl Hrole Hvotes Hcl Hscope Hns
  subst Hcl
  -- (D22 S-b′4) the scope only once the node is found; the index bound either way
  obtain ⟨Hscope, Hidx61⟩ := Hscope
  wp_start as H
  iNamed H
  icases ownSnapE_open _ _ _ $$ Hsnap with ⟨%pm, %pc, Hrest, Hcs⟩
  iunfold snapRest at Hrest
  iNamed Hrest
  obtain ⟨Hspn, Hpmn⟩ := Hnn
  wp_auto
  wp_apply wp_Snapshot_GetMetadata_field sp pm _ Hspn $$ [$HM] as HM
  wp_apply wp_SnapshotMetadata_GetIndex_field pm pi _ _ Hpmn $$ [$HI $cI] as HI
  -- `s.Metadata.Index <= r.raftLog.committed`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  by_cases Hst : uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.committed
  · -- obsolete
    rw [decide_eq_true Hst]
    wp_auto
    snap_close
    iapply HΦ $$ %false %s
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte]
    iframe Hphys Hsnap
    ipureintro
    exact .inl ⟨.inl Hst, rfl, rfl⟩
  rw [decide_eq_false Hst]
  wp_auto
  -- `r.state != StateFollower`: a follower
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  rw [Hrole, decide_eq_true (show stateW64 PRole.follower = W64 0 from rfl)]
  wp_auto
  -- `cs := pb.EnsureConfState(s.GetMetadata().GetConfState())`: the snapshot's conf state, its
  -- `AutoLeave` made non-`nil`; (D22 S-b, D22j) `nil` or not: a `nil` one is a fresh empty one,
  -- in which the search below finds nothing
  wp_apply wp_Snapshot_GetMetadata_field sp pm _ Hspn $$ [$HM] as HM
  wp_apply wp_SnapshotMetadata_GetConfState_field pm pc _ Hpmn $$ [$HC] as HC
  icases csOptA_nn _ _ _ $$ Hcs with ⟨Hcs, %Hpcn⟩
  try wp_auto
  wp_apply wp_EnsureConfState_opt wp_EnsureConfState pc _ $$ [Hcs] as %q ⟨#Hcfq, Hcs, %Hq⟩
  · iexact Hcs
  -- once the search finds `id`, the conf state is the snapshot's own (a `nil` one has no ids)
  -- (kept in the Iris context, out of `word`'s sight)
  ihave Hfq : ⌜FoundQ sv.Metadata'.ConfState'.lists id q pc⌝ $$ []
  · ipureintro
    intro Hh
    apply Hq
    rcases Hpcn with ⟨-, Hc0⟩ | Hpcn
    · exfalso; rw [Hc0] at Hh; simp [CSLists.Has, ConfStateM.lists] at Hh
    · exact Hpcn
  clear Hq Hpcn
  -- the `found` search over `[Voters; Learners; VotersOutgoing]`
  ihave Hcsq : csPts q DFrac.discard sv.Metadata'.ConfState' true $$ []
  · iexact Hcfq
  iunfold csPts at Hcsq
  icases Hcsq with ⟨%csv, %csl, %cso, %csn, %cpa, %Hcnn, HcV, Hcv, HcL, Hcl', HcO, Hco, HcN, Hcn,
    HcA, #ccA, %Hcal, #Hcpb⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %rsl ⟨Hrsl, -⟩
  simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
    List.set_cons_succ, List.set_cons_zero]
  wp_auto
  ihave %Hrlen := ownSlice_len $$ Hrsl
  simp only [List.length_cons, List.length_nil] at Hrlen
  -- the outer loop: no set before the current one has `id`; the inner loop finds it in some set,
  -- breaking both, or the three run out (the `!found` exit)
  ihave IH : (∃ (k : w64) (st : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "set" ∷ set_ptr ↦ st ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3 ∧ FoundBefore sv.Metadata'.ConfState'.lists id (sint.Z k).toNat⌝) $$ [i set found]
  · iexists W64 0, zero_val GoSlice
    iframe i set found
    ipureintro; exact ⟨by word, by word, foundBefore_zero sv.Metadata'.ConfState'.lists id⟩
  wp_for IH
  obtain ⟨Hk0, Hk3, Hkb⟩ := Hk
  wp_if_destruct
  rotate_left
  · -- (D22 S-b, D22j) the three sets ran out without `id`: the `!found` exit, `false`
    have Hk3' : (sint.Z k).toNat = 3 := by
      have : ¬ sint.Z k < 3 := by word
      omega
    rw [Hk3'] at Hkb
    have Hnf : ¬ CSLists.Has sv.Metadata'.ConfState'.lists id := fun h => foundBefore_three Hkb h
    -- the `Warningf`: `r.id`, `cs`
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    try wp_auto
    wp_raft_logC
    snap_close
    iapply HΦ $$ %false %s
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte]
    iframe Hphys Hsnap
    ipureintro
    exact .inl ⟨.inr Hnf, rfl, rfl⟩
  have Hk3' : (sint.Z k).toNat < 3 := by
    have : sint.Z k < 3 := by word
    omega
  icases found_slice_acc csv csl cso _ sv.Metadata'.ConfState'.lists (sint.Z k).toNat Hk3'
    $$ [Hcv Hcl' Hco] with ⟨%sl, %L, %HsL, HL, Hback3⟩
  · simp only [ConfStateM.lists]; iframe
  obtain ⟨Hsl, HLk⟩ := HsL
  rw [ite_eq_left]
  rotate_left
  · exact ⟨Hk0, by word⟩
  wp_apply wp_load_slice_index (V := GoSlice) (t := go.uint64.SliceType) _ (sint.Z k) _ _
      sl Hk0 $$ [$Hrsl] as Hrsl
  · ipureintro; exact Hsl
  ihave %Hvlen := ownSlice_len $$ HL
  ihave IH2 : (∃ (k2 x : w64),
      "i" ∷ i_ptr ↦ k2 ∗ "id" ∷ id_ptr ↦ x ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hk2" ∷ ⌜(0 ≤ sint.Z k2 ∧ sint.Z k2 ≤ (L.length : Int)) ∧
                id ∉ L.take (sint.Z k2).toNat⌝) $$ [i id found]
  · iexists W64 0, zero_val w64
    iframe i id found
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH2
  obtain ⟨Hk2b, Hk2n⟩ := Hk2
  wp_if_destruct
  rotate_left
  · -- this set ran out without `id`: on to the next one
    have HnL : id ∉ L := by
      have := Hk2n
      rwa [List.take_of_length_le (by word)] at this
    icases Hback3 $$ HL with ⟨Hcv, Hcl', Hco⟩
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1 by word]
    exact foundBefore_succ Hkb HLk HnL
  list_elem L (sint.Z k2).toNat as y
  rw [ite_eq_left (show 0 ≤ sint.Z k2 ∧ sint.Z k2 < sint.Z sl.len by word)]
  wp_apply wp_load_slice_index (V := w64) (t := go.uint64) _ (sint.Z k2) L _ y
      (by omega) $$ [$HL] as HL
  · ipureintro; exact Hy_lookup
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  by_cases Hne : y = id
  rotate_left
  · -- not this one: next
    rw [decide_eq_false Hne]
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [show (sint.Z (k2 + W64 1)).toNat = (sint.Z k2).toNat + 1 by word,
      List.take_add_one, Hy_lookup]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
    exact ⟨Hk2n, fun h => Hne h.symm⟩
  -- found: break the inner loop, then the outer one
  subst y
  -- (D22 S-b) the node is one of the `ConfState`'s ids, so the conf state is the snapshot's
  have Hidv : CSLists.Has sv.Metadata'.ConfState'.lists id :=
    found_has Hk3' HLk (List.mem_of_getElem? Hy_lookup)
  -- (D22 S-b′4) found: the scope of its lists
  obtain ⟨Hwf, Hvnd, Hlnd, Hond, Hnnd, Hsz, Hal0, -⟩ := Hscope (by
    first | exact Hidv | (rw [Hcl]; exact Hidv) | (subst Hcl; exact Hidv))
  icases Hfq with %Hfq
  have Hqp : pc = q := (Hfq Hidv).symm
  subst Hqp
  ihave #Hcf := Hcfq
  iclear Hcs
  rw [decide_eq_true rfl]
  wp_auto
  icases Hback3 $$ HL with ⟨Hcv, Hcl', Hco⟩
  wp_for_post
  wp_for_post
  iclear HcV Hcv HcL Hcl' HcO Hco HcN Hcn HcA
  -- `id := entryID{term: s.GetMetadata().GetTerm(), index: s.GetMetadata().GetIndex()}`
  wp_apply wp_Snapshot_GetMetadata_field sp pm _ Hspn $$ [$HM] as HM
  wp_apply wp_SnapshotMetadata_GetTerm_field pm pt _ _ Hpmn $$ [$HT $cT] as HT
  wp_apply wp_Snapshot_GetMetadata_field sp pm _ Hspn $$ [$HM] as HM
  wp_apply wp_SnapshotMetadata_GetIndex_field pm pi _ _ Hpmn $$ [$HI $cI] as HI
  try wp_auto
  -- `matchTerm(id)`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_matchTerm _ _ { term' := sv.Metadata'.Term', index' := sv.Metadata'.Index' }
    $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  -- (D19i part 1) above `committed`, so above the floor: `matchTerm` is exact
  icases ownRaftLog_fl _ _ $$ Hlog with ⟨%Hflb, Hlog⟩
  have Hb := Hb.2 (by simp only; omega)
  ihave Hphys := Hlogback $$ Hlog
  change b = decide (PlogMatches _ _ (snapId sv)) at Hb
  by_cases Hm : PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (snapId sv)
  · -- the log has the snapshot's last entry: fast-forward the commit
    rw [Hb, decide_eq_true Hm]
    wp_auto
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %last ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    -- the `Infof`: `r.id`, `r.raftLog.committed`, the two ids
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    -- `commitTo(Index)`: in range, the log has a term at `Index`
    obtain ⟨-, Hle⟩ := plogTermAt_some_range _ _ _ _ Hm
    wp_apply wp_Snapshot_GetMetadata_field sp pm _ Hspn $$ [$HM] as HM
    wp_apply wp_SnapshotMetadata_GetIndex_field pm pi _ _ Hpmn $$ [$HI $cI] as HI
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
    wp_apply wp_raftLog_commitTo _ _ sv.Metadata'.Index' Hle $$ [$Hlog] as Hlog
    ihave Hphys := Hlogback $$ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl
      (hcm := plogCommitTo_ge _ _))
      %(fun _ => logLast_le_of_fields rfl rfl rfl)
    try wp_auto
    ihave Hcs : csOptA pc (DFrac.own 1) sv.Metadata'.ConfState' $$ []
    · iunfold csOptA; iright; iright; iexact Hcf
    snap_close
    iapply HΦ $$ %false %_
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte]
    iframe Hphys Hsnap
    ipureintro
    refine .inr (.inl ⟨by simp only [snapId]; omega, Hidv, Hm, rfl, ?_⟩)
    simp only [plogCommitTo, snapId] at *
    rw [ite_eq_left (by omega)]
  · rw [Hb, decide_eq_false Hm]
    wp_auto
    -- `r.raftLog.restore(s)`, on half of the snapshot: the other half keeps the pointers `pm` and
    -- `pc` (`cs`), for `confchange.Restore` and `assertConfStatesEquivalent`
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at $$ Hphys with ⟨Hlog, %Hgh1, Hlogback⟩
    -- (D22 S-d3a) the restore past the commit index keeps what the log says of the snapshot the
    -- last `Ready` handed out (`SnpOk`)
    have Hsnp1 : SnpOk s.gh (logRestore s.logst (snapTrip sv sv.Metadata'.ConfState'.lists)) :=
      Hgh1.1.2.restore _ (by simp only [snapTrip, snapId]; omega)
    ihave Hrest : snapRest sp pm pc (DFrac.own 1) sv $$ [HD Hd HM HC HI HT]
    · iunfold snapRest
      iexists ds, pi, pt, uf, ufm
      iframe
      iframe cI cT Hpb Hpbm
      ipureintro; exact ⟨Hspn, Hpmn⟩
    icases snapRest_split sp pm pc (DFrac.own (Qp.half 1)) (DFrac.own (Qp.half 1)) sv $$ [Hrest]
      with ⟨HrA, HrB⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hrest
    ihave HsA : ownSnapM sp (DFrac.own (Qp.half 1)) sv $$ [HrA]
    · iapply ownSnapM_of_rest
      iframe HrA
      iunfold csOptA; iright; iright; iexact Hcf
    wp_apply wp_raftLog_restore _ _ sp _ sv (by simp only [snapId]; omega)
        (by simp only [snapId]; omega) $$ [$Hlog $HsA $Hcert] as ⟨HsA, Hlog⟩
    icases ownSnapM_tie sp pm pc _ _ sv $$ [HsA HrB] with ⟨HrA, HcsA, HrB⟩
    · iframe
    ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.of_snap (by simp [logRestore]) Hns Hsnp1)
      %(fun h => absurd (Hrole.symm.trans h) (by decide))
    -- the tracker replaced by the empty one, the log used meanwhile
    icases ownRaftPhysC_retrack c c.voters (CfgM.simple ∅ (domSet (∅ : GMap w64 Loc) \ ∅)).voters
        (c := CfgM.simple ∅ (domSet (∅ : GMap w64 Loc) \ ∅)) _ _ _
        (by intro h; exact absurd Hrole h) $$ Hphys with ⟨%tv, Htrkf, Htrk, Hlf, Hlog, Hback⟩
    icases ownTrackerC_maxinflight $$ Htrk with ⟨%Hmi, -⟩
    wp_auto
    wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes0, Hprs0⟩
    obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
    -- `confchange.Restore`: the empty tracker, the snapshot's `ConfState`, which it answers
    -- exactly (`restoreM_wf`)
    ipersist Hprs0
    have Hmi0 : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
      rw [Htv0mi]; exact Hmi
    have Hvne : sv.Metadata'.ConfState'.lists.voters ≠ [] := Hwf.1
    have Hrm := restoreM_wf sv.Metadata'.ConfState'.lists.outgoing sv.Metadata'.ConfState'.lists.voters sv.Metadata'.ConfState'.lists.learners sv.Metadata'.ConfState'.lists.learnersNext
      sv.Metadata'.ConfState'.AutoLeave' Hwf
    have Hinv := restoreM_cfgInv Hrm
    ihave HcB := csPts_weaken $$ Hcf
    wp_apply wp_confchange_Restore { Tracker' := tv0, LastIndex' := li } pc sv.Metadata'.ConfState'
        _ v0 _ Hrm Hmi0 Htv0arr Htv0l Htv0ln Htv0al
        $$ [$HcB $Hv0 $Hprs0]
      as %cfgv %prsm %prs ⟨HcB, Hv0, -, Hres⟩
    -- a voter, so an op ran: the fresh maps (2026-10-16, stage R8b)
    icases Hres with (⟨%Hops, -⟩ | ⟨-, Hcfg, Hprsm, %Hprs, Hprogs⟩)
    · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hvne Hops
    -- the configuration `Restore` built, as `switchToConfig` takes it
    ipersist Hprsm
    have Hsz' : (GMap.size prs : Int) ≤ 2 ^ 62 :=
      restore_prs_size sv.Metadata'.ConfState'.lists Hvnd Hlnd Hond Hsz prs sv.Metadata'.ConfState'.AutoLeave' Hprs
    ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
        ⌜(cfgStateC (csCfgM sv.Metadata'.ConfState'.lists.outgoing sv.Metadata'.ConfState'.lists.voters sv.Metadata'.ConfState'.lists.learners sv.Metadata'.ConfState'.lists.learnersNext
          sv.Metadata'.ConfState'.AutoLeave')).prs !! k = some p.learner⌝) $$ [Hprogs]
    · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
      intro k pr _
      iintro ⟨%p, Hp, %Hpk⟩
      iexists p
      iframe Hp
      ipureintro
      simpa [cfgStateC, cfgFlags, csCfgM, CfgM.voters, ConfStateM.lists] using Hpk
    ihave Hcfg := ownCfgCC_cast cfgv _
      (csCfgM sv.Metadata'.ConfState'.VotersOutgoing' sv.Metadata'.ConfState'.Voters' sv.Metadata'.ConfState'.Learners' sv.Metadata'.ConfState'.LearnersNext' sv.Metadata'.ConfState'.AutoLeave')
      (snapCfg sv sv.Metadata'.ConfState'.lists) rfl $$ Hcfg
    icases ownConfigC_of_restore (snapCfg sv sv.Metadata'.ConfState'.lists) cfgv prsm prs Hinv Hprs Hsz' _ (fun _ _ h => h) $$ Hcfg Hprsm Hprogs
      with ⟨%pvs, Hnew⟩
    -- the struct, re-sealed over the empty configuration
    ihave Htrk0 := ownTracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi0 $$ Hv0 Hvotes0 Hprs0
    ihave Htrk0 := ownTracker_toC _ _ _ $$ Htrk0
    ihave Hphys := Hback $$ %tv0 %∅ %∅ %∅ %_ Hlf Htrkf Htrk0 Hlog
      %(LogGhOk.of_snap (by simp [logRestore]) Hns Hsnp1)
      %(PrvalsOk.not_leader (fun h => absurd (Hrole.symm.trans h) (by decide)))
    generalize HS1 : ({ s with votes := ∅, progress := ∅, prvals := ∅, logst := logRestore s.logst (snapTrip sv sv.Metadata'.ConfState'.lists) } : NState) = s1
    have Hrole1 : s1.role = .follower := by rw [← HS1]; exact Hrole
    -- `assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`
    wp_apply raft.wp_load_loggerC $$ Hphys as %lok0 ⟨Hphys, #Hlg0⟩
    icases ownRaftPhysCV_reconfig _ (snapCfg sv sv.Metadata'.ConfState'.lists) ((snapCfg sv sv.Metadata'.ConfState'.lists).voters ∪ {[id]}) r id s1
        (fun h => absurd Hrole1 h) $$ Hphys with ⟨%tv1, Htrkf, Hold, Hback2⟩
    icases ownTrackerC_votes $$ Hold with ⟨Hvotes, %Hmi1⟩
    wp_apply wp_raft_switchToConfig (snapCfg sv sv.Metadata'.ConfState'.lists) r id s1 tv1 cfgv prsm prs pvs
        (fun h => absurd (Hrole1.symm.trans h) (by decide))
        (fun h => by rcases h with h | h <;> rw [Hrole1] at h <;> cases h)
        (fun h => absurd (Hrole1.symm.trans h) (by decide))
      $$ [$Htrkf $Hback2 $Hvotes $Hnew]
      as %cs2 %xs2 %os2 %ls2 %lns2 %s2 ⟨Hphys, Hcs2v, %Hcs2, %Hsw⟩
    · ipureintro; exact Hmi1
    obtain ⟨Hxs2, Hos2, Hls2, Hlns2⟩ := Hcs2
    unfold SwitchOkC at Hsw
    rw [ite_eq_right (by simp [Hrole1])] at Hsw
    subst Hsw
    -- the snapshot's lists against the configuration's sets
    have Hperm : sv.Metadata'.ConfState'.lists.Perm ⟨xs2, ls2, os2, lns2⟩ := by
      refine ⟨(perm_elements_listToSet _ Hvnd).trans Hxs2.symm,
        (perm_elements_listToSet _ Hlnd).trans Hls2.symm,
        (perm_elements_listToSet _ Hond).trans Hos2.symm,
        (perm_elements_listToSet _ Hnnd).trans Hlns2.symm⟩
    have Hbnd : sv.Metadata'.ConfState'.lists.Bounded := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    ihave Hcs2v := csPts_weaken $$ Hcs2v
    have Hal2 : sv.Metadata'.ConfState'.AutoLeave' = (snapCfg sv sv.Metadata'.ConfState'.lists).autoLeave := by
      unfold snapCfg csCfgM
      by_cases ho : sv.Metadata'.ConfState'.lists.outgoing = []
      · simp only [ho, ↓reduceIte]; exact Hal0 ho
      · simp only [ho, ↓reduceIte]
    wp_apply wp_assertConfStatesEquivalent _ pc cs2 sv.Metadata'.ConfState'
        (ConfStateM.mk xs2 ls2 os2 lns2
          (if sv.Metadata'.ConfState'.VotersOutgoing' = [] then false else sv.Metadata'.ConfState'.AutoLeave')) _ _ Hperm Hbnd Hal2
        $$ [$HcB $Hcs2v] as ⟨HcB, -⟩
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %last ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv3, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    -- the snapshot put back together
    iclear HcsA HcB
    have Hh : DFrac.own (Qp.half 1) • DFrac.own (Qp.half 1) = DFrac.own 1 := by
      rw [DFrac.op_own, Qp.half_add_half]
    ihave Hrest : snapRest sp pm pc (DFrac.own 1) sv $$ [HrA HrB]
    · rw [← Hh]; iapply snapRest_combine; iframe
    ihave Hsnap := ownSnapE_close sp pm pc _ sv $$ [Hrest]
    · iframe Hrest; iunfold csOptA; iright; iright; iexact Hcf
    iapply HΦ $$ %true %_
    simp only [restoreCfg, ↓reduceIte]
    iframe Hphys Hsnap
    ipureintro
    refine .inr (.inr ⟨by simp only [snapId]; omega, Hidv, Hm, rfl, prs, pvs,
      learnerOfC (snapCfg sv sv.Metadata'.ConfState'.lists) id, ?_⟩)
    subst HS1
    obtain ⟨⟩ := s
    simp only at Hvotes
    subst Hvotes
    rfl


end proof

end EtcdGrove
end Perennial
