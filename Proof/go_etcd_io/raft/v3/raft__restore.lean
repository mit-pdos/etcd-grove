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
pointers and ties the returned half to them (`ownSnapM_tie`); the halves are put back together at
the end. (Until 2026-10-28, stage U0, it also lent `cs` to `confchange.Restore` and
`assertConfStatesEquivalent`, the tracker's rebuild, now `appliedSnap`'s.)
-/
module

public import Spec.go_etcd_io.raft.v3.raft__restore
public import Proof.go_etcd_io.raft.v3.LemmasConfState
public import Spec.go_etcd_io.raft.v3.raftLog__matchTerm
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.raftLog__restore
public import Proof.go_etcd_io.raft.v3.InvApplyConfC
public import Proof.go_etcd_io.raft.v3.LemmasSendRD
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

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
- otherwise `raftLog.restore(s)`, `lastEntryID`, an `Infof` and `true`. (Until 2026-10-28, stage
  U0, the tracker was rebuilt from the snapshot's `ConfState` in between: `appliedSnap` does it
  now, `raft__appliedSnap.lean`.) -/
theorem raft.restore.wp_proof
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_raftLog_restore : raftLog.restore.spec (GF := GF) (hG := hG))
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    raft.restore.spec (GF := GF) (hG := hG) := by
  intro c r id s sp sv cl Hrole _ Hcl Hscope Hns
  subst Hcl
  -- (D22 S-b′4) the index bound (the scope was the tracker rebuild's, `appliedSnap`'s since stage U0)
  obtain ⟨-, Hidx61⟩ := Hscope
  wp_start as H
  iNamed H
  -- (D22 S-d4 item 4) the snapshot, every pointer field set, opened into its parts
  iunfold ownSnapS at Hsnap
  icases Hsnap with ⟨%ds, %pm, %uf, %Hspn, HD, Hd, HM, Hm, #Hpb⟩
  iunfold smPtsS at Hm
  icases Hm with ⟨%pc, %pi, %pt, %ufm, %Hnnm, HC, Hcs, HI, #cI, HT, #cT, #Hpbm⟩
  obtain ⟨Hpmn, HpcS, Hpin, Hptn⟩ := Hnnm
  ihave Hcs := csSet_A _ _ _ $$ Hcs
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
    icases ownRaftLog_quiet _ _ $$ Hlog with ⟨%Hq1, Hlog⟩
    have Hsnp1 : SnpOk s.gh (logRestore s.logst (snapTrip sv sv.Metadata'.ConfState'.lists)) :=
      Hgh1.1.2.1.restore _ (by simp only [snapTrip, snapId]; omega) Hq1.2
    ihave #Hcert' : ksnCert (GF := GF) s.logst.sn (snapTrip sv sv.Metadata'.ConfState'.lists) $$ []
    · rw [Hgh1.1.2.2]; iexact Hcert
    -- (D22 S-d4 item 4) the log's half set (its conf state read-only, `Hcf`)
    icases ownSnapS_rest_of_parts sp pm pc pi pt ds uf ufm (DFrac.own (Qp.half 1))
        (DFrac.own (Qp.half 1)) sv Hspn Hpmn HpcS Hpin Hptn $$ [HD Hd HM HC HI HT]
      with ⟨HsA, HrB⟩
    · rw [DFrac.op_own, Qp.half_add_half]
      iframe HD Hd HM HC HI HT
      iframe cI cT Hpb Hpbm Hcf
    wp_apply wp_raftLog_restore _ _ sp _ sv (by simp only [snapId]; omega)
        (by simp only [snapId]; omega) ⟨id, Hidv⟩ $$ [$Hlog $HsA $Hcert'] as ⟨HsA, Hlog⟩
    ihave HsA := ownSnapS_M _ _ _ $$ HsA
    icases ownSnapM_tie sp pm pc _ _ sv $$ [HsA HrB] with ⟨HrA, HcsA, HrB⟩
    · iframe
    ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.of_snap (by simp [logRestore]) Hns Hsnp1 Hgh1.1.2.2)
      %(fun h => absurd (Hrole.symm.trans h) (by decide))
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
    iclear HcsA
    have Hh : DFrac.own (Qp.half 1) • DFrac.own (Qp.half 1) = DFrac.own 1 := by
      rw [DFrac.op_own, Qp.half_add_half]
    ihave Hrest : snapRest sp pm pc (DFrac.own 1) sv $$ [HrA HrB]
    · rw [← Hh]; iapply snapRest_combine; iframe
    ihave Hsnap := ownSnapE_close sp pm pc _ sv $$ [Hrest]
    · iframe Hrest; iunfold csOptA; iright; iright; iexact Hcf
    iapply HΦ $$ %true %_
    iframe Hphys Hsnap
    ipureintro
    exact .inr (.inr ⟨by simp only [snapId]; omega, Hidv, Hm, rfl, rfl⟩)


end proof

end EtcdGrove
end Perennial
