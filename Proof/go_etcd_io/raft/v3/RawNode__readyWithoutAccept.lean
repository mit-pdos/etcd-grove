/- `RawNode.readyWithoutAccept`, Lean-first (2026-10-10): the first half of the proof of
`RawNode.Ready` (`RawNode__Ready.lean` until then, itself the port of
election_proof/proof_RawNode__Ready.v at 857d09190, finished in Lean), up to the call of
`acceptReady`, closed into `ownRawNodeReady`. The facts the application gets with the
`Ready` -- the committed entries extending `delivered`, the messages' `isRaftMsg` -- were
proved at the end of `Ready`'s proof; they come here, since `node.go` hands the `Ready` out
before accepting it.

Since 2026-10-10 the messages are appended with `wp_slice_append_undo`, so that the
loop keeps a way back to `r.msgs`' slice (`Hundo`, for `ownRawNodeReady_abandon`), and
their terms are bounded by the outbox's `OutTermOk` (2026-10-17: within the term ceiling; until
then, with pre-vote off, by the node's term).

Since 2026-10-13 the `ReadState`s are handed out (`rd.ReadStates = r.readStates` when not
empty): the slice read-only, and each one's `readStateOk`, copied out of the ghost state
(`ownRaftGhost_readStates`; `InvRawnodeReady.lean`'s header).

Lean notes: `readyWithoutAccept`'s `rd` is tracked as `readyVal` (one field per argument).

Raft v3.7 (2026-10-16, stage R5, `notes/decisions.md` D8): the messages are pointers and are
**handed out** (`readyDq`: a response at half, its other half kept); `r.msgsAfterAppend`'s
messages are read through `GetTo` (each one's ownership looked up in the queue's
`[∗list]`); `r.hardState()` allocates a fresh read-only hard state (inlined, as
`raft.hardState`'s proof builds it), handed out in `rd.HardState` unless equal to
`prevHardSt`; `rd.Snapshot` stays `nil`; the read states are `readStatesPts`.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasReadyR
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.raftLog__nextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__nextCommittedEnts
public import Spec.go_etcd_io.raft.v3.SoftState__equal
public import Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.MustSync
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

set_option linter.unusedSectionVars false

section helpers
variable [FfiSyntax]

/-- The `Ready` `readyWithoutAccept` builds, field by field (`Snapshot` stays `nil`: no
snapshot is pending). -/
abbrev readyVal (sp hp : Loc) (rs ents ce msgs : GoSlice) (ms : Bool) : Ready :=
  Ready.mk sp hp rs ents null ce msgs ms slice.nil

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `Ready`'s `SoftState`, made read-only (Rocq's inline `iAssert`). -/
private theorem soft_persist (c : Prop) [Decidable c] (sp : Loc) (v : SoftState) :
    ⊢ (if c then iprop(⌜sp = null⌝) else sp ↦ v) -∗
      |==> (if c then iprop(⌜sp = null⌝ : IProp GF) else sp ↦□ v) := by
  by_cases h : c
  · rw [ite_pos' h, ite_pos' h]
    iintro H; imodintro; iexact H
  · rw [ite_neg' h, ite_neg' h]
    iintro H
    ipersist H
    imodintro
    iexact H

/-- ... then forgotten down to what `acceptReady` needs: `nil`, or some read-only
`SoftState`. -/
private theorem soft_or (c : Prop) [Decidable c] (sp : Loc) (v : SoftState) :
    ⊢ (if c then iprop(⌜sp = null⌝ : IProp GF) else sp ↦□ v) -∗
      (⌜sp = null⌝ ∨ ∃ v' : SoftState, sp ↦□ v') := by
  by_cases h : c
  · rw [ite_pos' h]
    iintro H; ileft; iexact H
  · rw [ite_neg' h]
    iintro #H
    iright
    iexists v
    iexact H

theorem hsOpt_of_hsRO (p : Loc) (h : HardStateM) : hsRO (GF := GF) p h ⊢ hsOpt p h := by
  iintro H; unfold hsOpt; iright; iexact H

theorem RawNode.readyWithoutAccept.wp_proof
    (wp_raftLog_nextUnstableEnts : raftLog.nextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_nextCommittedEnts : raftLog.nextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_MustSync : MustSync.spec (GF := GF) (hG := hG))
    (wp_Message_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hlc := HasLC.hasLC)) :
    RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hsteps0 Hunp0
  wp_start as H
  iNamed H
  iNamed Hrn
  have HunpS : s.logst.unpersisted = [] := Hunp ▸ Hunp0
  -- the previous `SoftState`, as a record (no spec states it)
  obtain ⟨soft0, Hsoftv⟩ : ∃ soft0 : SoftSt, sv = softstateVal soft0 :=
    ⟨⟨sv.Lead', sv.RaftState'⟩, by cases sv; rfl⟩
  ihave %Hlen0 := BigSepL2.bigSepL2_length $$ Hpend
  rw [Hsteps0] at Hlen0
  cases steps with
  | cons _ _ => simp at Hlen0
  | nil =>
  -- ghost facts, read before anything moves
  icases ownRaftPhysC_nsOut γ _ cf rnv.raft' id s $$ Hphys Hghost with ⟨%Hnsout, Hphys, Hghost⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hghost, Hrest⟩
  icases ghostRest_nsLink γ _ cf id s $$ Hrest with ⟨%Hnl, Hrest⟩
  ihave #Hout := ownRaftGhost_outbox _ _ _ $$ Hghost
  ihave #Hrs_ok := ownRaftGhost_readStates _ _ _ $$ Hghost
  icases ownRaftGhost_committed _ _ _ $$ Hghost with ⟨%fp0, %Hfp, #Hcm⟩
  icases ownRaftPhysC_view cf rnv.raft' id s $$ Hphys with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  icases outboxRel_split _ _ _ $$ Houtbox with ⟨%Houtbox, Hown1, Hown2⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf1, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hwf2, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hwf3, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  wp_auto
  wp_apply wp_raftLog_nextUnstableEnts $$ [Hlog] as %sents ⟨Hlog, #Hents⟩
  · iframe Hlog
  -- `rn.applyUnstableEntries()` is `!asyncStorageWrites`
  wp_method_call
  wp_call
  wp_auto
  rw [Hasync]
  wp_apply wp_raftLog_nextCommittedEnts $$ [Hlog] as %sce %ce ⟨Hlog, #Hce, Hce_cap, %Hcepre, -⟩
  · iframe Hlog
  have Hsoft_iff : (s.lead = sv.Lead' ∧ stateW64 s.role = sv.RaftState') ↔
      nodeSoftstate s = soft0 := by
    subst Hsoftv
    constructor
    · intro ⟨H1, H2⟩
      show SoftSt.mk _ _ = _
      rw [H1, H2]; rfl
    · intro H
      rw [← H]; exact ⟨rfl, rfl⟩
  -- `r.softState()`, compared with `prevSoftSt`; the two arms joined
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_SoftState_equal $$ [$softSt $Hsoft] as ⟨softSt, -⟩
  wp_join iprop(∃ sp, rd_ptr ↦ readyVal sp null slice.nil sents sce sl1 false ∗
      (if nodeSoftstate s = soft0 then iprop(⌜sp = null⌝)
       else sp ↦ softstateVal (nodeSoftstate s)))
    with [rd softSt] as ⟨%sp, rd, Hsoftp⟩
  · iexists null
    iframe rd
    rw [ite_pos' (Hsoft_iff.1 Hif)]
    ipureintro; rfl
  · iexists escapingSoftSt_ptr
    iframe rd
    rw [ite_neg' (fun Hc => Hif (Hsoft_iff.2 Hc))]
    simp only [softstateVal, nodeSoftstate]
    iexact escapingSoftSt
  imod soft_persist _ _ _ $$ Hsoftp with #Hsoftp
  -- `r.hardState()`: a fresh read-only hard state (inlined, as `raft.hardState`'s proof
  -- builds it), compared with `prevHardSt`; the two arms joined
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  imod cellRO_alloc $$ «$v0» with #cT
  imod cellRO_alloc $$ «$v1» with #cV
  imod cellRO_alloc $$ «$v2» with #cC
  wp_alloc hp as Hp
  imod hsRO_of_struct hp (raftpb.HardState.mk zeroValDef «$v0_ptr» «$v1_ptr» «$v2_ptr» slice.nil 0)
    (hardstateVal (nodeHardstate s)) ⊤ rfl $$ [Hp] with #Hhp
  · iframe Hp
    rw [Hlv.1]
    simp only [hardstateVal, nodeHardstate]
    iframe cT cV cC
  clear Hlv
  wp_auto
  ihave #Hhp' := hsOpt_of_hsRO _ _ $$ Hhp
  ihave #Hhard' := hsOpt_of_hsRO _ _ $$ Hhard
  wp_apply (wp_isHardStateEqual hp rnv.prevHardSt' (hardstateVal (nodeHardstate s)) hprev) $$ [$Hhp' $Hhard']
  have Hhs_iff : ((hardstateVal (nodeHardstate s)).Term' = hprev.Term' ∧
      (hardstateVal (nodeHardstate s)).Vote' = hprev.Vote' ∧
      (hardstateVal (nodeHardstate s)).Commit' = hprev.Commit') ↔ nodeHardstate s = hsAbs hprev := by
    constructor
    · intro ⟨H1, H2, H3⟩
      show HardSt.mk _ _ _ = _
      simp only [hardstateVal, nodeHardstate] at H1 H2 H3
      rw [H1, H2, H3]; rfl
    · intro H
      rw [H]; exact ⟨rfl, rfl, rfl⟩
  wp_join iprop(rd_ptr ↦ readyVal sp (if nodeHardstate s = hsAbs hprev then null else hp)
      slice.nil sents sce sl1 false) with [rd hardSt] as rd
  · rw [ite_pos' (Hhs_iff.1 Hif)]
    iexact rd
  · rw [ite_neg' (fun Hc => Hif (Hhs_iff.2 Hc))]
    iexact rd
  generalize HHP : (if nodeHardstate s = hsAbs hprev then null else hp) = HP
  ihave #HHP : iprop(∃ h, hsOpt HP h) $$ []
  · rw [← HHP]
    by_cases He : nodeHardstate s = hsAbs hprev
    · rw [ite_pos' He]; iexists HardStateM.mk (W64 0) (W64 0) (W64 0)
      unfold hsOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
    · rw [ite_neg' He]; iexists hardstateVal (nodeHardstate s); iexact Hhp'
  wp_apply wp_raftLog_hasNextUnstableSnapshot $$ [Hlog] as %bsn ⟨Hlog, %Hbsn⟩
  · iframe Hlog
  rw [Hbsn Hsnap]
  wp_auto
  ihave %Hel := entsPts_len _ _ _ $$ Hents
  -- `if len(r.readStates) != 0 { rd.ReadStates = r.readStates }`
  wp_join iprop(rd_ptr ↦ readyVal sp HP (if s.rd.states = [] then slice.nil else rss)
      sents sce sl1 false ∗ r_ptr ↦ rnv.raft' ∗
      rnv.raft'.[raft, go!"readStates"] ↦ rss)
    with [rd r Hf_readStates] as ⟨rd, r, Hf_readStates⟩
  · first
      | (have Hne : s.rd.states ≠ [] := by
           intro h; rw [h] at Hrs; simp only [List.length_nil] at Hrs; apply Hif; word
         rw [ite_neg' Hne]
         iframe
         done)
      | (have He : s.rd.states = [] := by
           apply List.eq_nil_of_length_eq_zero; rw [Hrs.1]
           have Hz : rss.len = W64 0 := by
             first | exact Hif | (apply Classical.byContradiction; intro h; exact Hif h)
           rw [Hz]; rfl
         rw [ite_pos' He]
         iframe
         done)
  · first
      | (have Hne : s.rd.states ≠ [] := by
           intro h; rw [h] at Hrs; simp only [List.length_nil] at Hrs; apply Hif; word
         rw [ite_neg' Hne]
         iframe
         done)
      | (have He : s.rd.states = [] := by
           apply List.eq_nil_of_length_eq_zero; rw [Hrs.1]
           have Hz : rss.len = W64 0 := by
             first | exact Hif | (apply Classical.byContradiction; intro h; exact Hif h)
           rw [Hz]; rfl
         rw [ite_pos' He]
         iframe
         done)
  -- `MustSync(r.hardState(), rn.prevHardSt, len(rd.Entries))`: another fresh hard state
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  imod cellRO_alloc $$ «$v0» with #cT2
  imod cellRO_alloc $$ «$v1» with #cV2
  imod cellRO_alloc $$ «$v2» with #cC2
  wp_alloc hp2 as Hp2
  imod hsRO_of_struct hp2 (raftpb.HardState.mk zeroValDef «$v0_ptr» «$v1_ptr» «$v2_ptr» slice.nil 0)
    (hardstateVal (nodeHardstate s)) ⊤ rfl $$ [Hp2] with #Hhp2
  · iframe Hp2
    rw [Hlv.1]
    simp only [hardstateVal, nodeHardstate]
    iframe cT2 cV2 cC2
  clear Hlv
  wp_auto
  ihave #Hhp2' := hsOpt_of_hsRO _ _ $$ Hhp2
  wp_apply (wp_MustSync hp2 rnv.prevHardSt' (hardstateVal (nodeHardstate s)) hprev _)
    $$ [$Hhp2' $Hhard']
  rw [Hasync]
  wp_auto
  generalize HRS : (if s.rd.states = [] then slice.nil else rss) = RS
  generalize HMS : decide (¬sents.len = W64 0 ∨ ¬s.vote = hprev.Vote' ∨
      ¬s.term = hprev.Term') = MS
  -- `for _, m := range r.msgsAfterAppend { if m.GetTo() != r.id { rd.Messages =
  -- append(rd.Messages, m) } }`: in place, into `r.msgs`' capacity, or into a new array;
  -- either way `r.msgs`' slice can be had back (`Hundo`, for abandoning the `Ready`). The
  -- messages' ownership stays in `Hown2` (each one's `GetTo` reads it).
  ihave IH : iprop(∃ (n : w64) (msl : GoSlice) (mv : Loc),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "rd" ∷ rd_ptr ↦ readyVal sp HP RS sents sce msl MS ∗
      "Hmsgs" ∷ msl ↦* (ms1 ++ nonself id (ms2.take (sint.nat n))).map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc msl (DFrac.own 1) ∗
      "Hundo" ∷ (msl ↦* (ms1 ++ nonself id (ms2.take (sint.nat n))).map QMsg.loc -∗
                 ownSliceCap Loc msl (DFrac.own 1) -∗
                 sl1 ↦* ms1.map QMsg.loc ∗ ownSliceCap Loc sl1 (DFrac.own 1)) ∗
      "HmsgsAA" ∷ sl2 ↦* ms2.map QMsg.loc ∗
      "Hown2" ∷ ([∗list] q ∈ ms2, qOwn q) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms2.length : Int)⌝)
    $$ [i m rd Hmsgs Hmsgs_cap HmsgsAA Hown2]
  · iexists W64 0, sl1, null
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.take_zero]
    simp only [nonself, List.filter_nil, List.append_nil, named]
    iframe i m Hmsgs Hmsgs_cap HmsgsAA Hown2
    isplitl [rd]
    · iexact rd
    isplitr
    · iintro H1 H2; iframe H1 H2
    · ipureintro; word
  wp_for IH
  ihave %Hl2 := ownSlice_len _ _ _ $$ HmsgsAA
  simp only [List.length_map] at Hl2
  wp_if_destruct
  · have Hlt : sint.Z n < sint.Z sl2.len := by simpa using Hif
    list_elem ms2 (sint.nat n) as mm
    have Hmml : (ms2.map QMsg.loc)[sint.nat n]? = some mm.loc := by
      rw [List.getElem?_map, Hmm_lookup]; rfl
    rw [ite_pos' (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl2.len from ⟨Hn.1, Hlt⟩)]
    wp_apply wp_load_slice_index sl2 (sint.Z n) (ms2.map QMsg.loc) (DFrac.own 1) mm.loc Hn.1
      $$ [HmsgsAA] with HmsgsAA
    · iframe
      ipureintro
      exact Hmml
    icases bigSepL_acc_same (fun q => qOwn (GF := GF) q) ms2 _ mm Hmm_lookup $$ Hown2
      with ⟨Hmm, Hown2⟩
    wp_apply (wp_Message_GetTo.1 mm.loc (DFrac.own 1) DFrac.discard false mm.st) $$ [$Hmm]
      as Hmm
    ihave Hown2 := Hown2 $$ Hmm
    have HnS : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_if_destruct
    · -- to oneself: kept for `acceptReady`
      wp_for_post
      iframe
      iexists n + W64 1, msl, mm.loc
      rw [HnS, nonself_take_succ _ _ _ _ Hmm_lookup, ite_pos' rfl, List.append_nil]
      iframe
      ipureintro; word
    · -- to another node: handed out
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %msl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append_undo $$ [$Hmsgs $Hmsgs_cap $Hsl1]
        as %msl' ⟨Hmsgs, Hmsgs_cap, -, Hundo'⟩
      ihave Hundo : iprop(msl' ↦* ((ms1 ++ nonself id (ms2.take (sint.nat n))).map QMsg.loc
            ++ [mm.loc]) -∗
          ownSliceCap Loc msl' (DFrac.own 1) -∗
          sl1 ↦* ms1.map QMsg.loc ∗ ownSliceCap Loc sl1 (DFrac.own 1)) $$ [Hundo Hundo']
      · iintro H1 H2
        icases Hundo' $$ [H1 H2] with ⟨H1, H2⟩
        · iframe H1 H2
        iapply Hundo $$ H1 H2
      wp_for_post
      iframe
      iexists n + W64 1, msl', mm.loc
      rw [HnS, nonself_take_succ _ _ _ _ Hmm_lookup, ite_neg' Hif, ← List.append_assoc,
        List.map_append (l₁ := ms1 ++ _), List.map_cons, List.map_nil]
      iframe
      ipureintro; word
  -- the loop is done: every message of `msgsAfterAppend` seen
  have Hn2 : sint.nat n = ms2.length := by
    have : ¬ sint.Z n < sint.Z sl2.len := by simpa using Hif
    word
  rw [show ms2.take (sint.nat n) = ms2 from List.take_of_length_le (by omega)]
  -- the messages handed out: those of `r.msgs` and those of `msgsAfterAppend` to others, at
  -- `readyDq`; kept, the halves of the responses (`respHalf` of `r.msgs`'s, inside `Hundo`;
  -- `Hother`) and the self-addressed ones (`Hself`)
  have Hresp2 : ∀ q ∈ ms2, RespType q.st.msg.Type' := fun q hq => (HmsgsAA_ok q hq).1
  icases qOwns_ready ms1 $$ Hown1 with ⟨H1r, H1h⟩
  icases (qOwns_self_split id ms2).1 $$ Hown2 with ⟨Hself, Hown2⟩
  icases qOwns_other_ready id ms2 Hresp2 $$ Hown2 with ⟨H2r, Hother⟩
  ihave Hundo : iprop(msl ↦* (ms1 ++ nonself id ms2).map QMsg.loc -∗
      ownSliceCap Loc msl (DFrac.own 1) -∗
      ([∗list] q ∈ ms1 ++ nonself id ms2, msgOwn q.loc (readyDq q.st) q.st) -∗
      sl1 ↦* ms1.map QMsg.loc ∗ ownSliceCap Loc sl1 (DFrac.own 1) ∗
      ([∗list] q ∈ ms1, qOwn q) ∗
      ([∗list] q ∈ ms2.filter (fun q => !isSelfQ id q),
        msgOwn q.loc (DFrac.own (1 : Qp).half) q.st)) $$ [Hundo H1h]
  · iintro Hm Hc Ho
    icases BigSepL.bigSepL_append.1 $$ Ho with ⟨Ho1, Ho2⟩
    icases Hundo $$ Hm Hc with ⟨Hm, Hc⟩
    iframe Hm Hc
    isplitl [Ho1 H1h]
    · iapply qOwns_unready ms1; iframe Ho1 H1h
    · iapply readyDq_halves _ (fun q hq => Hresp2 q (List.mem_filter.1 hq).1) $$ Ho2
  ihave Hphys : ownRaftPhysReady cf rnv.raft' id s msl (ms1 ++ nonself id ms2) false $$
    [Hf_Term Hf_Vote Hf_readStates HreadStates_cap Hf_raftLog Hf_state Hf_lead Hf_witnessMsgs Hf_msgs
     Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hundo Hlog Hclose]
  · unfold ownRaftPhysReady
    iexists rss, sl1, sl2, ms1, ms2
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_witnessMsgs Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hundo Hlog Hclose
    ipureintro
    refine ⟨Houtbox, HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hxf, ?_⟩
    simp only [List.length_append]
    have := List.length_filter_le (fun q => !isSelfQ id q) ms2
    simp only [nonself]
    omega
  -- the messages' terms: within the ceiling (`OutTermOk`, the node's term below it)
  have Hsub : ∀ q ∈ ms1 ++ nonself id ms2, q ∈ ms1 ++ ms2 := by
    intro q Hq
    rcases List.mem_append.1 Hq with Hq | Hq
    · exact List.mem_append_left _ Hq
    · exact List.mem_append_right _ (List.mem_filter.1 Hq).1
  have Hmsgs_term : ∀ q ∈ ms1 ++ nonself id ms2, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc := by
    intro q Hq
    rw [Hpvoff.2.1]
    have := Hpvoff.2.2.1
    rcases Hout_term q (Hsub q Hq) with h | h <;> omega
  -- the `MsgReadIndex`s handed out: at most the outbox's read-index requests (2026-10-13)
  have Hrdc : rdCountM ((ms1 ++ nonself id ms2).map QMsg.st) ≤ rdCount s.outbox :=
    outboxRelP_rdCount _ _ _ _ Houtbox
  have Hprc : ((ms1 ++ nonself id ms2).filterMap (fun q => qProp q.st)).Subperm
      (propsOf s.outbox) :=
    outboxRelP_props _ _ _ _ Houtbox
  -- the committed entries handed out extend `delivered`: both are prefixes of the
  -- global committed log, and `delivered` is as long as the `applying` entries before `ce`
  have Hpre := ready_committed_prefix fp0 (s.logst.sents ++ s.logst.uents) ce s.logst.prev
    s.logst.committed s.logst.applying Hfp.1
    ⟨by have := Hwf2.2 Hsnap; omega, Hwf1.2.2⟩
    (by simp only [List.length_append]; push_cast; omega) (by omega) Hcepre
  ihave #Hcm' : isCommitted γ
      ((fp0 ++ (s.logst.sents ++ s.logst.uents)).take (uint.Z s.logst.applying).toNat ++ ce)
    $$ []
  · rw [show (toPState s).commit = s.logst.committed from rfl,
      show (toPState s).log = s.logst.sents ++ s.logst.uents from rfl]
    iapply isCommitted_mono _ _ _ Hpre.1 $$ Hcm
  ihave %Hagree := isCommitted_agree γ rs.delivered _ $$ Hdeliv Hcm'
  have Hdeq := eq_of_prefix_or _ _ _ Hagree (Hdlen.trans Hpre.2.symm)
  ihave #Hdeliv' : isCommitted γ (rs.delivered ++ ce) $$ []
  · rw [Hdeq]; iexact Hcm'
  -- `rd.SoftState`: `nil`, or the node's soft state, read-only
  ihave #Hrdsoft : iprop(⌜sp = null⌝ ∨ ∃ v : SoftState, sp ↦□ v) $$ []
  · iapply soft_or _ _ _ $$ Hsoftp
  -- `rd.ReadStates`: the node's `ReadState`s, read-only (`nil` if there are none)
  ihave #Hrdrs : readStatesPts RS s.rd.states $$ []
  · rw [← HRS]
    by_cases He : s.rd.states = []
    · rw [ite_pos' He, He]; iapply readStatesPts_nil
    · rw [ite_neg' He]; iexact HreadStates
  ihave #Hrdrs' : iprop(∃ sts : List ReadStateM, readStatesPts RS sts ∗ ⌜sts = [] → s.rd.states = []⌝)
    $$ []
  · iexists s.rd.states
    iframe Hrdrs
    ipureintro; exact fun h => h
  ihave #Hrdhard := HHP
  icases HHP with ⟨%hrd, #HHP⟩
  ihave #Hmsgs_ok : iprop([∗list] q ∈ ms1 ++ nonself id ms2, isRaftMsg γ q.st) $$ []
  · iapply outboxRelP_isRaftMsgs γ (toPState s).outbox ms1 ms2 Houtbox _ Hsub Hnsout
      (fun h => (Hxf.2 (Hnl.1.trans h)).2.2) $$ Hout
  iapply HΦ $$ %(readyVal sp HP RS sents sce msl MS) %ce %(nextUnstable s.logst)
    %(ms1 ++ nonself id ms2) %s.rd.states %hrd
  simp only [named]
  isplitl [Hrn Hphys Hghost Hrest Hsteps Hsteps_cap Hce_cap]
  · unfold ownRawNodeReady
    iexists s, cf, fp, rnv, sv, hprev
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    rw [show s.outbox = (toPState s).outbox from rfl]
    iframe Hrn Hphys Hsdrf Hout Hsoft Hhard Hsteps Hsteps_cap Hdeliv' Hstrecs Hrdsoft Hrdrs' Hce
      Hce_cap Hents Hrdhard
    isplitl [Hghost Hrest]
    · iunfold ownStepGhost; iframe Hghost Hrest
    ipureintro
    exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, HunpS, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
      Hrs_clb,
      ⟨Hrnfl.1, Int.not_lt.1 fun h => by
        obtain ⟨_, _, Hm, -⟩ := Hrnfl.2 h; rw [Hsteps0] at Hm; simp at Hm⟩,
      ceOk_of_prefix s.logst ce Hidx ⟨by have := Hwf2.2 Hsnap; omega, Hwf1.2.2⟩ (by omega) Hcepre,
      trivial, Hrdc, Hprc, Hnsout⟩
  isplitr
  · iexact Hce
  isplitr
  · iexact Hdeliv'
  isplitr
  · iexact Hents
  isplitl [Hmsgs]
  · iexact Hmsgs
  isplitl [Hmsgs_cap]
  · iexact Hmsgs_cap
  isplitl [H1r H2r]
  · iapply BigSepL.bigSepL_append.2; iframe H1r H2r
  isplitr
  · iexact Hmsgs_ok
  isplitr
  · ipureintro; exact Hmsgs_term
  isplitr
  · iintro H1 H2 H3 H4
    iapply ownRawNodeReady_abandon γ rn id rs (readyVal sp HP RS sents sce msl MS) ce
      (nextUnstable s.logst) (ms1 ++ nonself id ms2) Hsteps0 Hunp0 $$ H1 H2 H3 H4
  isplitr
  · ipureintro; first | rfl | trivial
  isplitr
  · iexact Hrdrs
  isplitr
  · rw [← toPState_rd_states s]
    iexact Hrs_ok
  · iexact HHP

end proof

end EtcdGrove
end Perennial
