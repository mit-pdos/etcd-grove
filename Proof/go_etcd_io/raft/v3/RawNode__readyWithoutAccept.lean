/- `RawNode.readyWithoutAccept`, Lean-first (2026-10-10): the first half of the proof of
`RawNode.Ready` (`RawNode__Ready.lean` until then, itself the port of
election_proof/proof_RawNode__Ready.v at 857d09190, finished in Lean), up to the call of
`acceptReady`, closed into `ownRawNodeReady`. The facts the application gets with the
`Ready` -- the committed entries extending `delivered`, the messages' `isRaftMsg` -- were
proved at the end of `Ready`'s proof; they come here, since `node.go` hands the `Ready` out
before accepting it.

Lean notes: `readyWithoutAccept`'s `rd` is tracked as `readyVal` (one field per argument).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.raftLog__nextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__nextCommittedEnts
public import Spec.go_etcd_io.raft.v3.SoftState__equal
public import Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.MustSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- `if_pos`/`if_neg` (deprecated in core under those names). -/
private theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := ite_eq_left_of_eq_true _ _ (eq_true h)

private theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := ite_eq_right_of_eq_false _ _ (eq_false h)

section helpers
variable [FfiSyntax]

/-- The committed entries handed out sit in the global log right after its first
`applying` entries: `fp` is the log below the boundary `prev` (`FullOk`), `es` the log
after it. -/
theorem ready_committed_prefix (fp es ce : List raftpb.Entry) (prev : entryID) (cm apg : w64)
    (Hfp : (fp.length : Int) = uint.Z prev.index')
    (Hle : uint.Z prev.index' ≤ uint.Z apg ∧ uint.Z apg ≤ uint.Z cm)
    (Hcm : uint.Z cm ≤ uint.Z prev.index' + (es.length : Int))
    (Hnw : uint.Z cm + 1 < 2 ^ 64)
    (Hce : ce <+: (plogFrom prev es (apg + W64 1)).take (uint.Z cm - uint.Z apg).toNat) :
    (fp ++ es).take (uint.Z apg).toNat ++ ce <+: (fp ++ es).take (uint.Z cm).toNat ∧
    ((fp ++ es).take (uint.Z apg).toNat).length = (uint.Z apg).toNat := by
  unfold plogFrom at Hce
  have Hk : (uint.Z (apg + W64 1) - uint.Z prev.index' - 1).toNat
      = (uint.Z apg).toNat - fp.length := by word
  rw [Hk] at Hce
  rw [List.take_append, List.take_append,
    List.take_of_length_le (l := fp) (by omega), List.take_of_length_le (l := fp) (by omega)]
  refine ⟨?_, by simp only [List.length_append, List.length_take]; word⟩
  rw [List.append_assoc, List.prefix_append_right_inj]
  have Hsplit : (uint.Z cm).toNat - fp.length
      = ((uint.Z apg).toNat - fp.length) + (uint.Z cm - uint.Z apg).toNat := by omega
  rw [Hsplit, List.take_add, List.prefix_append_right_inj]
  exact Hce

/-- `delivered` is the committed log's prefix up to `applying`: of the same length as
`pre` and comparable with `pre ++ ce` (`isCommitted_agree`), it is `pre`. -/
theorem eq_of_prefix_or {α : Type _} (l pre ce : List α) (H : l <+: pre ++ ce ∨ pre ++ ce <+: l)
    (Hl : l.length = pre.length) : l = pre := by
  rcases H with H | H
  · exact (List.prefix_of_prefix_length_le H (List.prefix_append pre ce) (by omega)).eq_of_length Hl
  · have Hle := H.length_le
    simp only [List.length_append] at Hle
    have Hce : ce = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst Hce
    rw [List.append_nil] at H
    exact (H.eq_of_length Hl.symm).symm

/-- The messages of `msgsAfterAppend` that `readyWithoutAccept` hands out (`To ≠ id`;
`acceptReady` keeps those to oneself to step, `selfmsgs`). -/
def nonself (id : w64) (ms : List raftpb.Message) : List raftpb.Message :=
  ms.filter (fun m => decide (m.To' ≠ id))

theorem nonself_take_succ (id : w64) (ms : List raftpb.Message) (n : Nat)
    (mm : raftpb.Message) (Hl : ms[n]? = some mm) :
    nonself id (ms.take (n + 1)) =
      nonself id (ms.take n) ++ (if mm.To' = id then [] else [mm]) := by
  unfold nonself
  rw [List.take_add_one, Hl]
  by_cases h : mm.To' = id <;> simp [List.filter_append, h]

theorem nonself_cons (id : w64) (m : raftpb.Message) (ms : List raftpb.Message) :
    nonself id (m :: ms) = if m.To' = id then nonself id ms else m :: nonself id ms := by
  by_cases h : m.To' = id <;> simp [nonself, h]

/-- The `Ready` `readyWithoutAccept` builds, field by field (`Snapshot` stays zero and
`ReadStates` nil: no snapshot is pending, no read state is queued). -/
abbrev readyVal (sp : Loc) (hs : raftpb.HardState) (ents ce msgs : GoSlice) (ms : Bool) :
    Ready :=
  Ready.mk sp hs slice.nil ents (zero_val raftpb.Snapshot) ce msgs ms

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- The messages handed out: each one's abstraction was in the outbox, whose messages
are all `isMessage` (`ownRaftGhost_outbox`). -/
theorem msgs_ok_list (γ : RaftNames) (o : List Msg) (ms : List raftpb.Message)
    (as_ : List (Option Msg)) (HP : ∀ a ∈ as_, ∀ x, a = some x → x ∈ o) :
    ⊢ ([∗list] x ∈ o, isMessage (GF := GF) γ x) -∗
      ([∗list] _k ↦ m;a ∈ ms;as_, msgAbs (GF := GF) m a) -∗
      [∗list] m ∈ ms, isRaftMsg (GF := GF) γ m := by
  induction ms generalizing as_ with
  | nil => iintro _ _; iempintro
  | cons m ms IH =>
    iintro #Ho H
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ H with ⟨%a, %as', %Has, #Hm, H⟩
    subst Has
    isplitl []
    · unfold isRaftMsg
      iexists a
      iframe Hm
      cases a with
      | none => simp only [Option.toList_none]; iempintro
      | some x =>
        simp only [Option.toList_some]
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).2
        iapply BigSepL.bigSepL_mem (Φ := fun x => isMessage (GF := GF) γ x)
          (HP _ List.mem_cons_self x rfl) $$ Ho
    · iapply IH as' (fun b Hb => HP b (List.mem_cons_of_mem _ Hb)) $$ Ho H

theorem nonself_sepL (id : w64) (ms : List raftpb.Message) (Φ : raftpb.Message → IProp GF) :
    ⊢ ([∗list] m ∈ ms, Φ m) -∗ [∗list] m ∈ nonself id ms, Φ m := by
  induction ms with
  | nil => iintro _; simp only [nonself, List.filter_nil]; iempintro
  | cons m ms IH =>
    iintro ⟨Hm, H⟩
    rw [nonself_cons]
    by_cases h : m.To' = id
    · simp only [h, ↓reduceIte]
      iapply IH $$ H
    · simp only [h, ↓reduceIte]
      isplitl [Hm]
      · iexact Hm
      · iapply IH $$ H

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

theorem RawNode.readyWithoutAccept.wp_proof
    (wp_raftLog_nextUnstableEnts : raftLog.nextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_nextCommittedEnts : raftLog.nextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_MustSync : MustSync.spec (GF := GF) (hG := hG)) :
    RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hsteps0 Hunp0
  wp_start as H
  iNamed H
  iNamed Hrn
  have HunpS : s.logst.unpersisted = [] := Hunp ▸ Hunp0
  -- the previous `SoftState`/`HardState`, as records (no spec states them)
  obtain ⟨soft0, Hsoftv⟩ : ∃ soft0 : SoftSt, sv = softstateVal soft0 :=
    ⟨⟨sv.Lead', sv.RaftState'⟩, by cases sv; rfl⟩
  obtain ⟨hard0, Hhard⟩ : ∃ hard0 : HardSt, rnv.prevHardSt' = hardstateVal hard0 :=
    ⟨hsAbs rnv.prevHardSt', by generalize rnv.prevHardSt' = h; cases h; rfl⟩
  ihave %Hlen0 := BigSepL2.bigSepL2_length $$ Hpend
  rw [Hsteps0] at Hlen0
  cases steps with
  | cons _ _ => simp at Hlen0
  | nil =>
  -- ghost facts, read before anything moves
  ihave #Hout := ownRaftGhost_outbox _ _ _ $$ Hghost
  icases ownRaftGhost_committed _ _ _ $$ Hghost with ⟨%fp, %Hfp, #Hcm⟩
  icases ownRaftPhys_view γ.reCfg rnv.raft' id s $$ Hphys with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf1, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hwf2, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hwf3, Hlog⟩
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
  have Hhs_iff : (s.term = (hardstateVal hard0).Term' ∧ s.vote = (hardstateVal hard0).Vote' ∧
      s.logst.committed = (hardstateVal hard0).Commit') ↔ nodeHardstate s = hard0 := by
    constructor
    · intro ⟨H1, H2, H3⟩
      show HardSt.mk _ _ _ = _
      rw [H1, H2, H3]; rfl
    · intro H
      rw [← H]; exact ⟨rfl, rfl, rfl⟩
  -- `r.softState()`, compared with `prevSoftSt`; the two arms joined
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_SoftState_equal $$ [$softSt $Hsoft] as ⟨softSt, -⟩
  wp_join iprop(∃ sp, rd_ptr ↦ readyVal sp (zero_val raftpb.HardState) sents sce sl1 false ∗
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
  -- `r.hardState()`, compared with `prevHardSt`; the two arms joined
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  rw [Hlv.1]
  clear Hlv
  wp_apply wp_isHardStateEqual
  rw [Hhard]
  wp_join iprop(rd_ptr ↦ readyVal sp (if nodeHardstate s = hard0 then zero_val raftpb.HardState
      else hardstateVal (nodeHardstate s)) sents sce sl1 false) with [rd hardSt] as rd
  · rw [ite_pos' (Hhs_iff.1 Hif)]
    iexact rd
  · rw [ite_neg' (fun Hc => Hif (Hhs_iff.2 Hc))]
    simp only [hardstateVal, nodeHardstate, readyVal]
    iexact rd
  wp_apply wp_raftLog_hasNextUnstableSnapshot $$ [Hlog] as %bsn ⟨Hlog, %Hbsn⟩
  · iframe Hlog
  rw [Hbsn Hsnap]
  wp_auto
  ihave %Hel := ownSlice_len _ _ _ $$ Hents
  rw [Hrs]
  wp_auto
  -- `MustSync(r.hardState(), rn.prevHardSt, len(rd.Entries))`
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  rw [Hlv.1, Hhard]
  clear Hlv
  wp_apply wp_MustSync
  rw [Hasync]
  wp_auto
  generalize HHS : (if nodeHardstate s = hard0 then zero_val raftpb.HardState
      else hardstateVal (nodeHardstate s)) = HS
  generalize HMS : decide (¬sents.len = W64 0 ∨ ¬s.vote = hard0.vote ∨
      ¬s.term = hard0.term) = MS
  -- `for _, m := range r.msgsAfterAppend { if m.To != r.id { rd.Messages =
  -- append(rd.Messages, m) } }`: in place, into `r.msgs`' capacity
  ihave IH : iprop(∃ (n : w64) (msl : GoSlice) (mv : raftpb.Message),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "rd" ∷ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      "Hmsgs" ∷ msl ↦* (ms1 ++ nonself id (ms2.take (sint.nat n))) ∗
      "Hmsgs_cap" ∷ ownSliceCap raftpb.Message msl (DFrac.own 1) ∗
      "HmsgsAA" ∷ sl2 ↦* ms2 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms2.length : Int)⌝)
    $$ [i m rd Hmsgs Hmsgs_cap HmsgsAA]
  · iexists W64 0, sl1, zero_val raftpb.Message
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.take_zero]
    simp only [nonself, List.filter_nil, List.append_nil, named]
    iframe i m Hmsgs Hmsgs_cap HmsgsAA
    isplitl [rd]
    · iexact rd
    · ipureintro; word
  wp_for IH
  ihave %Hl2 := ownSlice_len _ _ _ $$ HmsgsAA
  wp_if_destruct
  · list_elem ms2 (sint.nat n) as mm
    rw [ite_pos' (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl2.len from ⟨Hn.1, Hif⟩)]
    wp_apply wp_load_slice_index sl2 (sint.Z n) ms2 (DFrac.own 1) mm Hn.1 $$ [HmsgsAA]
      with HmsgsAA
    · iframe
      ipureintro
      exact Hmm_lookup
    have HnS : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_if_destruct
    · -- to oneself: kept for `acceptReady`
      wp_for_post
      iframe
      iexists n + W64 1, msl, mm
      -- (`wp_if_destruct` substituted `id := mm.To'`)
      rw [HnS, nonself_take_succ _ _ _ _ Hmm_lookup, ite_pos' rfl, List.append_nil]
      iframe
      ipureintro; word
    · -- to another node: handed out
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %msl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hmsgs $Hmsgs_cap $Hsl1] as %msl' ⟨Hmsgs, Hmsgs_cap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, msl', mm
      rw [HnS, nonself_take_succ _ _ _ _ Hmm_lookup, ite_neg' Hif, List.append_assoc]
      iframe
      ipureintro; word
  -- the loop is done: every message of `msgsAfterAppend` seen
  rw [List.take_of_length_le (l := ms2) (i := sint.nat n) (by word)]
  -- the raft struct, without the outbox's contents (now `rd.Messages`)
  ihave Hphys : ownRaftPhysReady γ.reCfg rnv.raft' id s $$
    [Hf_id Hf_Term Hf_Vote Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs Hf_msgsAA
     HmsgsAA HmsgsAA_cap Hlog Hclose]
  · unfold ownRaftPhysReady
    iexists rss, sl1, sl2, ms1, ms2
    simp only [named]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs Hf_msgsAA
      HmsgsAA HmsgsAA_cap Hlog Hclose Houtbox
    ipureintro; exact ⟨Hrs, HmsgsAA_ok⟩
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Hperm, #Hb1, #Hb2⟩
  obtain ⟨Hps, Hwfs⟩ := Hrel
  subst Hps
  have Hin_out : ∀ a ∈ as1 ++ as2, ∀ x, a = some x → x ∈ s.outbox := by
    intro a Ha x Hx
    subst Hx
    apply Hperm.mem_iff.2
    simp only [absList, ← List.filterMap_append]
    exact List.mem_filterMap.2 ⟨some x, Ha, rfl⟩
  -- the committed entries handed out extend `delivered`: both are prefixes of the
  -- global committed log, and `delivered` is as long as the `applying` entries before `ce`
  have Hpre := ready_committed_prefix fp (s.logst.sents ++ s.logst.uents) ce s.logst.prev
    s.logst.committed s.logst.applying Hfp.1
    ⟨by have := Hwf2.2 Hsnap; omega, Hwf1.2.2⟩
    (by simp only [List.length_append]; push_cast; omega) (by omega) Hcepre
  ihave #Hcm' : isCommitted γ
      ((fp ++ (s.logst.sents ++ s.logst.uents)).take (uint.Z s.logst.applying).toNat ++ ce)
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
  iapply HΦ $$ %(readyVal sp HS sents sce msl MS) %ce %(nextUnstable s.logst)
    %(ms1 ++ nonself id ms2)
  simp only [named]
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hce_cap]
  · unfold ownRawNodeReady
    iexists s, toPState s, rnv, sv
    simp only [named]
    iframe Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hdeliv' Hstrecs Hrdsoft Hce Hce_cap
    ipureintro
    exact ⟨⟨rfl, Hwfs⟩, Hin, Hasync, Hdlen, HunpS, Hsnap, Htrm, Hstor, ⟨trivial, trivial⟩, Hcepre, trivial⟩
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
  isplitr
  · iapply (BigSepL.bigSepL_append (Φ := fun _ m => isRaftMsg (GF := GF) γ m)).2
    isplitr
    · iapply msgs_ok_list γ (toPState s).outbox ms1 as1
        (fun a Ha => Hin_out a (List.mem_append_left _ Ha)) $$ Hout Hb1
    · iapply nonself_sepL id ms2 (fun m => isRaftMsg (GF := GF) γ m)
      iapply msgs_ok_list γ (toPState s).outbox ms2 as2
        (fun a Ha => Hin_out a (List.mem_append_right _ Ha)) $$ Hout Hb2
  ipureintro; exact ⟨trivial, trivial⟩

end proof

end EtcdGrove
end Perennial
