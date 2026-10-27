/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/deliver.lean`. Lean-first (no
Rocq counterpart).

raft v3.7 (2026-10-16, stage R6b): each message is a `*pb.Message` the `Ready` handed out owned
(`msgOwn q.loc (readyDq q.st) q.st`); `deliverable` and the getters read it, `m.Entries =
append([]*pb.Entry(nil), m.Entries...)` replaces its entries slice by a fresh copy with its
capacity (`msgPtsC_store_Entries`), and `Node.Step` takes it for good (`stepP_deliverable`).

The message stepped is the wire's copy (`cluster.go`, 2026-10-16): a fresh `pb.Message` sharing
`m`'s scalar cells (persistent `cellRO`s, read at whatever fraction the `Ready` gave: a response
comes at half, D8) and its context bytes, with its own entries slice (the receiver may adopt it)
and no snapshot or responses; owned at `1` (`msgPtsC_of_struct`), it is what `Node.Step` takes
for good (`stepP_deliverable`), while raft's own object stays as `Ready` handed it out.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.transfers__take
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.deliverable
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [StorageModel GF]

omit [StorageModel GF] in
/-- (D22 S-r) A `nil` snapshot pointer, of no snapshot. -/
theorem snapOpt_none_null (p : Loc) (dq : DFrac) (s : Option SnapshotM) (h : s = none) :
    snapOpt (GF := GF) p dq s ⊢ ⌜p = null⌝ := by
  subst h; simp only [snapOpt]; exact .rfl

omit [StorageModel GF] in
theorem snapOpt_some_iff (p : Loc) (dq : DFrac) (s : Option SnapshotM) (sv : SnapshotM)
    (h : s = some sv) : snapOpt (GF := GF) p dq s ⊣⊢ ownSnapM p dq sv := by
  subst h; simp only [snapOpt]; exact .rfl

omit [StorageModel GF] in
theorem snapOpt_null_none (dq : DFrac) (s : Option SnapshotM) (h : s = none) :
    ⊢ snapOpt (GF := GF) (null : Loc) dq s := by
  subst h; simp only [snapOpt]; ipureintro; trivial

set_option hygiene false in
/-- The tail of an iteration that steps the wire's copy of the message `q` into its node `n`:
the copy's struct built from `m`'s fields' loads (`iNamed`), the appended entries slice and
(D22 S-r) the snapshot's clone `snc` (`Hsnc`), owned (`msgPtsC_of_struct`), made `stepP`
(`Draft.stepIn_intro`, `deliverable_step`), `Node.Step`. Expects the tick credit `Htc`, the
message's credits `Hc1`, `Hmok`, `HisNode`, and the loop's `Hk1`. -/
local macro "deliver_tail " snc:term : tactic =>
  `(tactic| (
    try wp_auto
    wp_apply wp_slice_append slice.nil ([] : List Loc) es els DFrac.discard $$ [Hes]
      as %s' ⟨Hs, Hcap, -⟩
    · iframe Hes
      isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    rw [List.nil_append]
    -- `wp_auto` allocated the copy (`«$r0_ptr»`, its struct `«$r0»`) and stored it in `c`
    imod msgPtsC_of_struct «$r0_ptr»
        (⟨zero_val _, pty, pto, pfr, pte, plt, pix, s', pco, pvo, $snc, prj, prh, cs, slice.nil,
          slice.nil, 0⟩ : raftpb.Message)
        (DFrac.own 1) true els ⟨q.st.msg, q.st.ents, q.st.snap, q.st.ctx, []⟩ ⊤ rfl
        $$ [«$r0» Hs Hcap Hsnc] with Hmc
    · simp only [↓reduceIte]
      iframe «$r0» Hs Hcap Hsnc
      iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs
      iapply ownSlice_nil
    wp_apply context.wp_Background
    ihave #Hbg := nodeCtx_background (GF := GF) bgCd
    have Hsteps := deliverable_step q.st.msg.To' q.st Hd rfl
    imod Draft.stepIn_intro γ kvRaftN q.st.msg.To' «$r0_ptr» q.st Hsteps.1 Hsteps.2.1 Hsteps.2.2 rfl
      $$ [Hmok Hmc Hc1 Htc] with Hstep
    · iframe Hmok Hmc Hc1 Htc
    wp_apply +noauto wp_node_Step n γ kvRaftN q.st.msg.To' «$r0_ptr» context.backgroundCtxVal bgCd
      $$ [Hstep] as %err -
    · iframe
      iframe HisNode Hbg
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, q.loc
    rw [Hk1]
    iframe
    ipureintro; constructor <;> word))

set_option hygiene false in
/-- The wire's copy of the message `q` (`Hmq`): `m`'s fields taken apart (`iNamed`). The proof
then clones its snapshot, if any (D22 S-r), and runs `deliver_tail`. -/
local macro "deliver_pre" : tactic =>
  `(tactic| (
    iunfold msgPtsC at Hmq
    iNamed Hmq
    wp_auto))

theorem deliver.wp_proof (wp_deliverable : deliverable.spec (GF := GF) (hG := hG))
    (wp_take : transfers.take.spec (GF := GF) (hG := hG))
    (wp_node_Step : Draft.node.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    deliver.spec (GF := GF) (hG := hG) := by
  intro γ peers tr P msl ms
  wp_start as ⟨#Hpeers, #HP, #Htr, Hms, Hmsok⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  ihave %Hmslen := ownSlice_len $$ Hms
  simp only [List.length_map] at Hmslen
  ihave IH : iprop(∃ (k : w64) (mv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hms" ∷ msl ↦* ms.map QMsg.loc ∗
      "Hmsok" ∷ ([∗list] q ∈ ms.drop (sint.nat k),
        msgOwn q.loc (readyDq q.st) q.st ∗ Draft.sentMsg γ kvRaftN q.st ∗
          Draft.msgCredits γ kvRaftN q.st) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝) $$ [i m Hms Hmsok]
  · iexists W64 0, _
    iframe i m Hms
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe Hmsok
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ms.length := by word
    obtain ⟨q, Hq⟩ : ∃ q, ms[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hql : (ms.map QMsg.loc)[sint.nat k]? = some q.loc := by
      rw [List.getElem?_map, Hq]; rfl
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z msl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index msl (sint.Z k) _ (DFrac.own 1) q.loc Hk.1 $$ [Hms] as Hms
    · iframe Hms; ipureintro; exact Hql
    -- the message's resources
    have Hdrop : ms.drop (sint.nat k) = q :: ms.drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]
      rw [List.getElem?_eq_getElem Hlt] at Hq
      rw [Option.some.inj Hq]
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hdrop]
    icases Hmsok with ⟨⟨Hmq, #Hmok, Hc1⟩, Hmsok⟩
    wp_apply wp_deliverable q.loc (readyDq q.st) DFrac.discard false q.st $$ [$Hmq] as %b ⟨Hmq, %Hb⟩
    cases b
    · wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, q.loc
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
    have Hd := Hb rfl
    wp_auto
    -- `peers[m.GetTo()]`
    wp_apply wp_GetTo.1 q.loc (readyDq q.st) DFrac.discard false q.st $$ [$Hmq] as Hmq
    wp_apply wp_map_lookup2 go.uint64 _ peers P q.st.msg.To' DFrac.discard $$ Hpeers as -
    cases HPt : P !! q.st.msg.To' with
    | none =>
      try simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, q.loc
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
    | some nd =>
      ihave #Hpeer := BigSepM.bigSepM_lookup (Φ := fun id nd => kvPeerOk (GF := GF) γ id nd)
        HPt $$ HP
      unfold kvPeerOk
      icases Hpeer with ⟨%n, %Hnd, #HisNode⟩
      subst Hnd
      try simp only [Option.isSome_some, Option.getD_some, _root_.decide_true, Bool.not_true]
      wp_auto
      -- `m.GetType() == pb.MsgTimeoutNow && !tr.take()`
      wp_apply wp_GetType.1 q.loc (readyDq q.st) DFrac.discard false q.st $$ [$Hmq] as Hmq
      -- a `MsgTimeoutNow`: a tick credit from the transfer budget, or dropped
      by_cases Htn : q.st.msg.Type' = W32 14
      · rw [decide_eq_true Htn]
        wp_auto
        wp_apply wp_take γ tr $$ [$Htr] as %b Hb
        cases b
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, q.loc
          rw [Hk1]
          iframe
          ipureintro; constructor <;> word
        wp_auto
        ihave Htc : Draft.tickCredit γ (if q.st.msg.Type' = MsgTimeoutNow then 1 else 0) $$ [Hb]
        · have Htn' : q.st.msg.Type' = MsgTimeoutNow := Htn
          rw [ite_eq_left Htn']
          simp only [↓reduceIte]
          iexact Hb
        deliver_pre
        by_cases Hsq : q.st.snap = none
        · ihave %Hpn := snapOpt_none_null ps _ q.st.snap Hsq $$ Hsn
          subst Hpn
          try rw [decide_eq_true rfl]
          try wp_auto
          ihave Hsnc := snapOpt_null_none (GF := GF) (DFrac.own 1) q.st.snap Hsq
          deliver_tail (null : Loc)
        · obtain ⟨sv, Hsq⟩ := Option.ne_none_iff_exists'.1 Hsq
          ihave Hsn := (snapOpt_some_iff ps _ q.st.snap sv Hsq).1 $$ Hsn
          icases ownSnapM_not_null ps _ sv $$ Hsn with ⟨Hsn, %Hpn⟩
          try rw [decide_eq_false Hpn]
          try wp_auto
          wp_apply wp_CloneSnapshot.1 ps _ sv $$ [$Hsn] as %snc ⟨-, Hsnc⟩
          try wp_auto
          ihave Hsnc := (snapOpt_some_iff snc (DFrac.own 1) q.st.snap sv Hsq).2 $$ Hsnc
          deliver_tail snc
      · rw [decide_eq_false Htn]
        wp_auto
        imod Draft.tickCredit_zero (GF := GF) γ with Htc0
        ihave Htc : Draft.tickCredit γ (if q.st.msg.Type' = MsgTimeoutNow then 1 else 0) $$ [Htc0]
        · have Htn' : ¬ q.st.msg.Type' = MsgTimeoutNow := Htn
          rw [ite_eq_right Htn']
          iexact Htc0
        deliver_pre
        by_cases Hsq : q.st.snap = none
        · ihave %Hpn := snapOpt_none_null ps _ q.st.snap Hsq $$ Hsn
          subst Hpn
          try rw [decide_eq_true rfl]
          try wp_auto
          ihave Hsnc := snapOpt_null_none (GF := GF) (DFrac.own 1) q.st.snap Hsq
          deliver_tail (null : Loc)
        · obtain ⟨sv, Hsq⟩ := Option.ne_none_iff_exists'.1 Hsq
          ihave Hsn := (snapOpt_some_iff ps _ q.st.snap sv Hsq).1 $$ Hsn
          icases ownSnapM_not_null ps _ sv $$ Hsn with ⟨Hsn, %Hpn⟩
          try rw [decide_eq_false Hpn]
          try wp_auto
          wp_apply wp_CloneSnapshot.1 ps _ sv $$ [$Hsn] as %snc ⟨-, Hsnc⟩
          try wp_auto
          ihave Hsnc := (snapOpt_some_iff snc (DFrac.own 1) q.st.snap sv Hsq).2 $$ Hsnc
          deliver_tail snc
  · iapply HΦ; itrivial

end proof

end kv
end EtcdGrove
end Perennial
