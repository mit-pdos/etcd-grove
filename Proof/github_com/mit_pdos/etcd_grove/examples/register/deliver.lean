/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/deliver.lean`. Lean-first (no
Rocq counterpart).

raft v3.7 (2026-10-16, stage R6b): each message is a `*pb.Message` the `Ready` handed out owned
(`msgOwn q.loc (readyDq q.st) q.st`); `deliverable` and the getters read it, `m.Entries =
append([]*pb.Entry(nil), m.Entries...)` replaces its entries slice by a fresh copy with its
capacity (`msgPtsC_store_Entries`), and `Node.Step` takes it for good (`stepP_deliverable`).

**A gap between raft's `Ready` and the register's transport (D8, Q3).** A response
(`MsgAppResp`, `MsgVoteResp`: `RespType`) comes out of `Ready` at half (`readyDq`: raft's
`acceptReady` still reads its `To`, `issues/raft-ready-messages-read-after-handout.md`), while the
store to `m.Entries` and `Node.Step`'s `msgIn` (the struct at `1`) need the whole message. The
in-process transport hands the sender's object to the receiver, which etcd's (marshalling)
transport never does; so the two steps cannot be verified for a response as the Go code stands,
and that branch is a `sorry` (below). The fixes are a Go change in `deliver` (step a fresh message
sharing the cells, which are persistent) or a finer `readyDq` in raft (half of `To` only).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.transfers__take
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.deliverable
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

/-- A message that is no response comes out of `Ready` whole. -/
theorem readyDq_nonresp (st : MsgSt) (h : ¬ RespType st.msg.Type') :
    readyDq st = DFrac.own 1 := by
  unfold readyDq; rw [ite_eq_right h]

set_option hygiene false in
/-- The tail of an iteration that steps the message `q` into its node `n`: the entries slice
copied (`msgPtsC_store_Entries`), the message made `stepP` (`stepP_deliverable`), `Node.Step`.
Expects `Hmq : msgOwn q.loc (DFrac.own 1) q.st`, the tick credit `Htc`, the read credit `Hc1`,
`Hmsg`, `Hmlb`, `HisNode`, and the loop's `Hk1`. -/
local macro "deliver_step" : tactic =>
  `(tactic| (
    icases msgPtsC_store_Entries q.loc DFrac.discard false q.st $$ Hmq
      with ⟨%es, %els, HEs, #Hes, #Hents, Hback⟩
    wp_auto
    wp_apply wp_slice_append slice.nil ([] : List Loc) es els DFrac.discard $$ [Hes]
      as %s' ⟨Hs, Hcap, -⟩
    · iframe Hes
      isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    rw [List.nil_append]
    ihave Hmq := Hback $$ %s' %(DFrac.own 1) HEs Hs Hcap
    wp_apply context.wp_Background
    imod stepP_deliverable γn q.st.msg.To' q.loc q.st Hd rfl $$ Hmsg Hmlb Hmq Hc1 Htc with Hstep
    wp_apply +noauto wp_node_Step γn q.st.msg.To' n q.loc $$ [Hstep] as %err -
    · iframe
      iexact HisNode
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, q.loc
    rw [Hk1]
    iframe
    ipureintro; constructor <;> word))

theorem deliver.wp_proof (wp_deliverable : deliverable.spec (GF := GF) (hG := hG))
    (wp_take : transfers.take.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    deliver.spec (GF := GF) (hG := hG) := by
  intro γ bud peers tr P msl ms
  wp_start as ⟨#Hpeers, #HP, #Htr, Hms, Hmsok, Hcr⟩
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
        msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ q.st ∗ termLB bud q.st.msg.Term') ∗
      "Hcr" ∷ ([∗list] q ∈ ms.drop (sint.nat k),
        rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝) $$ [i m Hms Hmsok Hcr]
  · iexists W64 0, _
    iframe i m Hms
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe Hmsok Hcr
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
    icases Hmsok with ⟨⟨Hmq, #Hmok, #Hmlb⟩, Hmsok⟩
    icases Hcr with ⟨Hc1, Hcr⟩
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
      ihave #Hpeer := BigSepM.bigSepM_lookup (Φ := fun id nd => peerOk (GF := GF) γ bud id nd)
        HPt $$ HP
      unfold peerOk
      icases Hpeer with ⟨%γn, %n, %Hnd, #HisNode⟩
      obtain ⟨Hr, Hbud, rfl⟩ := Hnd
      ihave #Hmsg := raftMsg_deliverable γ q.st Hd $$ Hmok
      try simp only [Option.isSome_some, Option.getD_some, _root_.decide_true, Bool.not_true]
      wp_auto
      subst Hr Hbud
      -- `m.GetType() == pb.MsgTimeoutNow && !tr.take()`
      wp_apply wp_GetType.1 q.loc (readyDq q.st) DFrac.discard false q.st $$ [$Hmq] as Hmq
      -- **the gap** (file header): a response comes at half; `m.Entries = ...` and `Node.Step`
      -- need the message whole
      by_cases Hresp : RespType q.st.msg.Type'
      · sorry
      have Hdq : readyDq q.st = DFrac.own 1 := readyDq_nonresp q.st Hresp
      rw [Hdq]
      -- a `MsgTimeoutNow`: a tick credit from the transfer budget, or dropped
      by_cases Htn : q.st.msg.Type' = W32 14
      · rw [decide_eq_true Htn]
        wp_auto
        wp_apply wp_take γn.bud tr $$ [$Htr] as %b Hb
        cases b
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, q.loc
          rw [Hk1]
          iframe
          ipureintro; constructor <;> word
        wp_auto
        ihave Htc : tickCred γn.bud (if q.st.msg.Type' = MsgTimeoutNow then 1 else 0) $$ [Hb]
        · have Htn' : q.st.msg.Type' = MsgTimeoutNow := Htn
          rw [ite_eq_left Htn']
          simp only [↓reduceIte]
          iexact Hb
        deliver_step
      · rw [decide_eq_false Htn]
        wp_auto
        imod tickCred_zero (GF := GF) γn.bud with Htc0
        ihave Htc : tickCred γn.bud (if q.st.msg.Type' = MsgTimeoutNow then 1 else 0) $$ [Htc0]
        · have Htn' : ¬ q.st.msg.Type' = MsgTimeoutNow := Htn
          rw [ite_eq_right Htn']
          iexact Htc0
        deliver_step
  · iapply HΦ; itrivial

end proof

end register
end EtcdGrove
end Perennial
