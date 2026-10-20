/-
**The server's side of the raft network** (D21 stage M2, 2026-10-19; `notes/decisions.md`, "D21 M2:
the network contract designed"). Lean-first (no Rocq counterpart).

* `srvProcOk γn s`: what `EtcdServer.Process` (and the reports) read of the server `s`, read-only:
  its logger, member id, cluster, stats and its raft wrapper's node with the node's inbound
  methods (`rnStepIfc`), and the network's payload the server's (`srvNet`). `NewServer` has it
  before the transport starts (the wrapper's fields split off early, `rnFixed_split`), which is
  when the transport may start calling `Process`.
* `stepP_of_recv`: a message the network delivers to the server (`netRecv`) is what raft's
  `node.Step` takes (`stepP`): a forwarded proposal (`fwdP`, the copy owned) or a network message
  (`netP`, the receiver's `NetMsgOk` from the sender's `SentMsgOk`, raft's clause on every
  message a `Ready` hands out, D21g (A)).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the inbound path reads of the server `s`**, member `id` (persistent; see the file
header), in the network `γn` whose payload is the server's (`srvNet` at the node's raft and budget names), the
cluster in raft's no-snapshot mode, booted from a non-empty log, and (2026-10-19, D22 S-a) in its
no-transfer mode (`RaftNames.reNoXfer`, until then the no-snapshot mode's). -/
def srvProcOk (γn : NetNames GF) (s : Loc) (id : w64) : IProp GF :=
  iprop(∃ (l c st : Loc) (γ : RNNames),
    srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗ srvMemberIDAddr s ↦□ id ∗ ⌜γ.id = id⌝ ∗
    srvClusterAddr s ↦□ c ∗ membership.isRaftCluster c ∗
    srvStatsAddr s ↦□ st ∗ ⌜st ≠ null⌝ ∗
    rnNodeAddr (srvRAddr s) ↦□ rnNodeIface γ ∗ rnStepIfc γ (rnNodeIface γ) ∗
    ⌜γn.N = srvNet γ.node.raft γ.node.bud ∧ γ.node.raft.reNoSnap = true ∧
      γ.node.raft.reBoot ≠ [] ∧ γ.node.raft.reNoXfer = true⌝)

instance srvProcOk_persistent (γn : NetNames GF) (s : Loc) (id : w64) :
    Persistent (srvProcOk (GF := GF) γn s id) := by
  unfold srvProcOk; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A message raft sent, not a snapshot: every abstraction of its type is sent (`isMessage`). -/
theorem isRaftMsg_isMessages (γ : RaftNames) (st : MsgSt) (Hns : st.msg.Type' ≠ MsgSnap) :
    isRaftMsg (GF := GF) γ st ⊢
      □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗
        isMessage γ (absMsg ty st.msg st.ents st.ctx)) := by
  iintro #Hr
  iunfold isRaftMsg at Hr
  icases Hr with ⟨-, -, %a, %Habs, #Hl⟩
  imodintro
  iintro %ty %Hty
  rcases Habs with ⟨Hn, -⟩ | ⟨ty', Hty', -, rfl⟩ | ⟨sv, Hsn, -, -⟩
  · rw [Hty] at Hn; cases Hn
  · rw [Hty] at Hty'; cases Hty'
    simp only [Option.toList_some]
    ihave #Hx := (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessageC (GF := GF) γ x)).1 $$ Hl
    iapply isMessageC_isMessage $$ Hx
  · exact absurd (mtypeOf_Snap _ Hsn) Hns

/-- **A delivered message is what `node.Step` takes** (see the file header): at the node `γ.id`
whose network payload is the server's. -/
theorem stepP_of_recv (γn : NetNames GF) (γ : RNNames)
    (HN : γn.N = srvNet γ.node.raft γ.node.bud) (hns : γ.node.raft.reNoSnap = true)
    (hboot : γ.node.raft.reBoot ≠ [])
    -- (2026-10-19, D22 S-a) `SentMsgOk` is of the no-transfer mode (D22 S-a to S-c: of both)
    (hnx : γ.node.raft.reNoXfer = true) {γd : GName} (ml : Loc) :
    netRecv (GF := GF) γn γ.id γd ml ⊢ |==> stepP γ.node γ.id ml := by
  obtain ⟨N, g, dir⟩ := γn
  simp only at HN
  subst HN
  iintro Hr
  iunfold netRecv at Hr
  simp only [srvNet]
  icases Hr with ⟨%st, %st', Hm, %Hw, #HP, ⟨HO, Htk⟩, -⟩
  obtain ⟨⟨Hmsg, Hents, Hsnap, Hctx⟩, Hto⟩ := Hw
  icases HP with ⟨#Hrm, #Htl⟩
  ihave %Hns := isRaftMsg_not_snap γ.node.raft hns st $$ Hrm
  ihave #Hrm' := Hrm
  iunfold isRaftMsg at Hrm'
  icases Hrm' with ⟨-, %Hsent0, -⟩
  have Hsent := Hsent0 hnx
  have Htn := SentMsgOk.ne_timeoutNow Hsent
  ihave #Hmsgs := isRaftMsg_isMessages γ.node.raft st Hns $$ Hrm
  -- the copy's state is the message's but for its responses
  have Hst' : st' = { st with resps := st'.resps } := by
    cases st; cases st'; simp_all
  rw [Hst']
  unfold stepP
  by_cases Hp : st.msg.Type' = MsgProp
  · -- a forwarded proposal: the copy owned
    iright
    unfold fwdP
    imodintro
    iexists { st with resps := st'.resps }
    isplitl [Hm]
    · rw [← Hst']; iapply msgPtsC_cap_any $$ Hm
    isplitr
    · ipureintro; exact Hp
    isplitr
    · ihave #H := Hmsgs $$ %MsgType.propose %(by rw [Hp]; exact mtypeOf_MsgProp)
      -- a proposal's protocol fact ignores the context (raft's `isMessage_propose_ctx`, stated
      -- under a storage model this file does not fix)
      unfold isMessage absMsg absMsgFrom at *
      iexact H
    -- (2026-10-19, D21 M6) its tickets, delivered once
    unfold stTks
    rw [if_pos Hp]
    simp only [Hents]
    iexact Htk
  · imod msgPtsC_persist_els $$ Hm with Hm
    imod tickCred_zero γ.node.bud with Htc
    imodintro
    ileft
    unfold netP
    iexists { st with resps := st'.resps }
    isplitl [Hm]
    · rw [← Hst']; iapply msgPtsC_cap_any $$ Hm
    isplitr
    · ipureintro
      exact NetMsgOk.of_sent Hsent Hto Hp
    isplitr
    · ipureintro; exact ⟨fun _ => hboot, fun h => absurd h (SentMsgOk.ne_transferLeader Hsent), Hns⟩
    simp only [ite_eq_right Htn]
    iframe Hmsgs Htl HO Htc

end lemmas

end EtcdGrove
end Perennial
