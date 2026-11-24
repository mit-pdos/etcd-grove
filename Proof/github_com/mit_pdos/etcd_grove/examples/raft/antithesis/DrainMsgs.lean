/-
Lean-first (no Rocq counterpart). #33 S4: **a `Ready`'s messages as `Cluster.drain` hands them out**
(`Cluster__drain.lean`): a message to another node with `ReadyMsgShape` (`Sim/MsgShapeStmt.lean`,
`msgShape.stmt`), raft's shape (`SentMsgShape`, in the `Ready`'s `isRaftMsg`), its numbers within the
binding's bound (`readyMsgNums`) and its term within it, is in-flight (`NetFacts`: `netFacts_of_ready`),
and raft's certificate `isMessage` of its protocol reading (`isRaftMsg_isMessage'`); a `Ready`'s
entries and committed entries, slices of its normal log, are normal (`ents_normal`, `ce_normal`);
and the binding's relation at the node, read from the run's invariant (`drain_peek`), what
`msgShape.stmt` and `readyMsgNums` take.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRunLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShapeStmt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `AllNormal` is `Sim`'s `EntsNormal`. -/
theorem allNormal_iff (es : List EntryM) : AllNormal es ↔ AntSim.EntsNormal es := Iff.rfl

/-- A message's protocol reading, not a snapshot, is `absMsg` at its type. -/
theorem absMsgOf_cases {st : MsgSt} {q : Msg} (h : absMsgOf st = some q) (hns : q.ty ≠ .snap) :
    ∃ ty, mtypeOf st.msg.Type' = some ty ∧ q = absMsg ty st.msg st.ents st.ctx := by
  unfold absMsgOf at h
  split at h
  · cases h
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact absurd rfl hns
  · rename_i ty _ hty; cases h; exact ⟨ty, hty, rfl⟩

/-- A described type the network carries is one of `antStepTypes`. -/
theorem mtypeOf_antStep {t : w32} {ty : MsgType} (H : mtypeOf t = some ty) (h : AntSim.NetTy ty) :
    t ∈ antStepTypes := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false]
  unfold mtypeOf at H
  split at H <;> cases H <;> rename_i hk <;> rw [key _ hk] <;>
    (rcases h with h | h | h | h | h | h <;> cases h) <;> decide

/-- `MsgHeartbeatResp`'s described type. -/
theorem mtypeOf_hbResp {t : w32} {ty : MsgType} (H : mtypeOf t = some ty)
    (h : t = MsgHeartbeatResp) : ty = .heartbeatResp := by
  subst h; rw [mtypeOf_MsgHeartbeatResp] at H; exact (Option.some.inj H).symm

theorem antStepTypes_nx {t : w32} (h : t ∈ antStepTypes) :
    ¬ (t = MsgProp ∨ t = MsgReadIndex ∨ t = MsgTransferLeader) := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

theorem antStepTypes_net {t : w32} (h : t ∈ antStepTypes) : t ∈ netStepTypes := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- **A `Ready`'s message to another node is in flight** (`NetFacts`): its shape (`ReadyMsgShape`,
not a proposal), raft's (`SentMsgShape`: a nonzero term and sender, no responses), addressed to
another node (`ReadyOut`'s `To' ≠ id`), a voter, from a voter, its numbers within the bound. -/
theorem netFacts_of_ready {st : MsgSt} {q : Msg} {id : w64} (habs : absMsgOf st = some q)
    (hto : st.msg.To' ≠ id) (hsh : AntSim.ReadyMsgShape id q) (hp : q.ty ≠ .propose)
    (hdst : ∃ j : Fin 3, q.dst = AntSim.nodeId j) (hsrc : ∃ i : Fin 3, id = AntSim.nodeId i)
    (hsent : SentMsgShape st) (hnums : AntSim.MsgNums (2 ^ 61) q)
    (hterm : uint.Z st.msg.Term' < 2 ^ 61) : NetFacts st q := by
  obtain ⟨hs, hty, hctx, hnorm⟩ := hsh
  have hnty : AntSim.NetTy q.ty := hty.resolve_right hp
  have hns : q.ty ≠ .snap := by
    rcases hnty with h | h | h | h | h | h <;> rw [h] <;> decide
  obtain ⟨ty, hmt, rfl⟩ := absMsgOf_cases habs hns
  simp only [absMsg, absMsgFrom, Msg.mkV] at hs hnty hctx hnorm hdst hnums
  have htys : st.msg.Type' ∈ antStepTypes := mtypeOf_antStep hmt hnty
  obtain ⟨-, hf0, -, hst, -, -, -, hres⟩ := hsent
  have hstamp := antStepTypes_stamped htys
  have hnx := antStepTypes_nx htys
  have hnt : st.msg.Type' ≠ MsgTransferLeader := antStepTypes_ne_transfer htys
  have hft : st.msg.From' ≠ st.msg.To' := by rw [hs]; exact Ne.symm hto
  obtain ⟨i, hi⟩ := hsrc
  refine ⟨⟨?_, fun _ => ⟨rfl, hst hnx, hf0⟩, fun hu => absurd hu hstamp, fun h => absurd h hnt,
      fun _ => hft, fun _ _ => hft, fun h => absurd h hnt, fun _ => hft, hres⟩,
    htys, fun h => hctx (h.imp (fun h => by rw [h] at hmt; exact (Option.some.inj
      ((mtypeOf_MsgHeartbeat).symm.trans hmt)).symm) (mtypeOf_hbResp hmt)), hnorm, habs, hdst, ⟨i, by show st.msg.From' = _; rw [hs, hi]⟩,
    hterm, hnums.1, hnums.2.1, hnums.2.2.1, fun e he => (hnums.2.2.2 e he).1⟩
  exact antStepTypes_net htys

/-- A `Ready`'s entries, a suffix of its normal log, are normal. -/
theorem ents_normal {l es : List EntryM} (hl : AllNormal l) (h : ∃ k, l.drop k = es) :
    AllNormal es := by
  obtain ⟨k, rfl⟩ := h
  exact fun e he => hl e (List.mem_of_mem_drop he)

/-- A `Ready`'s committed entries, within its normal log, are normal. -/
theorem ce_normal {l d ce : List EntryM} (hl : AllNormal l) (h : d ++ ce <+: l) : AllNormal ce :=
  fun e he => hl e (h.subset (List.mem_append_right _ he))

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]

/-- Raft's shape of a message it hands out. -/
theorem isRaftMsg_shape (γ : RaftNames) (id : w64) (st : MsgSt) :
    isRaftMsg (GF := GF) γ id st ⊢ ⌜SentMsgShape st⌝ := by
  unfold isRaftMsg
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-- **Raft's certificate of a message it hands out** (`isMessage` of its protocol reading, not a
snapshot). -/
theorem isRaftMsg_isMessage' (γ : RaftNames) (id : w64) (st : MsgSt) (q : Msg)
    (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap) :
    isRaftMsg (GF := GF) γ id st ⊢ □ isMessage γ q := by
  obtain ⟨ty, hty, rfl⟩ := absMsgOf_cases habs hns
  have hns' : ty ≠ .snap := hns
  iintro #H
  unfold isRaftMsg
  icases H with ⟨-, ⟨%a, %Ha, #H⟩, -⟩
  rcases Ha with ⟨Hn, -⟩ | ⟨ty', Hty', -, rfl⟩ | ⟨sv, Hs, -, -⟩
  · rw [hty] at Hn; cases Hn
  · rw [hty] at Hty'; cases Hty'
    simp only [Option.toList_some]
    ihave #H := BigSepL.bigSepL_singleton.1 $$ H
    imodintro
    iapply isMessageC_isMessage $$ H
  · rw [hty] at Hs; cases Hs; exact absurd rfl hns'

variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem setV_self {V : Fin 3 → AntSim.NodeView} {j : Fin 3} {v : AntSim.NodeView} (h : V j = v) :
    AntSim.setV V j v = V := by
  funext i
  unfold AntSim.setV
  split
  · rename_i hij; subst hij; exact h.symm
  · rfl

/-- **The binding's relation at the node, read from the invariant** (open: the caller's `live`
token): some checker state and sent list past the caller's lower bound `net₀` at which the network
and node `j`, at its view `v`, are related (`NetOk`, `NodeOk`): what `msgShape.stmt` and
`readyMsgNums` take. -/
theorem drain_peek (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (net₀ : List Msg) :
    inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ viewFrag γ j v ∗ nodeLive γ j ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net : List Msg), AntSim.NetOk S net ∧
          AntSim.NodeOk S net j v ∧ net₀ <+: net⌝ ∗ viewFrag γ j v ∗ nodeLive γ j := by
  iintro ⟨#Hinv, #Hlb, Hv, Hl⟩
  iunfold sentLb at Hlb
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G, Hstr, H0, H1, H2, Hnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    imod view_update _ γ j V v v $$ [Hv H0 H1 H2] with ⟨%HVj, Hv, H0, H1, H2⟩
    · iframe Hv H0 H1 H2
    rw [setV_self HVj]
    imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, V, net, G
      iframe Hstr H0 H1 H2 Hnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl
    ipureintro
    obtain ⟨-, hA, -⟩ := Hpure.1
    exact ⟨S, net, hA.2.2.1, by rw [← HVj]; exact hA.2.2.2 j, Hpre.2⟩
  · iexfalso
    iapply nodeLive_over γ j
    iframe Hl Hover

end proof

end AntHarness
end EtcdGrove
end Perennial
