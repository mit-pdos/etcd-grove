/- Relate the immutable term runs to the Raft state's entries above the delivered cursor. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- Every entry above the delivered cursor in this Ready has a readable run with its term. -/
def replayRunsDescribe [GooseExts] (runs : List replayTermRun) (S : RaftState) (delivered : Nat) : Prop :=
  ∀ (ci term : w64), delivered < uint.nat ci → plogTermAt S.base S.ents ci = some term →
    replayRunCovers runs ci = true ∧ ∃ r, replayRunAt runs ci = some r ∧ r.term' = term

variable [GooseExts]

/-- In the replay window the last entry in the durable backend prefix is at the
consistent index. Agreement with the Raft state's log identifies the entry term. -/
theorem replayImage_plogTerm (A : List EntryModel) (S : RaftState) (ci : w64)
    (hpos : 0 < A.length) (hci : uint.Z ci = A.length) (hb : uint.nat S.base.index' ≤ A.length)
    (ha : DurAgrees S (A.map EntryModel.toLE)) :
    plogTermAt S.base S.ents ci = some ((A.getLast?.map EntryModel.term).getD (W64 0)) := by
  let k := A.length - 1
  have hk : k < A.length := by dsimp [k]; omega
  have he := List.getElem?_eq_getElem hk
  have hm : (A.map EntryModel.toLE)[k]? = some (A[k].toLE) := by simp [List.getElem?_map, he]
  have hn : k + 1 = A.length := by dsimp [k]; omega
  have hterm := ha k _ (by omega) hm
  have hw : W64 ((k : Int) + 1) = ci := by word
  rw [hw] at hterm
  rw [List.getLast?_eq_getElem?, he]
  exact hterm

variable [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (2026-11-24, the lifetime law: `notes/etcd-dist-d6.md`, T4 round 5) **A `MsgSnap` of this run is
past the restart's term**: a `MsgSnap` a `Ready` of this run handed out (`rnMessageSource`), at a
restart (`a0 ≠ []`: `rnRestartOk`'s second disjunct, with the node's `nodeStartTerm γ.nl γ.t0`), has
a term past `t0` (raft's `readySnapSources_startTerm`). -/
theorem rnReplayJob_lifetime (γ : RNNames GF) (sm : MsgSt) (ml : Loc) :
    rnRestartOk γ ∗ rnMessageSource γ ⟨ml, sm⟩ ⊢
      ⌜sm.msg.Type' = MsgSnap → γ.a0 ≠ [] → uint.Z γ.t0 < uint.Z sm.msg.Term'⌝ := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hrok, #Hsrc⟩
  iunfold rnRestartOk at Hrok
  icases Hrok with (%h0 | ⟨-, -, #Hst⟩)
  · ipureintro; intro _ hne; exact absurd h0.1 hne
  iunfold rnMessageSource at Hsrc
  icases Hsrc with ⟨%term, %ms, %bound, %inst, %hq, #Hss⟩
  ihave %Hall := readySnapSources_startTerm γ.node.cl γ.nl γ.id term ms bound inst γ.t0 $$ [Hss Hst]
  · iframe Hss Hst
  ipureintro
  intro ht _
  exact Hall ⟨ml, sm⟩ hq ht

/-- The apply channel gets the concrete run for the backend index when the
elected log agrees with the committed backend prefix. (2026-11-24, the lifetime law) The agreement is
needed only for a `MsgSnap` of this run (`rnReplayJob`), so only at a term past the restart's
(`rnReplayJob_lifetime`): `uint.Z γ.t0 < uint.Z rt`, which raft's `raftState_cmtBefore_agree` takes. -/
theorem rnReplayJob_of_history (γ : RNNames GF) (view : GoSlice) (runs : List replayTermRun)
    (rt : w64) (n : Nat) (S : RaftState) (hb : uint.nat S.base.index' ≤ n)
    (hr : replayRunsDescribe runs S n) :
    letI := srvStor (GF := GF) γ.node
    (view ↦*□ runs : IProp GF) ⊢ rnRestartOk γ -∗
      (□ ∀ sm : MsgSt, ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < γ.a0.length ∧
          uint.Z γ.t0 < uint.Z rt⌝ -∗
        sentMsg γ.node.cl srvClusterN γ.id sm ={⊤}=∗ ⌜DurAgrees S (γ.a0.map EntryModel.toLE)⌝) -∗
      rnReplayJob γ view rt n := by
  iintro #Hr #Hrok #Hagree
  iunfold rnReplayJob
  iintro !> %sm %ci %h #Hsent %ml #Hsrc
  obtain ⟨ht, hrt, hn, hci⟩ := h
  ihave %hlt := rnReplayJob_lifetime γ sm ml $$ [Hrok Hsrc]
  · iframe Hrok Hsrc
  have ht0 : uint.Z γ.t0 < uint.Z rt := by
    rw [← hrt]; exact hlt ht (fun h => by rw [h] at hn; exact Nat.not_lt_zero _ hn)
  ihave Hag := Hagree $$ %sm %(⟨ht, hrt, hn, ht0⟩) Hsent
  imod Hag with %ha
  have hd := replayImage_plogTerm γ.a0 S ci (by omega) hci (by omega) ha
  obtain ⟨hc, r, hfound, hterm⟩ := hr ci _ (by have := uint_nat_eq ci; omega) hd
  imodintro
  iexists runs, r
  iframe Hr
  ipureintro; exact ⟨hc, hfound, hterm⟩

/-- (2026-11-24, option (a): the campaign map's closure) **L2 at the durable state, as the replay job's
premise**: raft's `raftState_leadAgree` at a durable state `S` of term `rt` (made at the `Ready`'s
*enter*) gives `rnReplayJob_of_history`'s premise: a `MsgSnap` this node sent at `rt` shows it leads
`rt` (`sentMsg_localSnapshotLeader`). -/
theorem rnReplayJob_premise_of_lead (γ : RNNames GF) (S : RaftState) (rt : w64) (n : Nat)
    (hrt : S.term = rt) :
    letI := srvStor (GF := GF) γ.node
    (□ (snapshotLeader γ.node.cl γ.id S.term ={⊤}=∗
        ⌜durLogAgrees S (γ.a0.map EntryModel.toLE)⌝) : IProp GF) ⊢
      □ ∀ sm : MsgSt, ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < γ.a0.length ∧
          uint.Z γ.t0 < uint.Z rt⌝ -∗
        sentMsg γ.node.cl srvClusterN γ.id sm ={⊤}=∗ ⌜DurAgrees S (γ.a0.map EntryModel.toLE)⌝ := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hlaw !> %sm %h #Hsent
  obtain ⟨ht, htm, -, -⟩ := h
  ihave #Hsl := sentMsg_localSnapshotLeader γ.node.cl srvClusterN γ.id sm ht $$ Hsent
  rw [htm, ← hrt]
  ihave Hl := Hlaw $$ Hsl
  imod Hl with %ha
  imodintro; ipureintro; exact ha

/-- (2026-11-24, the lifetime law) **The server's membership is fixed** (raft's L2 premise `confFixed`):
after every committed log the configuration is the boot one (`srv_confAt_simple`). -/
theorem srv_confFixed [go_etcd_io.raft.v3.Assumptions] (γ : ServerRaftNames) (E : CoPset)
    (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) γ ⊢
      (letI := srvStor (GF := GF) γ.raft; confFixed γ.raft.cl E (Membership.simple γ.raft.cfg)) := by
  letI := srvStor (GF := GF) γ.raft
  iintro #Hinv
  unfold confFixed
  iintro !> %l #Hl
  iapply srv_confAt_simple γ l l.length (Nat.le_refl _) E hC hL
  iframe Hinv Hl

end EtcdGrove
end Perennial
