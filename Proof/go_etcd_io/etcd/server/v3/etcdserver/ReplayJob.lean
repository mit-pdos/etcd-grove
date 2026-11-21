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

/-- The apply channel gets the concrete run for the backend index when the
elected log agrees with the committed backend prefix. -/
theorem rnReplayJob_of_history (γ : RNNames GF) (view : GoSlice) (runs : List replayTermRun)
    (rt : w64) (n : Nat) (S : RaftState) (hb : uint.nat S.base.index' ≤ n)
    (hr : replayRunsDescribe runs S n) :
    letI := srvStor (GF := GF) γ.node
    (view ↦*□ runs : IProp GF) ⊢
      (□ ∀ sm : MsgSt, ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < γ.a0.length⌝ -∗
        sentMsg γ.node.cl srvClusterN γ.id sm -∗ ⌜DurAgrees S (γ.a0.map EntryModel.toLE)⌝) -∗
      rnReplayJob γ view rt n := by
  iintro #Hr #Hagree
  iunfold rnReplayJob
  iintro !> %sm %ci %h #Hsent
  obtain ⟨ht, hrt, hn, hci⟩ := h
  ihave %ha := Hagree $$ %sm %(And.intro ht ⟨hrt, hn⟩) Hsent
  have hd := replayImage_plogTerm γ.a0 S ci (by omega) hci (by omega) ha
  obtain ⟨hc, r, hfound, hterm⟩ := hr ci _ (by have := uint_nat_eq ci; omega) hd
  iexists runs, r
  iframe Hr
  ipureintro; exact ⟨hc, hfound, hterm⟩

end EtcdGrove
end Perennial
