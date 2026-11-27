-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/IsLocalMsg.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). -/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.IsLocalMsg
public import KvRaft.Spec.go_etcd_io.raft.v3.isMsgInArray

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

omit [GooseExts] in
/-- `isLocalMsg`'s literal at the indices it has. -/
private theorem localMsgsV_fin : ∀ n : Fin 23,
    localMsgsV.arr[n.val]?.getD false = decide (W32 (n.val : Int) ∈ localMsgTypes) := by
  decide

omit [GooseExts] in
/-- `isLocalMsg`'s literal at a type: whether it is a local one. -/
private theorem localMsgsV_get (t : w32) (ht : 0 ≤ sint.Z t) :
    localMsgsV.arr[(sint.Z t).toNat]?.getD false = decide (t ∈ localMsgTypes) := by
  obtain ⟨n, hn⟩ : ∃ n, (sint.Z t).toNat = n := ⟨_, rfl⟩
  have hb : sint.Z t < 2 ^ 31 := by word
  have hn' : sint.Z t = (n : Int) := by omega
  have ht' : t = W32 (n : Int) := by rw [← hn']; exact BitVec.ofInt_toInt.symm
  rw [hn, ht']
  by_cases h : n < 23
  · exact localMsgsV_fin ⟨n, h⟩
  · rw [List.getElem?_eq_none (by simp [localMsgsV]; omega)]
    symm
    apply decide_eq_false
    simp only [localMsgTypes, List.mem_cons, List.not_mem_nil, _root_.or_false]
    intro hc
    rcases hc with e | e | e | e | e | e | e | e | e <;>
      (have e' := congrArg uint.Z e;
       rw [uint_Z_W32 _ (by omega) (by omega), uint_Z_W32 _ (by omega) (by omega)] at e'; omega)

/-- The table `isLocalMsg` from `isInitialized`, as a slice. -/
theorem IsLocalMsg.wp_proof
    (wp_isMsgInArray : isMsgInArray.spec (GF := GF) (hG := hG)) :
    IsLocalMsg.spec (GF := GF) (hG := hG) := by
  intro t Ht
  wp_start
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 23 - W64 0 = W64 23 from rfl]
  ihave #Hsl := array_slice_bool (globalAddr isLocalMsg) localMsgs DFrac.discard $$ isLocalMsg
  wp_apply wp_isMsgInArray t _ localMsgs.arr Ht as %b %Hb
  · iexact Hsl
  iapply HΦ
  ipureintro
  rw [Hb, HlocalMsgs]; exact localMsgsV_get t Ht

end proof

end EtcdGrove
end Perennial
