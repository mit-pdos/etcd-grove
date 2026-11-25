/-
The proof of `KvRaft/Spec/.../kvraft/Transport__Send.lean`: a loop over the messages; each one's peer
looked up by its `To` in the read-only peers map (`isPeers`): a peer's (`isPeer`) gets the message
with its fact by `enqueue` (`qElem`: its `To` is the peer's id, the map's key), another is dropped.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__Send
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__enqueue
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__dropped
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Transport.Send.wp_proof (wp_enqueue : Transport.enqueue.spec (GF := GF) (hG := hG))
    (wp_dropped : Transport.dropped.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    Transport.Send.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n msl dqs ms
  wp_start as ⟨#Ht, #Hps, Hms, Hel⟩
  ihave #Hps' := Hps
  iunfold isPeers at Hps'
  icases Hps' with ⟨%pm, %M, #Hpm, #HM, #Hpeers⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  ihave %Hmslen := ownSlice_len $$ Hms
  ihave IH : iprop(∃ (k : w64) (mv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hms" ∷ msl ↦*{dqs} ms ∗
      "Hel" ∷ ([∗list] m ∈ ms.drop (sint.nat k), sendElem F m) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝) $$ [i m Hms Hel]
  · iexists W64 0, _
    iframe i m Hms
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe Hel
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ms.length := by word
    obtain ⟨q, Hq⟩ : ∃ q, ms[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z msl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index msl (sint.Z k) _ dqs q Hk.1 $$ [Hms] as Hms
    · iframe Hms; ipureintro; exact Hq
    have Hdrop : ms.drop (sint.nat k) = q :: ms.drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]
      rw [List.getElem?_eq_getElem Hlt] at Hq
      rw [Option.some.inj Hq]
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hdrop]
    icases Hel with ⟨Hq, Hel⟩
    iunfold sendElem at Hq
    icases Hq with ⟨%dq, %dqe, %cap, %st, %src, Hm, #Hok⟩
    try wp_auto
    wp_apply wp_GetTo.1 q _ _ _ _ $$ [$Hpb $Hm] as Hm
    wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.peer.ty)
      pm M st.msg.To' DFrac.discard) $$ HM as -
    try wp_auto
    cases Hl : M !! st.msg.To' with
    | none =>
      simp only [Option.isSome_none, Option.getD_none, decide_false]
      try wp_auto
      wp_apply wp_dropped F t γ N id n q dq dqe cap st $$ [$Hpkg $Ht $Hm] as -
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, q
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
    | some p =>
      simp only [Option.isSome_some, Option.getD_some, decide_true]
      try wp_auto
      icases BigSepM.bigSepM_lookup Hl $$ Hpeers with ⟨%a, #Hp⟩
      wp_apply wp_enqueue F t γ N id n p st.msg.To' a q $$ [$Hpkg $Ht $Hp Hm]
      · iunfold qElem
        iexists dq, dqe, cap, st, src
        iframe Hm Hok
        ipureintro; rfl
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, q
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
  · try wp_auto
    iapply HΦ
    iexact Hms

end proof

end kvraft
end EtcdGrove
end Perennial
