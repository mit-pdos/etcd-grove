/- Lean-first (no Rocq counterpart).

Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/newTransport.lean`: the
transport's struct, then a loop over the addresses (`wp_map_for_range`): each other replica's peer,
its queue a fresh channel made a bag of `qElem F pid` (`start_bag`), inserted in the peers map; the
map persisted at the end.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.newTransport

@[expose] public section

set_option linter.iris.style.nameCheck false

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

theorem newTransport.wp_proof : newTransport.spec (GF := GF) (hG := hG) := by
  intro F id am M sts
  wp_start as ⟨#HM, #Hpr⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %pm Hpm
  -- (2026-11-24, G5) the stop channel, a broadcast: its closer goes to `stop`
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsc Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  irename : id_ptr ↦ id => Hidv
  iStructNamed «$r0»
  ipersist id
  ipersist stats
  ipersist peers
  ipersist stopc
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := GoString) (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64) (y : GoString)
      (Mp : GMap w64 Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hidv" ∷ id_ptr ↦ id ∗
      "t" ∷ t_ptr ↦ «$r0_ptr» ∗
      "pid" ∷ pid_ptr ↦ x ∗
      "addr" ∷ addr_ptr ↦ y ∗
      "Hpm" ∷ pm ↦$ Mp ∗
      "Hps" ∷ ([∗map] k ↦ p ∈ Mp, ∃ a, isPeer F p k a))) _ go.uint64 go.string am M DFrac.discard $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [pid addr Hpm Hidv t]
  · iexists _, _, ∅
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact Int.le_refl _
    iapply BigSepM.bigSepM_empty.2; itrivial
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    try wp_auto
    wp_if_destruct
    · -- itself: left out
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, vv, Mp
      simp only [named]
      iframe
      ipureintro; omega
    · -- another replica: its peer
      wp_apply chan.wp_make2 (V := Loc) (W64 256) as %ch %γq ⟨#Hch, %_, Hoc⟩
      · ipureintro; decide
      ihave Hoc : ownChan γq Loc (.Buffered []) $$ Hoc
      imod start_bag (qElem F key) (.Buffered []) ch γq trivial $$ Hch Hoc with #Hbag
      try wp_auto
      iStructNamed «$r0»
      ipersist id
      ipersist addr
      ipersist queue
      have Hkv : M !! key = some vv ∧ key ≠ id := ⟨Hvv, Hif⟩
      ihave ⟨#Hap, %Hok⟩ := Hpr $$ %key %vv %Hkv
      try wp_auto
      wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 pm Mp key _) $$ Hpm as Hpm
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, vv, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      ihave #Hp : iprop(∃ a, isPeer F «$r0_ptr» key a) $$ []
      · iexists vv
        unfold isPeer isPeerAddr
        iframe #
        ipureintro; exact Hok
      cases h : Mp !! key with
      | none =>
        iapply (BigSepM.bigSepM_insert h).2
        iframe Hp Hps
      | some y =>
        icases (BigSepM.bigSepM_delete h).1 $$ Hps with ⟨-, Hps⟩
        iapply BigSepM.bigSepM_insert_delete.2
        iframe Hp Hps
  iintro HP -
  iNamed HP
  imod ownMap_persist pm _ _ $$ Hpm with #Hpm
  try wp_auto
  iapply HΦ
  iframe #
  isplitl [node]
  · iexists _; iexact node
  isplitl [Hps]
  · unfold isPeers
    iexists pm, Mp
    iframe #
    iexact Hps
  iexists sc, γsc
  unfold isTransportStop transportStopper
  iframe stopc Hunk Hpend

end proof

end kvraft
end EtcdGrove
end Perennial
