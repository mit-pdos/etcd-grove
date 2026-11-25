/- Lean-first (no Rocq counterpart).

Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Transport__start.lean`: the
node stored and its field made read-only (`isTransportCore` then holds), then a loop over the
read-only peers map (`wp_map_for_range`), forking each peer's `runPeer` with its `isPeer`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__start
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__runPeer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Transport.start.wp_proof (wp_runPeer : Transport.runPeer.spec (GF := GF) (hG := hG)) :
    Transport.start.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n sp et ed
  wp_start as ⟨#Hid, #Hsp, ⟨%v0, Hnode⟩, #Hstats, #Hps, #HisNode, %Htr, ⟨%sc, %γsc, #Hstop⟩, #Het, #Hed⟩
  ihave #Hps' := Hps
  iunfold isPeers at Hps'
  icases Hps' with ⟨%pm, %M, #Hpm, #HM, #Hpeers⟩
  try wp_auto
  ipersist Hnode
  ihave #Hcore : isTransportCore F t γ N id n $$ []
  · unfold isTransportCore
    iexists sp, sc, γsc
    iframe #
    ipureintro; exact Htr
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (_ : List w64) (i : Int) => iprop(∃ (x : Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "p" ∷ p_ptr ↦ x ∗
      "t" ∷ t_ptr ↦ t)) _ go.uint64 _ pm M DFrac.discard $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [p t]
  · iexists _
    simp only [named]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %pv ⟨%Hkey, %Hpv⟩ HP
    iNamed HP
    try wp_auto
    ihave ⟨%a, #Hp⟩ := BigSepM.bigSepM_lookup Hpv $$ Hpeers
    wp_apply wp_fork
    · wp_apply wp_runPeer F t γ N id n pv key a et ed $$ [$Hpkg $Hcore $Hp $Het $Hed]
      itrivial
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists pv
    simp only [named]
    iframe
    ipureintro; omega
  iintro HP -
  iNamed HP
  try wp_auto
  iapply HΦ
  iexact Hcore

end proof

end raft_kvnet
end EtcdGrove
end Perennial
