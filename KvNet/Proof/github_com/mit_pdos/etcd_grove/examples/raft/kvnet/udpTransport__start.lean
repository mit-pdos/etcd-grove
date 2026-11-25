/-
The proof of `KvNet/Spec/.../kvnet/udpTransport__start.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__start
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__runPeer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

theorem udpTransport.start.wp_proof
    (wp_runPeer : udpTransport.runPeer.spec (GF := GF) (hG := hG)) :
    udpTransport.start.spec (GF := GF) (hG := hG) := by
  intro F γu t γ N id n sc γsc
  wp_start as ⟨#Hb, ⟨%v0, Hnode⟩, #HisNode, %Htr⟩
  ihave #Hb' := Hb
  iunfold isUdpBase at Hb'
  icases Hb' with ⟨%u, %boot, %sp, -, -, -, -, -, -, #Hps⟩
  iunfold isUdpPeers at Hps
  icases Hps with ⟨%pm, %M, #Hpm, #HM, #Hpeers⟩
  try wp_auto
  ipersist Hnode
  ihave #Hcore : isUdpCore F γu t γ N id n $$ []
  · unfold isUdpCore
    iexists sc, γsc
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
    ihave #Hp := BigSepM.bigSepM_lookup Hpv $$ Hpeers
    wp_apply wp_fork
    · wp_apply wp_runPeer F γu t γ N id n pv key $$ [$Hpkg $Hcore $Hp]
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
