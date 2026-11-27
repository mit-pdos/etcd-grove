/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__write.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__write
public import KvRaft.Spec.net.UDPConn__WriteToUDP

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]

/-- **`udpDgOk_send`**: the write's atomic update, through the destination's invariant: a datagram
of the protocol, short enough to arrive intact (`parseDg_length`), is what the network may hold of
it, so the invariant keeps holding. -/
private theorem udpDgOk_send (F : KvFacts GF) (γu : UdpNames) (a : GoString) (bs : List w8) :
    ⊢ udpAddrInv F γu a -∗ udpDgOk F γu bs -∗ £ 1 -∗
      |={⊤,∅}=> ∃ ms, udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ∗
        ∀ r ms', ⌜SendOut bs ms r ms'⌝ -∗
          udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms' ={∅,⊤}=∗
          (fun _ : Bool => iprop(True)) (r = errCode none) := by
  iintro #Hinv #Hd Hlc
  ihave #Hd' := Hd
  iunfold udpDgOk at Hd'
  icases Hd' with ⟨%dg, %Hdg, -⟩
  have Hlen : bs.length ≤ intactMax := parseDg_length Hdg
  iunfold udpAddrInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑udpSentN) $$ Hlc Hi with Hi
  icases Hi with ⟨%ms, Hs, #Hms⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ms
  iframe Hs
  iintro %r %ms' %Hout Hs
  imod Hmask with -
  obtain ⟨d, Hint, Hms'⟩ := Hout
  have Hd : d = bs := Hint Hlen
  subst Hd
  ihave #Hms'' : [∗list] x ∈ ms', udpDgOk F γu x $$ []
  · rcases Hms' with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
    · iapply BigSepL.bigSepL_cons.2; iframe Hd Hms
    · iapply BigSepL.bigSepL_cons.2; iframe Hd Hms
    · iexact Hms
  imod Hclose $$ [Hs] with -
  · inext; iexists ms'; iframe Hs Hms''
  imodintro
  itrivial

theorem udpNet.write.wp_proof
    (wp_WriteToUDP : net.UDPConn.WriteToUDP.spec (GF := GF) (hG := hG)) :
    udpNet.write.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot to b bs
  wp_start as ⟨#Hu, #Hb, #Hd⟩
  iunfold isUdpNet at Hu
  icases Hu with ⟨%c, %s, %a, %am, %A, #Hid, #Hc, #Hconn, #Ha, #Ham, #HA, #Haddrs, #Hboot, #Hinv,
    #Hmu⟩
  wp_auto_lc 1
  wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
    (go.GoType.PointerType _root_.Perennial.net.UDPAddr.ty) am A to DFrac.discard) $$ HA as -
  try wp_auto
  cases h : A !! to with
  | none =>
    simp only [Option.isSome_none, Option.getD_none]
    try wp_auto
    iapply HΦ
    itrivial
  | some p =>
    simp only [Option.isSome_some, Option.getD_some]
    try wp_auto
    ihave #Hp := BigSepM.bigSepM_lookup h $$ Haddrs
    iunfold isUdpPeerAddr at Hp
    icases Hp with ⟨%ip, %port, %pa, #Hpa, %Hvd, #Hpinv⟩
    wp_apply wp_WriteToUDP c s a b DFrac.discard bs p ip port pa (fun _ => iprop(True))
      $$ [Hlc1] as %n %err ⟨-, %ok, -, Hres⟩
    · iframe Hconn Hb Hpa
      isplitr
      · ipureintro; exact Hvd
      iapply udpDgOk_send F γu pa bs $$ Hpinv Hd Hlc1
    icases Hres with (%Hok | ⟨%Hok, %src, Herr⟩)
    · obtain ⟨-, -, rfl⟩ := Hok
      try wp_auto
      iapply HΦ
      itrivial
    · iunfold net.udpErr at Herr
      icases Herr with ⟨%pe, %e, %Herr, -⟩
      subst Herr
      try wp_auto
      iapply HΦ
      itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
