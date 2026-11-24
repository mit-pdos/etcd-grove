/-
The proof of `KvNet/Spec/.../kvnet/udpNet__receive.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__receive
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newReassembler
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__handle
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__stepper
public import KvNet.Spec.net.UDPConn__ReadFromUDP
public import Perennial.Proof.time.Link

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

/-- What a read at the address `a` gives (`ReadFromUDP`'s atomic update, through the address's
invariant): a datagram of the protocol, or nothing. -/
private def recvQ (F : KvFacts GF) (γu : UdpNames) : Option (List w8) → IProp GF
  | some d => udpDgOk F γu d
  | none => iprop(True)

/-- **`udpDgOk_recv`**: the read's atomic update, from the address's invariant: what arrives is a
datagram sent there, so of the protocol. -/
private theorem udpDgOk_recv (F : KvFacts GF) (γu : UdpNames) (a : GoString) :
    ⊢ udpAddrInv F γu a -∗ £ 1 -∗
      |={⊤,∅}=> ∃ ms, udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ∗
        ∀ od, ⌜RecvOut ms od⌝ -∗
          udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ={∅,⊤}=∗ recvQ F γu od := by
  iintro #Hinv Hlc
  iunfold udpAddrInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑udpSentN) $$ Hlc Hi with Hi
  icases Hi with ⟨%ms, Hs, #Hms⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ms
  iframe Hs
  iintro %od %Hod Hs
  imod Hmask with -
  imod Hclose $$ [Hs] with -
  · inext; iexists ms; iframe Hs Hms
  imodintro
  rcases od with _ | d
  · unfold recvQ; itrivial
  · simp only [RecvOut] at Hod
    unfold recvQ
    iapply (BigSepL.bigSepL_mem Hod) $$ Hms

theorem udpNet.receive.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (wp_newReassembler : newReassembler.spec (GF := GF) (hG := hG))
    (wp_stepper : udpNet.stepper.spec (GF := GF) (hG := hG) F rep stp)
    (wp_handle : udpNet.handle.spec (GF := GF) (hG := hG))
    (wp_ReadFromUDP : net.UDPConn.ReadFromUDP.spec (GF := GF) (hG := hG)) :
    udpNet.receive.spec (GF := GF) (hG := hG) F rep stp := by
  intro γu u id boot nd γ N
  wp_start as ⟨#Hu, #Hnd, #Hcc⟩
  ihave #Hu' := Hu
  iunfold isUdpNet at Hu'
  icases Hu' with ⟨%c, %s, %a, %am, %A, #Hid, #Hconn, #Hca, #Hainv, #Ham, #HA, -, -, -, -⟩
  ihave #Hnd' := Hnd
  iunfold isNodeS at Hnd'
  icases Hnd' with ⟨%cfg, %M, %sp, %f, -, -, -, #Hst, #Hs, -⟩
  try wp_auto
  wp_apply wp_newReassembler F γu sp $$ [$Hpkg $Hs] as %r Hr
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %stm Hstm
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (Q : GMap w64 Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "id" ∷ id_ptr ↦ x ∗
      "u" ∷ u_ptr ↦ u ∗ "n" ∷ n_ptr ↦ nd ∗ "steps" ∷ steps_ptr ↦ stm ∗
      "Hstm" ∷ stm ↦$ Q ∗
      "HQ" ∷ ([∗map] _pid ↦ c ∈ Q, ∃ γq : ChanNames,
        isChanBag (V := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received) γq c (recvElem F id)))) _ go.uint64 _ am A DFrac.discard $$ HA
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id u n steps Hstm]
  · iexists _, ∅
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
    · try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, Q
      simp only [named]
      iframe
      ipureintro; omega
    · wp_apply chan.wp_make2 (V := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received) (W64 256)
        as %ch %γq ⟨#Hch, %_, Hoc⟩
      · ipureintro; decide
      ihave Hoc : ownChan γq github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received (.Buffered []) $$ Hoc
      imod start_bag (recvElem F id) (.Buffered []) ch γq trivial $$ Hch Hoc with #Hbag
      try wp_auto
      wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 stm Q key _) $$ Hstm as Hstm
      try wp_auto
      wp_apply wp_fork
      · wp_apply wp_stepper γu u id boot nd γ N ch γq $$ [$Hpkg $Hu $Hnd $Hcc $Hbag]
        itrivial
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      ihave #Hq : iprop(∃ γq : ChanNames,
          isChanBag (V := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received) γq ch
            (recvElem F id)) $$ []
      · iexists γq; iexact Hbag
      cases h : Q !! key with
      | none =>
        iapply (BigSepM.bigSepM_insert h).2
        iframe Hq HQ
      | some y =>
        icases (BigSepM.bigSepM_delete h).1 $$ HQ with ⟨-, HQ⟩
        iapply BigSepM.bigSepM_insert_delete.2
        iframe Hq HQ
  iintro HP -
  iNamed HP
  imod ownMap_persist stm _ _ $$ Hstm with #Hstm
  icases HQ with #HQ
  wp_auto_lc 1
  wp_apply (wp_slice_make2 (V := w8) (W64 524)) as %b ⟨Hb, -⟩
  · ipureintro; decide
  ihave %Hblen := ownSlice_len $$ Hb
  try wp_auto
  ihave IH : iprop(∃ bs0 : List w8,
      "Hb" ∷ b ↦* bs0 ∗ "Hr" ∷ ownReassembler F γu r ∗ "Hlc" ∷ £ 1 ∗
      "%Hbs0" ∷ ⌜bs0.length = 524⌝) $$ [Hb Hr Hlc1]
  · iexists _
    iframe Hb Hr Hlc1
    ipureintro; rw [List.length_replicate]
  wp_for IH
  wp_apply_core wp_ReadFromUDP c s a b bs0 (recvQ F γu) $$ [Hb Hlc]
  · iframe Hca Hb
    iapply udpDgOk_recv F γu a $$ Hainv Hlc
  iintro %k %addr %err ⟨%od, Hrq, Hod⟩
  wp_auto_lc 1
  rcases od with _ | d
  · -- a failed read: wait, then go on
    icases Hod with ⟨⟨%Hk, %Haddr⟩, Hb, %src, #He⟩
    iunfold net.udpErr at He
    icases He with ⟨%pe, %e, %Herr, -⟩
    subst Herr
    try wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
    iexists bs0
    iframe Hb Hr Hlc1
    ipureintro; exact Hbs0
  · -- a datagram of the protocol
    dsimp only [recvQ]
    icases Hod with ⟨⟨%Hk, %Herr⟩, Hb⟩
    subst Herr
    ihave #Hrq := Hrq
    ihave Hrq' := Hrq
    iunfold udpDgOk at Hrq'
    icases Hrq' with ⟨%dg, %Hdg, -⟩
    have Hdl := parseDg_length Hdg
    have Hbl : sint.nat b.len = 524 := by rw [← Hblen.1, List.length_replicate]
    have Hkd : k.toNat = d.length := by
      rw [Hk]; unfold maxDatagramN at Hdl
      have : b.len.toNat = 524 := by have := Hblen.2; word
      omega
    rw [Hkd, List.take_of_length_le (Nat.le_refl _)]
    ihave %Hwf := ownSlice_wf $$ Hb
    have Hkb : sint.Z k ≤ sint.Z b.len := by
      have := Hblen.2; unfold maxDatagramN at Hdl; word
    simp only
    try wp_auto
    rw [ite_eq_left (by refine ⟨by decide, by word, by word⟩)]
    icases (ownSlice_split_all k b (DFrac.own 1) _ ⟨by word, Hkb⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    have Hsk : sint.nat k = d.length := by word
    rw [Hsk, List.take_left' rfl]
    try wp_auto
    wp_apply wp_handle F γu u id boot nd sp r stm Q (slice.slice b w8 (W64 0) k) (DFrac.own 1) d
      $$ [$Hpkg $Hu $Hst $Hs $Hr $Hstm $HQ $Hb1 $Hrq] as ⟨Hr, Hb1⟩
    ihave Hb := (ownSlice_split_all k b (DFrac.own 1) (d ++ List.drop d.length bs0) ⟨by word, Hkb⟩).2 $$ [Hb1 Hb2]
    · rw [Hsk, List.take_left' rfl]
      iframe Hb1
      iexact Hb2
    try wp_auto
    wp_for_post
    iframe
    iexists _
    iframe Hb Hr Hlc1
    ipureintro
    simp only [List.length_append, List.length_drop, Hbs0]
    unfold maxDatagramN at Hdl
    omega

end proof

end raft_kvnet
end EtcdGrove
end Perennial
