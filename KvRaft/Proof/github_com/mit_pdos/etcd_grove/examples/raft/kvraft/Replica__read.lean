/-
The proof of `KvRaft/Spec/.../kvraft/Replica__read.lean` at the store's facts (`kvFacts`, `kvRep`,
`Facts.lean`): kvdurablenoax's `Replica.read` proof (kvreconf's), with the read's context minted by the
client (the request's `readOkK`: the context at `(id, seq)`, committed after a committed log `l0`) in
place of `readSeqs.next`'s, and the replica's check that no read of the same `seq` waits (a client's
retry reaching it again: no answer). Under the lock a handoff channel is registered as the waiting
read (`readWaiterOk`); the answer comes through it (`readAns`), in the blocking `select` or, after the
timeout, in the non-blocking one; it is the key's value in a history extending `l0`'s
(`kd_readAns_ok`). The answer's length bound comes with it (`readWaiterOk`, from the replica's map: `MapFits`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Replica__read
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Facts
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ApplyLemmas
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.readCtx
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.withTimeout
public import KvRaft.Spec.go_etcd_io.raft.v3.node__ReadIndex
public import KvRaft.Proof.go_etcd_io.raft.v3.InvNodeCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open raft_kvreconf (readCtxB logHist kvFold)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Replica.read.wp_proof
    (wp_readCtx : readCtx.spec (GF := GF) (hG := hG))
    (wp_node_ReadIndex : node.ReadIndex.spec (GF := GF) (hG := hG))
    (hWT : withTimeout.spec (GF := GF) (hG := hG))
    (γ : KdNames) (vs : List w64) (dir : GoString) (cf : List w8 → Prop) :
    Replica.read.spec (GF := GF) (hG := hG) (kvFacts γ cf) (kvRep γ vs dir) := by
  intro r id seq key tmo
  have Hfr : (kvFacts (GF := GF) γ cf).readOk id seq key = readOkK γ id seq key := rfl
  have Hfa : ∀ v, (kvFacts (GF := GF) γ cf).ansRead id seq key v = ansReadK γ id seq key v :=
    fun _ => rfl
  rw [Hfr]
  simp only [Hfa]
  wp_start as ⟨#Hrep0, #Hro⟩
  iunfold kvRep at Hrep0
  iunfold isRep at Hrep0
  icases Hrep0 with ⟨%n, %st, %sts, %sq, %ρ, #HrepR⟩
  iunfold isReplicaR at HrepR
  iNamed HrepR
  ihave #Hrr := Hrep
  iunfold isReplica at Hrr
  iNamed Hrr
  ihave Hro' := Hro
  iunfold readOkK at Hro'
  icases Hro' with ⟨%Hkey, #Hmint, #Hrc, %l0, #Hra, #Hl0⟩
  have Hk64 : (key.length : Int) < 2 ^ 64 := by omega
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcci := context.isClosedchanInit_of_init $$ Hctxinit
  try wp_auto
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  try wp_auto
  imod start_handoff ch (fun v => iprop(readAns γ (readCtxB id seq key) v ∗ ⌜(v.length : Int) + 9 < 2 ^ 63⌝)) iprop(True) iprop(False) γc
    $$ Hch Hoc with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
  try wp_auto
  wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
    (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mR Rd seq (DFrac.own 1)) $$ HRd as HRd
  cases Hbusy : Rd !! seq with
  | some ch0 =>
    -- a read of the same `seq` waits: no answer
    simp only [Option.isSome_some, _root_.decide_true]
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters HmR HRd Hreads]
    · inext
      unfold lockInv
      iexists mW, W, mR, Rd
      iframe
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  | none =>
  simp only [Option.isSome_none]
  try wp_auto
  wp_apply wp_mapInsert go.uint64 mR Rd seq ch $$ [$HRd] as HRd
  ihave Hreads := reads_drop γ id Rd seq $$ Hreads
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters HmR HRd Hreads Hprod]
  · inext
    unfold lockInv
    iexists mW, W, mR, Rd.insert seq ch
    iframe
    rw [← GMap.insert_delete Rd seq ch]
    iapply (BigSepM.bigSepM_insert (Φ := fun s ch => readWaiterOk (GF := GF) γ id s ch)
      (GMap.lookup_delete_eq Rd seq)).2
    iframe Hreads
    unfold readWaiterOk
    iexists readCtxB id seq key, γh
    iframe Hmint Hho Hprod
  try wp_auto
  wp_apply hWT tmo $$ [$Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx, -⟩
  try wp_auto
  wp_apply wp_readCtx id seq key Hkey $$ [$Hpkg] as %b ⟨Hb, -⟩
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  ihave #Hnc : nodeCtx ctx' cd $$ []
  · unfold nodeCtx; iright; iexact Hctx
  ihave #Hhch : isChan ch γh.chanName GoString $$ [Hho]
  · unfold isHandoff; icases Hho with ⟨$, -⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  ihave %Htr0 := kdCluster_untraced γ vs $$ Hcl
  wp_apply wp_node_ReadIndex n γ.r.cluster kdRaftN id b (readCtxB id seq key)
    (fun _ => iprop(True)) ctx' cd Htr0 $$ [$Hraftinit $HisNode $Hnc $Hb $Hrc] as %err -
  · ipureintro; intro b h; simp [Hmd] at h
  try wp_auto
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto_lc 1
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the answer
    simp only [chan.blockingClausePre]
    iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, ch, γh.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hhch
    iapply handoff_rcv_au γh ch (fun v => iprop(readAns γ (readCtxB id seq key) v ∗ ⌜(v.length : Int) + 9 < 2 ^ 63⌝)) iprop(True)
      iprop(False) false _ $$ Hho Hlc1 Hcons
    inext
    iintro %v %ok ⟨Hcons, Hgot⟩
    try wp_auto
    wp_apply Hcancel
    try wp_auto
    unfold handoffGot
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot with ⟨-, Hf⟩
      iexfalso; iexact Hf
    simp only [↓reduceIte]
    icases Hgot with ⟨⟨#Hw, %Hvl⟩, -⟩
    iapply HΦ
    simp only [↓reduceIte]
    icases kd_readAns_ok γ id seq key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
    unfold ansReadK
    iexists l0, L
    iframe Hra HL
    ipureintro; exact HLf
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the timeout
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    try wp_auto
    wp_apply Hcancel
    try wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
    iunfold lockInv at HL
    icases HL with ⟨%mW2, %W2, %mR2, %Rd2, HL⟩
    iNamed HL
    try wp_auto
    wp_apply (wp_map_lookup1 (K := w64) (V := Loc) go.uint64
      (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mR2 Rd2 seq (DFrac.own 1)) $$ HRd as HRd
    try wp_auto
    wp_if_destruct
    · wp_apply wp_mapDelete mR2 Rd2 seq go.uint64
        (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$HRd] as HRd
      ihave Hreads := reads_drop γ id Rd2 seq $$ Hreads
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters HmR HRd Hreads]
      · inext
        unfold lockInv
        iexists mW2, W2, mR2, GMap.delete seq Rd2
        iframe
      try wp_auto
      -- an answer sent before the read was deleted, if any
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, _,
            γh.chanName
          isplitr
          · ipureintro; rfl
          isplitr
          · iexact Hhch
          unfold nonblockingRecvAu
          isplit
          · iapply recvAu_nonblocking
            iapply handoff_rcv_au γh _ (fun v => iprop(readAns γ (readCtxB id seq key) v ∗ ⌜(v.length : Int) + 9 < 2 ^ 63⌝)) iprop(True)
              iprop(False) false _ $$ Hho Hlc1 Hcons
            inext
            iintro %v %ok ⟨Hcons, Hgot⟩
            try wp_auto
            unfold handoffGot
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases ok
            · simp only [Bool.false_eq_true, ↓reduceIte]
              icases Hgot with ⟨-, Hf⟩
              iexfalso; iexact Hf
            simp only [↓reduceIte]
            icases Hgot with ⟨⟨#Hw, %Hvl⟩, -⟩
            iapply HΦ
            simp only [↓reduceIte]
            icases kd_readAns_ok γ id seq key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
            unfold ansReadK
            iexists l0, L
            iframe Hra HL
            ipureintro; exact HLf
          · itrivial
        · iapply BigAndL.bigAndL_nil.2
          itrivial
      · try wp_auto
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    · try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters HmR HRd Hreads]
      · inext
        unfold lockInv
        iexists mW2, W2, mR2, Rd2
        iframe
      try wp_auto
      -- an answer sent before the read was deleted, if any
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, _,
            γh.chanName
          isplitr
          · ipureintro; rfl
          isplitr
          · iexact Hhch
          unfold nonblockingRecvAu
          isplit
          · iapply recvAu_nonblocking
            iapply handoff_rcv_au γh _ (fun v => iprop(readAns γ (readCtxB id seq key) v ∗ ⌜(v.length : Int) + 9 < 2 ^ 63⌝)) iprop(True)
              iprop(False) false _ $$ Hho Hlc1 Hcons
            inext
            iintro %v %ok ⟨Hcons, Hgot⟩
            try wp_auto
            unfold handoffGot
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases ok
            · simp only [Bool.false_eq_true, ↓reduceIte]
              icases Hgot with ⟨-, Hf⟩
              iexfalso; iexact Hf
            simp only [↓reduceIte]
            icases Hgot with ⟨⟨#Hw, %Hvl⟩, -⟩
            iapply HΦ
            simp only [↓reduceIte]
            icases kd_readAns_ok γ id seq key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
            unfold ansReadK
            iexists l0, L
            iframe Hra HL
            ipureintro; exact HLf
          · itrivial
        · iapply BigAndL.bigAndL_nil.2
          itrivial
      · try wp_auto
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
