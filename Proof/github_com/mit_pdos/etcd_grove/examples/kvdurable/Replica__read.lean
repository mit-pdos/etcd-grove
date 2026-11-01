/-
kvreconf's proof (the same Go text), ported. Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__read.lean`. Lean-first (no
Rocq counterpart); kv's `KV.Read` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/KV__Read.lean`)
with a timeout and without a read credit.

The cluster's next read sequence number (`readSeqs.next`, for the replica's id, in `1..9` by
`isReplica`) mints the read's context at `(id, seq)`, committed to the read seeing at least the
reader's committed log; under the lock a handoff
channel is registered as its waiting read (`readWaiterOk`). The answer comes through the handoff
(`readAns`), in the blocking `select` or, once the read is deleted, in the non-blocking one; it is the
key's value in a history extending the reader's (`kvr_readAns_ok`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__read
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.readCtx
public import Spec.context.WithTimeoutBackground
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ApplyLemmas
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.readSeqs__next
public import Proof.go_etcd_io.raft.v3.InvNodeCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (readCtxB logHist kvFold)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Replica.read.wp_proof
    (wp_readCtx : readCtx.spec (GF := GF) (hG := hG))
    (wp_next : readSeqs.next.spec (GF := GF) (hG := hG))
    (wp_node_ReadIndex : node.ReadIndex.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Replica.read.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph key tmo L0 Hkey
  wp_start as ⟨#Hrep, #HL0⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  iunfold kvLb at HL0
  icases HL0 with ⟨%l0, #Hl0, %HL0⟩
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
  have Hk64 : (key.length : Int) < 2 ^ 64 := by omega
  wp_apply wp_next γ vs sq id key l0 Hidr.1 Hidr.2 Hk64 $$ [$Hpkg $Hseqs $Hcl $Hl0]
    as %seq %ok Hmint
  cases ok
  case false =>
    -- the read sequence numbers used up
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  -- the read's context, minted at `(id, seq)`, committed after the reader's log
  icases Hmint $$ %rfl with ⟨#Hmint, #Hrc, #Hra⟩
  try wp_auto
  imod start_handoff ch (readAns γ (readCtxB id seq key)) iprop(True) iprop(False) γc
    $$ Hch Hoc with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
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
  wp_apply context.wp_Background
  try wp_auto
  wp_apply hWT tmo $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
  try wp_auto
  wp_apply wp_readCtx id seq key Hkey $$ [$Hpkg] as %b ⟨Hb, -⟩
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  ihave #Hnc : nodeCtx ctx' cd $$ []
  · unfold nodeCtx; iright; iexact Hctx
  ihave #Hhch : isChan ch γh.chanName GoString $$ [Hho]
  · unfold isHandoff; icases Hho with ⟨$, -⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  wp_apply wp_node_ReadIndex n γ.r.cluster kdRaftN id b (readCtxB id seq key)
    (fun _ => iprop(True)) ctx' cd $$ [$Hraftinit $HisNode $Hnc $Hb $Hrc] as %err -
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
    iapply handoff_rcv_au γh ch (readAns γ (readCtxB id seq key)) iprop(True)
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
    icases Hgot with ⟨Hw, -⟩
    iapply HΦ
    simp only [↓reduceIte]
    icases kd_readAns_ok γ id seq key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
    iexists L
    iframe HL
    ipureintro; rw [HL0]; exact HLf
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
    wp_apply wp_mapDelete mR2 Rd2 seq go.uint64
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
        iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, ch,
          γh.chanName
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hhch
        unfold nonblockingRecvAu
        isplit
        · iapply recvAu_nonblocking
          iapply handoff_rcv_au γh ch (readAns γ (readCtxB id seq key)) iprop(True)
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
          icases Hgot with ⟨Hw, -⟩
          iapply HΦ
          simp only [↓reduceIte]
          icases kd_readAns_ok γ id seq key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
          iexists L
          iframe HL
          ipureintro; rw [HL0]; exact HLf
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

end kvdurable
end EtcdGrove
end Perennial
