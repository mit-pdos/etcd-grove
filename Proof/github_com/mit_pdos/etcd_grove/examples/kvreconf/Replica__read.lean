/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__read.lean`. Lean-first (no
Rocq counterpart); kv's `KV.Read` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/KV__Read.lean`)
with a timeout and without a read credit.

Under the lock the replica's next read sequence number mints the read's context at `(id, seq)`
(`kvr_mint_read`, committed to the read seeing at least the reader's committed log), and a handoff
channel is registered as its waiting read (`readWaiterOk`). The answer comes through the handoff
(`readAns`), in the blocking `select` or, once the read is deleted, in the non-blocking one; it is the
key's value in a history extending the reader's (`kvr_readAns_ok`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__read
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.readCtx
public import Spec.context.WithTimeoutBackground
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientLemmas
public import Proof.go_etcd_io.raft.v3.InvNodeCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Replica.read.wp_proof
    (wp_readCtx : kvreconf.readCtx.spec (GF := GF) (hG := hG))
    (wp_node_ReadIndex : node.ReadIndex.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Replica.read.spec (GF := GF) (hG := hG) := by
  intro γr vs id r key tmo L0 Hkey
  wp_start as ⟨#HisRep, #HL0⟩
  iunfold isRep at HisRep
  icases HisRep with ⟨%n, %st, %sts, %ρ, #HR⟩
  iunfold isReplicaR at HR
  iNamed HR
  ihave #Hrep' := Hrep
  iclear Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv⟩
  iunfold kvLb at HL0
  icases HL0 with ⟨%l0, #Hl0, %HL0⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  try wp_auto
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
  try wp_auto
  wp_if_destruct
  · -- the read sequence numbers used up
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
    · inext
      unfold lockInv
      iexists _, mW, W, mR, Rd
      iframe
      ipureintro; exact HRdom
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  have Hns : uint.Z ns + 1 < 2 ^ 64 := by
    have : ns ≠ W64 18446744073709551615 := by assumption
    word
  have Hk64 : (key.length : Int) < 2 ^ 64 := by omega
  try wp_auto
  -- the read's context, minted at `(id, ns + 1)`
  imod kvr_mint_read γr id ns key l0 ⊤ CoPset.subseteq_top Hns Hk64 $$ Hinv Hseq Hl0
    with ⟨Hseq, #Hmint, #Hrc, #Hra⟩
  imod start_handoff ch (readAns γr (readCtxB id (ns + W64 1) key)) iprop(True) iprop(False) γc
    $$ Hch Hoc with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  have HRfresh : Rd !! (ns + W64 1) = none := by
    cases h : Rd !! (ns + W64 1) with
    | none => rfl
    | some ch' => have := HRdom _ _ h; word
  wp_apply wp_mapInsert go.uint64 mR Rd (ns + W64 1) ch $$ [$HRd] as HRd
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters Hns Hseq HmR HRd Hreads Hprod]
  · inext
    unfold lockInv
    iexists ns + W64 1, mW, W, mR, Rd.insert (ns + W64 1) ch
    iframe
    isplitr
    · ipureintro
      intro s ch' Hs
      by_cases Hss : s = ns + W64 1
      · subst Hss; exact Int.le_refl _
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hss)] at Hs
        have := HRdom _ _ Hs; word
    iapply (BigSepM.bigSepM_insert (Φ := fun s ch => readWaiterOk (GF := GF) γr id s ch) HRfresh).2
    iframe Hreads
    unfold readWaiterOk
    iexists readCtxB id (ns + W64 1) key, γh
    iframe Hmint Hho Hprod
  try wp_auto
  wp_apply context.wp_Background
  try wp_auto
  wp_apply hWT tmo $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
  try wp_auto
  wp_apply wp_readCtx id (ns + W64 1) key Hkey $$ [$Hpkg] as %b ⟨Hb, -⟩
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  ihave #Hnc : nodeCtx ctx' cd $$ []
  · unfold nodeCtx; iright; iexact Hctx
  ihave #Hhch : isChan ch γh.chanName GoString $$ [Hho]
  · unfold isHandoff; icases Hho with ⟨$, -⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  wp_apply wp_node_ReadIndex n γr.cluster kvrRaftN id b (readCtxB id (ns + W64 1) key)
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
    iapply handoff_rcv_au γh ch (readAns γr (readCtxB id (ns + W64 1) key)) iprop(True)
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
    icases kvr_readAns_ok γr id (ns + W64 1) key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
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
    icases HL with ⟨%ns2, %mW2, %W2, %mR2, %Rd2, HL⟩
    iNamed HL
    try wp_auto
    wp_apply wp_mapDelete mR2 Rd2 (ns + W64 1) go.uint64
      (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$HRd] as HRd
    ihave Hreads := reads_drop γr id Rd2 (ns + W64 1) $$ Hreads
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
    · inext
      unfold lockInv
      iexists ns2, mW2, W2, mR2, GMap.delete (ns + W64 1) Rd2
      iframe
      ipureintro
      intro s ch' Hs
      by_cases Hss : s = ns + W64 1
      · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
      · rw [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs; exact HRdom s ch' Hs
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
          iapply handoff_rcv_au γh ch (readAns γr (readCtxB id (ns + W64 1) key)) iprop(True)
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
          icases kvr_readAns_ok γr id (ns + W64 1) key l0 v Hk64 $$ Hra Hl0 Hw with ⟨%L, #HL, %HLf⟩
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

end kvreconf
end EtcdGrove
end Perennial
