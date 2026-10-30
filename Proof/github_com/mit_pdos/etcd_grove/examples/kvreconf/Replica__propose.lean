/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__propose.lean`. Lean-first
(no Rocq counterpart); kv's `KV.do` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/KV__do.lean`)
with a timeout and the replica's table of applied operations.

Under the lock: an operation applied here is answered from the applied table (`AppliedOk`, at a
committed prefix: `waitP`); otherwise a handoff channel is registered as the datum's waiter
(`waiterOk`). Every proposal takes the persistent update `kvr_propAu`. The answer comes through the
handoff: in the blocking `select` (against the context's `Done`), or, once the waiter is deleted, in
the non-blocking one (`recvAu_nonblocking`); a timeout answers nothing.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__propose
public import Spec.context.WithTimeoutBackground
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientAu
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

theorem Replica.propose.wp_proof
    (wp_node_Propose : node.Propose.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Replica.propose.spec (GF := GF) (hG := hG) := by
  intro γr vs id r d γp opsl tmo
  wp_start as ⟨#HisRep, #Hop, #Hopsl⟩
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
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_bytes_to_string opsl d DFrac.discard $$ [Hopsl] as -
  · iexact Hopsl
  try wp_auto
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  imod start_handoff ch (waitP γr d) iprop(True) iprop(False) γc $$ Hch Hoc
    with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
  iNamed Hrep
  try wp_auto
  wp_apply wp_map_lookup2 go.string go.string mA A d (DFrac.own (1 : Qp).half) $$ [$HA] as HA
  cases HAd : A !! d with
  | some v =>
    simp only [Option.isSome_some, _root_.decide_true]
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmW HW Hwaiters Hns Hseq HmR HRd Hreads HmA HA
      Hcs Hidx]
    · inext
      unfold lockInv
      iexists ns, mW, W, mR, Rd
      iframe
      isplitl
      · unfold repShared
        iexists mA, A, csp, c, idx, ap
        iframe
        iframe HcsO Hap
        ipureintro; exact HA
      · ipureintro; exact HRdom
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    unfold waitP
    iexists ap
    iframe Hap
    ipureintro; exact HA.2 d v HAd
  | none =>
    simp only [Option.isSome_none, decide_false, Bool.false_eq_true]
    try wp_auto
    wp_apply wp_mapInsert go.string mW W d ch $$ [$HW] as HW
    ihave Hwaiters := BigSepM.bigSepM_insert_elim (Φ := fun d ch => waiterOk (GF := GF) γr d ch)
      (m := W) (i := d) (x := ch) $$ [Hho Hprod] Hwaiters
    · unfold waiterOk
      iexists γh
      iframe Hho Hprod
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmW HW Hwaiters Hns Hseq HmR HRd Hreads HmA HA
      Hcs Hidx]
    · inext
      unfold lockInv
      iexists ns, mW, W.insert d ch, mR, Rd
      iframe
      isplitl
      · unfold repShared
        iexists mA, A, csp, c, idx, ap
        iframe
        iframe HcsO Hap
        ipureintro; exact HA
      · ipureintro; exact HRdom
    try wp_auto
    wp_apply context.wp_Background
    try wp_auto
    wp_apply hWT tmo $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
    try wp_auto
    ihave #Hhch : isChan ch γh.chanName GoString $$ [Hho]
    · unfold isHandoff; icases Hho with ⟨$, -⟩
    ihave #Hctx' := Hctx
    iNamed Hctx'
    ihave #Hpau := kvr_propAu_dup γr d γp $$ Hinv Hop
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    ihave HI : iprop(True) $$ []
    · itrivial
    wp_for HI
    wp_apply wp_node_Propose n γr.cluster kvrRaftN id opsl d ctx' cd
      $$ [$Hraftinit $HisNode $Hnc $Hopsl $Hpau] as %err -
    try wp_auto
    cases err
    case' ok i =>
      try wp_auto
      ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU $$ [] as %err' -
      try wp_auto
      cases err'
      case' nil =>
        -- dropped, the context live: propose again
        try wp_auto
        simp only [_root_.decide_true, ↓reduceIte]
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
    all_goals
      try wp_auto
      rw [ite_eq_right (by simp only [decide_eq_true_eq]; intro h; cases go.intoVal_inj (V := Bool) h),
        ite_eq_left (by simp)]
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
        iapply handoff_rcv_au γh ch (waitP γr d) iprop(True) iprop(False) false _ $$ Hho Hlc1 Hcons
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
        iexact Hw
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
        iNamed HL
        try wp_auto
        wp_apply wp_map_lookup1 go.string (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
          mW W d (DFrac.own 1) $$ [$HW] as HW
        try wp_auto
        -- the waiter deleted, if it is still this one
        wp_if_destruct
        all_goals first
          | (wp_apply wp_mapDelete mW W d go.string (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
                $$ [$HW] as HW
             ihave Hwaiters := waiters_drop γr W d $$ Hwaiters
             generalize GMap.delete d W = W')
          | generalize W = W'
        all_goals
          try wp_auto
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
          · inext
            unfold lockInv
            iexists ns, mW, W', mR, Rd
            iframe
            ipureintro; exact HRdom
          try wp_auto
          -- an answer sent before the waiter was deleted, if any
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
                iapply handoff_rcv_au γh _ (waitP γr d) iprop(True) iprop(False) false _
                  $$ Hho Hlc1 Hcons
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
                iexact Hw
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
