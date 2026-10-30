/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/newReplica.lean`. Lean-first
(no Rocq counterpart).

The channels: `stopc` a broadcast (`Q := True`: its `Pending` token the stopper's, its `Unknown`
view in `isReplicaR`), `runDone` and `tickDone` handoffs (`start_handoff`: the producers' tokens to
`run` and `ticker`, the consumers' to the stopper). The configuration a clone of `cs0`, frozen
read-only (`csOpt`). The replica's lock at the empty state with the read-sequence element at `0`;
the applier's halves (`repOwn` at the empty prefix) to `run` (`runStart`), forked with `ticker`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.newReplica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__ticker
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__snapshotter
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Halves

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

theorem newReplica.wp_proof (wp_run : Replica.run.spec (GF := GF) (hG := hG))
    (wp_ticker : Replica.ticker.spec (GF := GF) (hG := hG))
    (wp_snapshotter : Replica.snapshotter.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    newReplica.spec (GF := GF) (hG := hG) := by
  intro γr vs id n st sts cs0 tick f ms γs hs Htick Hnd Hvl Hcsm
  wp_start as ⟨#Hcci, #Hcl, #Hstats, #HisNode, Hdrv, Hrun, Hcfg, #Hrec, #HmsInv, Hmeta,
    Hsnap, #Hcs0, #Hsend, Hseq⟩
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  try wp_auto
  -- the channels
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsc Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  wp_apply chan.wp_make2 (V := RSnapReq) (W64 1) as %snc %γsn ⟨#Hsnc, %_, Hsnoc⟩
  · ipureintro; decide
  ihave Hsnoc : ownChan γsn RSnapReq (.Buffered []) $$ Hsnoc
  imod start_bag (snapReqOk γr id γs) (.Buffered []) snc γsn trivial $$ Hsnc Hsnoc with #HsnB
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %rdc %γrc ⟨#Hrdc, %_, Hroc⟩
  · ipureintro; decide
  ihave Hroc : ownChan γrc Unit (.Buffered []) $$ Hroc
  imod start_handoff rdc (fun _ => nodeRunning n γr.cluster kvrRaftN 1) iprop(True) iprop(False) γrc
    $$ Hrdc Hroc with ⟨%γrd, -, #HrdH, HrdP, HrdC⟩
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %tdc %γtc ⟨#Htdc, %_, Htoc⟩
  · ipureintro; decide
  ihave Htoc : ownChan γtc Unit (.Buffered []) $$ Htoc
  imod start_handoff tdc (fun _ => iprop(True)) iprop(True) iprop(False) γtc
    $$ Htdc Htoc with ⟨%γtd, -, #HtdH, HtdP, HtdC⟩
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %sdc %γdc ⟨#Hsdc, %_, Hsdoc⟩
  · ipureintro; decide
  ihave Hsdoc : ownChan γdc Unit (.Buffered []) $$ Hsdoc
  imod start_handoff sdc (fun _ => iprop(True)) iprop(True) iprop(False) γdc
    $$ Hsdc Hsdoc with ⟨%γsd, -, #HsdH, HsdP, HsdC⟩
  -- the stored snapshot opened for the two writers (`run`'s `ApplySnapshot`, the snapshot
  -- goroutine's `CreateSnapshot`/`Compact`)
  imod memSnapNone_open γs $$ Hsnap with #HsnLb
  try wp_auto
  wp_apply wp_Clone.1 cs0 DFrac.discard (bootCS vs) $$ [$Hproto $Hcs0] as %csp ⟨-, Hcsp⟩
  try wp_auto
  imod csPts_persist csp (DFrac.own 1) (bootCS vs) false $$ Hcsp with #Hcsp
  wp_apply wp_map_make1 (K := List w8) (V := List w8) as %mK HK
  wp_apply wp_map_make1 (K := List w8) (V := List w8) as %mA HA
  wp_apply wp_map_make1 (K := List w8) (V := Loc) as %mW HW
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mRd HRd
  iStructNamed «$r0»
  ipersist id
  ipersist node
  ipersist storage
  ipersist stats
  ipersist tick
  ipersist stopc
  ipersist runDone
  ipersist tickDone
  ipersist snapc
  ipersist snapDone
  icases (typedPointsto_half_split _ _ 1).1 $$ applied with ⟨applied1, applied2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ cs with ⟨cs1, cs2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ index with ⟨index1, index2⟩
  icases ownMap_halves_split mA ∅ $$ HA with ⟨HA1, HA2⟩
  ihave #Hc0 := isCommittedLogLb_nil (GF := GF) γr.cluster
  ihave #HcsO : csOpt csp DFrac.discard (bootCS vs) $$ []
  · iunfold csOpt; iright; iexact Hcsp
  have HA0 : AppliedOk (∅ : GMap (List w8) (List w8)) (logHist []) := by
    refine ⟨fun d => ?_, fun d v h => ?_⟩
    · simp [logHist, histOf]
    · simp at h
  imod sync.init_Mutex (lockInv γr id «$r0_ptr») ⊤ («$r0_ptr».[RReplica, go!"mu"])
    $$ mu [waiters HW nextRead Hseq reads HRd applied2 HA2 cs2 index2] with #Hmu
  · inext
    unfold lockInv
    iexists W64 0, mW, ∅, mRd, ∅
    simp only [named]
    iframe waiters HW Hseq reads HRd
    rw [show (W64 0 : w64) = 0 from rfl]
    iframe nextRead
    isplitl [applied2 HA2 cs2 index2]
    · unfold repShared
      iexists mA, ∅, csp, bootCS vs, _, []
      simp only [named]
      iframe applied2 HA2 cs2 index2 HcsO Hc0
      ipureintro; exact HA0
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · ipureintro; intro s ch Hs; cases Hs
    iapply BigSepM.bigSepM_empty.2; itrivial
  ihave #Hrep : isReplica γr vs id «$r0_ptr» n st sts $$ []
  · unfold isReplica
    simp only [named]
    iframe #
  ihave #HR : isReplicaR γr vs id «$r0_ptr» n st sts ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd⟩ $$ []
  · unfold isReplicaR
    simp only [named]
    iframe #
    ipureintro; exact Htick
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨-, -, #Hca0, -, -⟩
  try wp_auto
  wp_apply wp_fork $$ [Hdrv Hrun Hcfg kv HK applied1 HA1 cs1 index1 HrdP Hmeta]
  · wp_apply wp_run γr vs id «$r0_ptr» n st sts ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd⟩ f
      $$ [$HR $Hsend Hdrv Hrun Hcfg kv HK applied1 HA1 cs1 index1 HrdP Hmeta]
    · unfold runStart
      iexists csp, mA, hs
      iframe Hdrv Hrun Hcfg HrdP Hmeta
      unfold repOwn
      iexists mK, ∅, bootCS vs
      simp only [named]
      rw [show (W64 0 : w64) = 0 from rfl]
      iframe kv HK applied1 HA1 cs1 index1 Hc0 HcsO Hca0
      ipureintro
      refine ⟨by simp, ?_, HA0, Hcsm, ?_⟩
      rotate_left
      · simp only [Membership.ids, Membership.simple, GMap.union_empty_r_L]
        rw [GMap.size_list_to_set vs Hnd]; omega
      intro k; simp [logHist, histOf, kvFold, kvEmpty]
    itrivial
  try wp_auto
  wp_apply wp_fork $$ [HtdP]
  · wp_apply wp_ticker γr vs id «$r0_ptr» n st sts ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd⟩
      $$ [$HR $HtdP]
    itrivial
  try wp_auto
  wp_apply wp_fork $$ [HsdP]
  · wp_apply wp_snapshotter γr vs id «$r0_ptr» n st sts ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd⟩
      $$ [$HR $HsdP]
    itrivial
  try wp_auto
  iapply HΦ
  isplitr
  · unfold isRep
    iexists n, st, sts, ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd⟩
    iexact HR
  unfold repStop
  iexists id, n, st, sts, ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd⟩
  iframe HR Hpend HrdC HtdC HsdC

end proof

end kvreconf
end EtcdGrove
end Perennial
