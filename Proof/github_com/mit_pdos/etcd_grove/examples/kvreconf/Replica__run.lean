/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__run.lean`. Lean-first
(no Rocq counterpart).

The loop keeps `runInv` (`RunInv.lean`). Each iteration `select`s on the node's `Ready` channel
(`isReadyChan_recvAu`) and `stopc` (the broadcast). On `stopc`'s close it sends the loop's
`nodeRunning 1` on `runDone` (the handoff's producer) and returns; it does the same when a `Ready`'s
entries do not fit (`fits`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__maybeSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__maybeCompact
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.fits
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.decodeState
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunBatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunReadyIdx
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

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

set_option hygiene false in
/-- `run`'s exit: the loop's `nodeRunning 1` sent on `runDone`, then `return`. -/
local macro "run_exit" : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_handoff_send ρ.rd ρ.rdc (fun _ => nodeRunning n γr.cluster kvrRaftN 1) iprop(True)
      iprop(False) () $$ [$(frameH `HrdH) $(frameH `Hprod) Hrun] as -
    · isplitl [Hrun]
      · iexact Hrun
      · itrivial
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  ))

theorem Replica.run.wp_proof
    (wp_applyEntry : Replica.applyEntry.spec (GF := GF) (hG := hG))
    (wp_install : Replica.install.spec (GF := GF) (hG := hG))
    (wp_answer : Replica.answer.spec (GF := GF) (hG := hG))
    (wp_maybeSnapshot : Replica.maybeSnapshot.spec (GF := GF) (hG := hG))
    (wp_maybeCompact : Replica.maybeCompact.spec (GF := GF) (hG := hG))
    (wp_fits : fits.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_decodeState : decodeState.spec (GF := GF) (hG := hG))
    (wp_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Snapshot.GetData.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG)) :
    Replica.run.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ f
  wp_start as ⟨#Hrr, Hstart, #Hsend⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  ihave Hinv := runInv_init γr vs id r n st ρ pending_ptr snapIndex_ptr $$ [Hstart pending snapIndex]
  · iframe
  wp_for Hinv
  wp_apply (lc := 2) wp_Ready γr.cluster kvrRaftN id n $$ [$Hraft $HisNode] as %ch #Hch
  try wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a `Ready`
    simp only [chan.blockingClausePre]
    icases isReadyChan_recvAu n ch γr.cluster kvrRaftN id _ _ rfl $$ Hch HisNode Hdrv
      with ⟨%γc, #Hchan, Hau⟩
    iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hchan
    iapply Hau $$ [$Hlc1 $Hlc2]
    inext
    iintro %rdv ⟨%ce, %es, %h, %L, #Hce, #Hcomm, Hrs, Hrest, Hdrv⟩
    ihave ⟨%Hidx, Hrest⟩ := kvr_readyRest_indices _ _ _ _ _ _ _ _ _ $$ Hrest
    try wp_auto
    cases L with
    | none =>
      ihave ⟨%Hin, Hrest⟩ := readyRest_ceInBatch _ _ _ _ _ _ _ _ $$ Hrest
      iunfold readyRest at Hrest
      icases Hrest with ⟨%msl, #Hes, Hmsl, Hmsok, #Hhs, #Hss, %Hbnd, Hsnap⟩
      iunfold readySnap at Hsnap
      icases Hsnap with ⟨%Hnull, Happ, #Hcef⟩
      wp_apply wp_fits rdv.Entries' es DFrac.discard $$ [$Hpkg $Hes] as %b ⟨-, %Hfit⟩
      cases b
      · run_exit
      have Hfit' := Hfit rfl
      try wp_auto
      wp_apply wp_IsEmptySnap rdv.Snapshot' DFrac.discard none $$ [$Hraft] as %b2 ⟨%Hb2, -⟩
      · unfold snapOpt; ipureintro; exact Hnull
      subst Hb2
      try wp_auto
      sorry
    | some l =>
      sorry
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed: `nodeRunning 1` sent on `runDone`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ρ.stopc, ρ.sc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    run_exit
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
