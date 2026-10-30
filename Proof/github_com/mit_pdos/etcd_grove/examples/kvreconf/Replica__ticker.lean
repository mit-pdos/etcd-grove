/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__ticker.lean`. Lean-first
(no Rocq counterpart).

`time.NewTicker` at the replica's positive interval; the loop's `select`: a tick (Perennial's
ticker channel is a bag of times) is `node.Tick` over `isNode`; `stopc`'s close (the broadcast,
`Unknown`) stops the ticker and sends on `tickDone` with the producer's token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__ticker
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop

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

theorem Replica.ticker.wp_proof (wp_NewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (wp_TStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (wp_Tick : node.Tick.spec (GF := GF) (hG := hG)) :
    Replica.ticker.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ
  wp_start as ⟨#HR, Hprod⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  icases Htick with ⟨%tk, #Htk, %Htkpos⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply (lc := 2) wp_NewTicker tk as %t %tch %γt #Ht
  · ipureintro; exact Htkpos
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HtC, #HtI, #Htbag⟩
  try wp_auto
  wp_for
  try wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm0 -
    wp_auto_lc 2
    wp_apply wp_Tick n γr.cluster kvrRaftN id $$ [$Hraft $HisNode]
    try wp_auto
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ρ.stopc, ρ.sc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    try wp_auto
    wp_apply wp_TStop t $$ []
    · iexists tch, γt; iexact Ht
    try wp_auto
    wp_apply wp_handoff_send ρ.td ρ.tdc (fun _ => iprop(True)) iprop(True) iprop(False) ()
      $$ [$HtdH $Hprod] as -
    · isplitl <;> itrivial
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
