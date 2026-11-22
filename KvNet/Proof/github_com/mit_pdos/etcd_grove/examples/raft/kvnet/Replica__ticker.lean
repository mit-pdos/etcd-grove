/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Replica__ticker.lean`. Lean-first
(no Rocq counterpart). kvreconf's proof (the same Go text), ported.

`time.NewTicker` at the replica's positive interval; the loop's `select`: a tick (Perennial's
ticker channel is a bag of times) is `node.Tick` over `isNode`; `stopc`'s close (the broadcast,
`Unknown`) stops the ticker and sends on `tickDone` with the producer's token.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica__ticker
public import KvNet.Spec.go_etcd_io.raft.v3.node__Tick
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Replica.ticker.wp_proof (wp_NewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (wp_Tick : node.Tick.spec (GF := GF) (hG := hG)) :
    Replica.ticker.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ρ
  wp_start as #HR
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
  icases Ht' with ⟨#HtC, #HtI, #HtR, #Htbag⟩
  try wp_auto
  wp_for
  wp_apply wp_bag_receive (t := time.Time.ty) γt tch _ $$ Htbag as %tm0 -
  try wp_auto
  wp_apply wp_Tick n γ.r.cluster kdRaftN id $$ [$Hraft $HisNode]
  try wp_auto
  wp_for_post
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
