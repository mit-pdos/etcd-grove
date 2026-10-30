/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/sleep.lean`. Lean-first (no Rocq
counterpart).

`below`, `time.After` (a bag of times), then the blocking `select`: `stop`'s close (the broadcast,
`Unknown`) or a time.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.sleep
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Perennial.Spec.time.After

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

theorem sleep.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    sleep.spec (GF := GF) (hG := hG) := by
  intro pause stop γc
  wp_start as #Hstop
  try wp_auto
  wp_apply wp_below as %k -
  try wp_auto
  wp_apply (lc := 2) wp_After as %tch %γt #Htch
  try wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stop` closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stop, γc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstop
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstop
    iintro ⟨-, -⟩
    try wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the time
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %tm0 -
    try wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
