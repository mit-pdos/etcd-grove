/- Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__runLoop.lean`. Lean-first. -/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__runLoop
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__revokeExpiredLeases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__checkpointScheduledLeases
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.runLoop.wp_proof
    (wp_NewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (wp_TStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (hRev : lease.lessor.revokeExpiredLeases.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.checkpointScheduledLeases.spec (GF := GF) (hG := hG)) :
    lease.lessor.runLoop.spec (GF := GF) (hG := hG) := by
  intro lp γl GA ri d γd
  wp_start as ⟨#Hinv, #Hcfg, #Hexp, #Hguard, #Hstr, #Hri, #Hd, Hdone, Hrd, Htok, Htt, %Htb⟩
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hstr' := Hstr
  iunfold lessorStopRecv at Hstr'
  icases Hstr' with ⟨%sc, %γts, #Hsc, #Hsr⟩
  iunfold onceRecv at Hsr
  icases Hsr with ⟨%γcs, #Hchs, #Hcis⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_NewTicker as %t %tch %γt #Ht
  · ipureintro; decide
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HtC, #HtI, #HtR, #Htbag⟩
  (try wp_auto)
  ihave IH : iprop(lessorRd lp γl ∗ notifRTok γl ∗ levelTok leaseLvl) $$ [Hrd Htok Htt]
  · iframe
  wp_for IH
  icases IH with ⟨Hrd, Htok, Htt⟩
  (try wp_auto)
  wp_apply (hRev lp γl GA ri) $$ [$Hpkg $Hinv $Hcfg $Hexp $Hguard $Hri $Hrd $Htok $Htt]
    as ⟨Hrd, Htok, Htt⟩
  · ipureintro; exact Htb
  (try wp_auto)
  wp_apply (lc := 2) (hCk lp γl) $$ [$Hpkg $Hinv]
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick: again
    simp only [chan.blockingClausePre]
    iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm0 -
    (try wp_auto)
    wp_for_post
    unfold named
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopC` closed: the deferred `Stop()` and `close(doneC)`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γcs
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hchs
    iapply once_recvAu γcs γts _ $$ Hcis
    iintro %v
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    wp_apply wp_TStop t $$ []
    · iexists tch, γt; iexact Ht
    (try wp_auto)
    wp_apply (wp_broadcast_chan_close d γd iprop(True)) $$ [$Hdone] as -
    · iintro !>; itrivial
    (try wp_auto)
    iapply HΦ
    iexact Htt
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
