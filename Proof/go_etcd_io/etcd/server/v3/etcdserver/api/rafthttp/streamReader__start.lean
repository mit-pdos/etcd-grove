/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__start.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__run
public import Spec.context.WithCancelBackground
public import Perennial.Spec.context.Background
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.streamReader.start.wp_proof
    (hRun : rafthttp.streamReader.run.spec (GF := GF) (hG := hG))
    (hWithCancel : context.WithCancelBackground.spec (GF := GF) (hG := hG))
    (hBackground : context.Background.spec (GF := GF) (hG := hG)) :
    rafthttp.streamReader.start.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr ty dc0 cf0 Hmem Hnp
  wp_start as ⟨#H0, #Hcfg, Hdone, Herrc, Hctx, Hcancel⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %dc %γdn ⟨#Hdcc, %-, Hdco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γdn dc $$ Hdcc Hdco with Hdb
  icases ownBroadcastChan_open _ _ _ _ $$ Hdb with ⟨%γdch, #Hdint, Hdown⟩
  ihave #Hdunk : ownBroadcastChan dc γdn iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdch
    iframe #
  ihave Hdb := ownBroadcastChan_close dc γdn iprop(True) .Pending γdch $$ [$Hdint $Hdown]
  ihave #Hcfg' := Hcfg
  iunfold srCfg at Hcfg'
  icases Hcfg' with ⟨%rl, %pk, %tr, %urls, %uvs, %cid, %rt, %ec, -, -, -, -, -, #Htr, -, -, -, -,
    -, #Hec, -, -, -⟩
  (try wp_auto)
  -- `cr.ctx == nil`: a cancellable context
  wp_apply hBackground
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply hWithCancel as %ctx' %γc %cancel ⟨#Hcf, #Hctx'⟩
  (try wp_auto)
  ipersist Hdone; ipersist Herrc; ipersist Hctx; ipersist Hcancel
  ihave #Hfixed := srFixed_intro Rh lid pid γd cr ctx' _ $$ H0 Hctx Hctx'
  wp_apply wp_fork $$ [Hdb]
  · (try wp_auto)
    wp_apply hRun Rh lid pid γd cr ty Hmem Hnp $$ [Hdb]
    · iframe #
      isplitr
      · iunfold srDial
        iframe #
      iunfold srDoneRight
      iexists dc, γdn
      iframe; iframe #
    ipureintro; exact isPanic_intoVal _
  (try wp_auto)
  iapply HΦ
  iframe #
  iunfold srStopRight
  iexists cancel, γc, dc, γdn
  iframe #

end proof

end EtcdGrove
end Perennial
