module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__leaseKeepAlive
public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.LeaseServer.LeaseKeepAlive.wp_proof
    (hLoop : v3rpc.LeaseServer.leaseKeepAlive.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseKeepAlive.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid E γl S' st γs Up Dn ci cd
  wp_start as ⟨#Hls, #HRn, #Hst, #Hspec, #HUp, Hrt, Hstt, HS, HR⟩
  ihave #Hst' := Hst
  iunfold srvStreamIs at Hst'
  icases Hst' with ⟨%si, %Hsi, -, -, #HCtx, #Hctxis, -⟩
  ihave #Hctx2 := Hctxis
  iNamed Hctx2
  ihave #Pv3 : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  wp_auto
  -- `errc`: the loop's error
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %errc %γe ⟨#Herrc, %-, Hoe⟩
  · ipureintro; decide
  let PE : Int → GoInterface → IProp GF := fun _ _ => iprop(True)
  imod start_spsc errc PE (fun _ => iprop(False)) γe $$ Herrc [Hoe]
    with ⟨%γerr, #HspscE, HprodE, HconsE⟩
  · iright; iexact Hoe
  ipersist errc
  ipersist ls
  ipersist stream
  wp_apply wp_fork $$ [Hrt Hstt HS HR HprodE]
  · wp_auto
    wp_apply hLoop p s A cid mid E γl S' st γs Up Dn ci cd $$ [$Hrt $Hstt $HS $HR] as %lerr -
    · iframe #
    wp_apply wp_spsc_send γerr errc PE (fun _ => iprop(False)) [] lerr $$ [$HprodE] as -
    · iframe #
    itrivial
  rw [Hsi]
  wp_auto
  wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
  iapply HCtx
  · itrivial
  iintro !> -
  wp_auto
  wp_apply +noauto HDone as %chD %γD #HcD
  wp_auto_lc 2
  ihave #HerrcC : isChan errc γerr.chanName GoInterface $$ [HspscE]
  · unfold isSpsc; icases HspscE with ⟨$, -⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `err = <-errc`: the loop's error
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, errc, γerr.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact HerrcC
    iapply spsc_rcv_au γerr errc PE (fun _ => iprop(False)) [] _ $$ HspscE [$Hlc1 $Hlc2] HconsE
    inext
    iintro %ve %okE -
    wp_auto
    iapply HΦ
    iframe #
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-stream.Context().Done()`: the context's error
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chD, γD
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ HcD
    iapply context.isContextDone_receive _ _ _ _ $$ HcD
    iintro ⟨#HPD, #HCC⟩
    wp_auto
    wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
    iapply HCtx
    · itrivial
    iintro !> -
    wp_auto
    wp_apply +noauto HErrDone $$ [$HCC] as %cerr -
    wp_auto
    iapply HΦ
    iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
