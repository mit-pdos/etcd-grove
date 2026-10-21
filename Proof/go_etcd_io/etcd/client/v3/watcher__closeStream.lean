/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcher__closeStream.lean` (the watch slice's unit
W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__closeStream

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watcher.closeStream.wp_proof : watcher.closeStream.spec (GF := GF) (hG := hG) := by
  intro V G callSl
  wp_start as ⟨#Hw, #Hg, Hdc, #Hpub⟩
  iunfold isClientWatcher at Hw
  icases Hw with ⟨%wsl, %wvs, %Hwnn, #Hrem, #Hco, #Hvs, #Hok, #Hlg, #Hmu, #Hf, %Hlgnn⟩
  iunfold isWGS at Hg
  icases Hg with ⟨%Hgnn, #Hcv, #Hsf, %Hlg', #Howner, #Hremote, #Hcallo, #Hctx, #Hckey, #Hcancel,
    #Hreqc, #Hrespc, #Hdonec, #Herrc, #Hclosingc, #Hglg, #HisCtx, #Hcspec, #Hbreq, #Hberr, #Hbcl,
    #Hbdone, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  wp_apply wp_broadcast_chan_close G.donec G.γdone (closeErrPub G.wgs) $$ [$Hdc] as -
  · iframe #
  iunfold context.cancelSpec at Hcspec
  wp_bind (App (Val #G.cancel) (Val #()))
  iapply Hcspec
  · itrivial
  inext
  iintro -
  wp_auto
  iunfold watcherMu at HR
  icases HR with ⟨%m, Hst, HM⟩
  wp_auto
  icases HM with (%Hnil | ⟨%M, HM, #HMs⟩)
  · subst Hnil
    simp only [show (null : Loc) = map.nil from rfl, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst]
    · inext
      unfold watcherMu
      iexists map.nil
      iframe Hst
      ileft; ipureintro; rfl
    iapply HΦ; itrivial
  · by_cases hm : m = map.nil
    · simp only [hm, _root_.decide_true]
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HM]
      · inext
        unfold watcherMu
        iexists map.nil
        iframe Hst
        iright
        iexists M
        iframe HM
        iframe #
      iapply HΦ; itrivial
    · simp only [hm, _root_.decide_false]
      wp_auto
      wp_apply wp_mapDelete $$ [$HM] as HM
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HM]
      · inext
        unfold watcherMu
        iexists m
        iframe Hst
        iright
        iexists _
        iframe HM
        iapply (BigSepM.bigSepM_subseteq (GMap.delete_subseteq M G.ckey)) $$ HMs
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
