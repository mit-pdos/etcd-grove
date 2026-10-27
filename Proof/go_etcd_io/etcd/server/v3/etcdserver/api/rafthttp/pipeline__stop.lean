/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/pipeline__stop.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__stop
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Perennial.Spec.sync.WaitGroup__Wait

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.pipeline.stop.wp_proof
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG)) :
    rafthttp.pipeline.stop.spec (GF := GF) (hG := hG) := by
  intro Rh p to R
  wp_start as Hst
  iunfold pipeStarted at Hst
  icases Hst with ⟨#Hh, %sc, %γs, #Hsc, Hbc, Had⟩
  iunfold pipeHandleOk at Hh
  icases Hh with ⟨#Hs, -⟩
  iunfold pipeSenderOk at Hs
  icases Hs with ⟨%tr, %pk, %sc', %ec, %γs', %lg, %urls, %uvs, %lid, %cid, %rt, #Htr, -, -, -,
    #Hto, #Hlg, %Hlgnn, -, -, #Hlid, -, -, -, -, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_broadcast_chan_close sc γs iprop(True)) $$ [$Hbc] as -
  · imodintro; itrivial
  (try wp_auto)
  wp_apply +noauto (sync.join.WaitGroup.wp_Wait_of wp_Wait _ _ _) $$ [$Had] as ⟨HR, -⟩
  wp_auto_lc 1
  iapply wp_fupd
  imod lc_fupd_elim_later $$ Hlc1 HR with ⟨-, HR⟩
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals try (imodintro; iapply HΦ; iexact HR)
  wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls -
  wp_apply hZString as %f1 -
  wp_apply hIDStringPtr _ DFrac.discard to $$ [$Hto] as %ts -
  wp_apply hZString as %f2 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hInfo lg _ _ $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  imodintro; iapply HΦ; iexact HR

end proof

end EtcdGrove
end Perennial
