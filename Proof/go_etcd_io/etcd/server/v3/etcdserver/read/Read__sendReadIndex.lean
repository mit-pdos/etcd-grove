/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__sendReadIndex.lean`. Lean-first (no
Rocq counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__sendReadIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.uint64ToBigEndianBytes
public import Spec.context.WithTimeoutBackground
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.isStopped

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

theorem read.Read.sendReadIndex.wp_proof
    (hB : read.uint64ToBigEndianBytes.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    read.Read.sendReadIndex.spec (GF := GF) (hG := hG) := by
  intro r γr RQ LR NR id n
  wp_start as ⟨#Hpre, HLR, #Hc⟩
  iunfold isReadLoopPre at Hpre
  icases Hpre with ⟨%srv, %rf, %wc, %γw, #Hsf, #Hsrv, #Hrf, #Hraft, -, -, -, -, #Hcci⟩
  iunfold isReadServer at Hsrv
  icases Hsrv with ⟨-, %si, %Hsi, -, -, -, #HLg, -, -, -, #HRT⟩
  iunfold isReadRaft at Hraft
  icases Hraft with ⟨%ri, %Hri, -, #HRI⟩
  subst Hsi Hri
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨%cF, #HcF, #HcFs⟩, -, -, -, -, #HR, -, -⟩
  iunfold errVarLeaf at HR
  icases HR with ⟨%eR, #HeR, %HlR, -⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply hB as %sl Hsl
  wp_apply context.wp_Background
  wp_apply HRT as %d -
  wp_apply hWT d $$ [] as %cctx %cd %cancel ⟨#Hcancel, #Hcctx⟩
  · iframe #
  wp_apply HRI $$ %cctx %cd %sl %_ %id %n [Hsl] as %err ⟨Hsl, #HerrE, Hrq⟩
  · iframe #; iframe Hsl
  wp_auto
  wp_apply Hcancel
  wp_apply read_wp_Is_var hIs err eR HlR as %b -
  · iframe #
  cases b
  · cases err with
    | ok ei =>
      wp_auto
      wp_apply HLg $$ [HLR] as %lg ⟨%Hlg, HLR⟩
      · iexact HLR
      wp_apply hZE as %f -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fs ⟨-, -⟩
      (try wp_auto)
      wp_apply hW lg _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at HcFs
      icases HcFs with ⟨#HInc, -⟩
      (try wp_auto)
      wp_apply HInc
      (try wp_auto)
      iapply HΦ
      iframe HLR HerrE Hrq
    | nil =>
      wp_auto
      iapply HΦ
      iframe HLR HerrE Hrq
  · wp_auto
    iapply HΦ
    iframe HLR HerrE Hrq

end proof

end EtcdGrove
end Perennial
