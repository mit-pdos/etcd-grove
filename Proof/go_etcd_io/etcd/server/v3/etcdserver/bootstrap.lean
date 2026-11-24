/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrap.lean`: `bootstrap(cfg)` at a first
start (`bootstrap.go:53-130` at the etcd pin `edc800c6f`), straight-line over its callees' specs and
the laws of `BootParts.lean`. Lean-first; claim #34, stage 3 (2026-11-23),
`notes/bootstrap-proof-plan.md` §7.3.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapCluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapStorage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedCluster__Finalize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRaft
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedBackend__Close
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__MemberDir
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__WALDir
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__PeerDialTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NewRoundTripper
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Uint
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int
public import Spec.fmt.ErrorfWrap

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section gaps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A network for `bootstrapCluster`'s round tripper (any does: `rafthttp.NewRoundTripper.spec` and
`bootstrapCluster.spec` hold of every network, and `bootstrap` sends nothing). -/
def bootstrap.anyNet : http.HttpNet GF where
  proto _ :=
    { req := (fun _ _ => (iprop(True) : IProp GF))
      req_pers := (fun _ _ => inferInstance)
      resp := (fun _ _ _ _ => (iprop(True) : IProp GF))
      resp_pers := (fun _ _ _ _ => inferInstance)
      rhdr := (fun _ _ => True)
      streamed := (fun _ => False)
      sreq := (fun _ _ _ _ => (iprop(True) : IProp GF))
      sreq_pers := (fun _ _ _ _ => inferInstance) }

end gaps

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

theorem bootstrap.wp_proof
    (hSnap : bootstrapSnapshot.spec (GF := GF) (hG := hG))
    (hBack : bootstrapBackend.spec (GF := GF) (hG := hG))
    (hClus : bootstrapCluster.spec (GF := GF) (hG := hG))
    (hStor : bootstrapStorage.spec (GF := GF) (hG := hG))
    (hFin : bootstrappedCluster.Finalize.spec (GF := GF) (hG := hG))
    (hRaft : bootstrapRaft.spec (GF := GF) (hG := hG))
    (hClose : bootstrappedBackend.Close.spec (GF := GF) (hG := hG))
    (hTouchD : bootFs.touchData.law (GF := GF) (hG := hG))
    (hTouchM : bootFs.touchMember.law (GF := GF) (hG := hG))
    (hExist : bootFs.walExist.law (GF := GF) (hG := hG))
    (hMemberDir : config.ServerConfig.MemberDir.spec (GF := GF) (hG := hG))
    (hWALDir : config.ServerConfig.WALDir.spec (GF := GF) (hG := hG))
    (hPDT : config.ServerConfig.PeerDialTimeout.spec (GF := GF) (hG := hG))
    (hNRT : rafthttp.NewRoundTripper.spec (GF := GF) (hG := hG))
    (hBytes : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hUint : zap.Uint.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hInt : zap.Int'.spec (GF := GF) (hG := hG))
    (hWrap : fmt.ErrorfWrap.spec (GF := GF) (hG := hG)) :
    bootstrap.spec (GF := GF) (hG := hG) := by
  intro _ _ cfg U γ N HU Hfips HiOk Hvs Hlog Hmem
  wp_start as ⟨%Hpure, #Hzlg, Hfg, Hvoff, #Hro, Hrauth, Hres⟩
  obtain ⟨Hcok, Hfresh, Hwb, Hdb⟩ := Hpure
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_join (iprop(True) : IProp GF) with [] as -
  · ihave #Hhpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
    · iPkgInit
    ihave Hsi : (srvInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, ⟨%rs, #Hrs⟩⟩
    wp_apply hUint as %f0 -
    wp_apply hBytes as %hs -
    wp_apply hStr as %f1 -
    wp_apply hInt as %f2 -
    wp_apply hStr as %f3 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hWarn
    · iexact Hzlg
    wp_join_done
    itrivial
  · itrivial
  ihave #Hfpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
  · iPkgInit
  ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Hwpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ []
  · iPkgInit
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  -- `TouchDirAll(cfg.DataDir)`
  wp_apply (hTouchD cfg cfg.Logger') $$ [Hres] as %terr Ht
  · iframe Hres; iframe #
  icases Ht with (⟨%Hne, #Hte⟩ | ⟨%Heq, Hres⟩)
  · obtain ⟨ti, rfl⟩ : ∃ ti, terr = GoInterface.ok ti := by
      cases terr with
      | nil => exact absurd rfl Hne
      | ok ti => exact ⟨ti, rfl⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_auto
    rw [show (go!"cannot access data directory: %w" : GoString) =
      go!"cannot access data directory: " ++ go!"%w" from rfl]
    wp_apply (hWrap go!"cannot access data directory: " _ ti (DFrac.own 1) (by decide))
      $$ [$Hasl $Hte] as %e0 -
    iapply HΦ
    ileft; ipureintro; exact fun h => nomatch h
  subst Heq
  have Hfits : Fs.DirFits cfg.DataDir' := Hfresh.2.2.2
  have Hlen : cfg.DataDir'.length < 2 ^ 60 := by have := Hfits.1; omega
  wp_auto
  -- `TouchDirAll(cfg.MemberDir())`
  wp_apply (hMemberDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDD
  · iframe DataDirF
  wp_apply (hTouchM cfg cfg.Logger') $$ [Hres] as %terr Ht
  · iframe Hres; iframe #
  icases Ht with (⟨%Hne, #Hte⟩ | ⟨%Heq, Hmd⟩)
  · obtain ⟨ti, rfl⟩ : ∃ ti, terr = GoInterface.ok ti := by
      cases terr with
      | nil => exact absurd rfl Hne
      | ok ti => exact ⟨ti, rfl⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_auto
    rw [show (go!"cannot access member directory: %w" : GoString) =
      go!"cannot access member directory: " ++ go!"%w" from rfl]
    wp_apply (hWrap go!"cannot access member directory: " _ ti (DFrac.own 1) (by decide))
      $$ [$Hasl $Hte] as %e0 -
    iapply HΦ
    ileft; ipureintro; exact fun h => nomatch h
  subst Heq
  wp_auto
  iunfold bootFs.memberDir at Hmd
  icases Hmd with ⟨Hwp, Hdf, Hsdo⟩
  -- `bootstrapSnapshot(cfg)`
  wp_apply (hSnap cfg Hfits) $$ [Hdf] as %ss ⟨#Hss, Hsfree, Hff⟩
  · iframe Hdf; iframe #
  -- `rafthttp.NewRoundTripper(cfg.PeerTLSInfo, cfg.PeerDialTimeout())`
  wp_apply (hPDT cfg_ptr cfg.ElectionTicks' cfg.TickMs') as %dt -
  · iframe #
  wp_apply (hNRT bootstrap.anyNet) as %prt %perr Hprt
  icases Hprt with (%Hne | ⟨%Heq, #Hrt, %Htr⟩)
  · obtain ⟨pi, rfl⟩ : ∃ pi, perr = GoInterface.ok pi := by
      cases perr with
      | nil => exact absurd rfl Hne
      | ok pi => exact ⟨pi, rfl⟩
    wp_auto
    iapply HΦ; ileft; ipureintro; exact Hne
  subst Heq
  wp_auto
  -- `wal.Exist(cfg.WALDir())`: `false`
  iunfold bootFs.walPart at Hwp
  icases Hwp with ⟨%Hwd, Hwa⟩
  have Hwne : cfg.DedicatedWALDir' ≠ [] := by
    rw [Hwd]; unfold srvWalDirOf; simp
  wp_apply (hWALDir cfg_ptr DFrac.discard cfg.DedicatedWALDir' Hwne) as #HWD
  · iframe DedicatedWALDirF
  wp_apply (hExist cfg) $$ [Hwa] as Hwp
  · iframe #; iunfold bootFs.walPart; iframe Hwa; ipureintro; exact Hwd
  -- `bootstrapBackend(cfg, false)`
  wp_apply (hBack cfg N Hlen Hcok Hwb Hdb) $$ [Hfg Hvoff Hff] as %bkl %berr
    ⟨%Hberr, %bk, %γA, %cil, %d, %D, Hbk, %Hbk0, Hrows, Hnew, Hwbt⟩
  · iframe Hfg Hvoff Hff; iframe #
  subst Hberr
  wp_auto
  iunfold bootBackendRows at Hrows
  iNamed Hrows
  -- `bootstrapCluster(cfg, nil, prt)`
  wp_apply hInfo
  · iexact Hzlg
  wp_apply (hClus cfg U bootstrap.anyNet prt Hfresh HU Hfips HiOk) as %c %cerr Hc
  · iframe #
  icases Hc with (%Hne | ⟨%Heq, %bc, Hc, %Hbc, Hcb⟩)
  · obtain ⟨ci, rfl⟩ : ∃ ci, cerr = GoInterface.ok ci := by
      cases cerr with
      | nil => exact absurd rfl Hne
      | ok ci => exact ⟨ci, rfl⟩
    wp_auto
    iunfold bootBackendNew at Hnew
    iunfold backend.newPostK at Hnew
    icases Hnew with ⟨#HB, #HSC, Hleft, -⟩
    iunfold bootLeft at Hleft
    icases Hleft with ⟨-, Hopen⟩
    ipersist Hbk
    wp_apply (hClose bkl bk d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P))
      d.be) $$ [Hopen]
    · iframe Hopen; iframe Hbk HB HSC; ipureintro; exact Hbe.1
    iapply HΦ; ileft; ipureintro; exact Hne
  subst Heq
  wp_auto
  -- `bootstrapStorage(cfg, backend, nil, cluster)`
  wp_apply hInfo
  · iexact Hzlg
  iunfold clusterBuilt at Hcb
  icases Hcb with ⟨%ms, %lgc, %rp, %dp, Hclg, #Hlgok, Hlid, Hcid, Hcbe, Hmu, Hver, Hmem0, Hrm,
    Hrmm, Hdg, Hdgv, Hml, Hvc⟩
  wp_apply (hStor cfg bkl c bc (DFrac.own 1) (DFrac.own 1) (bootGo.cid U cfg.InitialClusterToken'))
    $$ [Hwp Hc Hcid] as %sl ⟨%sto, %bw, Hs, Hbw, %Hsto, Hwal, Hc, Hcid⟩
  · iframe Hwp Hc Hcid; iframe #
  -- `cluster.Finalize(cfg, s)`
  obtain ⟨hstob, hbwlg, hhw, hst, hents, hsnap, hmeta⟩ := Hsto
  iunfold bootBackendNew at Hnew
  ihave Hbk : (sto.backend' ↦ bk : IProp GF) $$ [Hbk]
  · rw [hstob]; iexact Hbk
  wp_apply (hFin cfg U c sl bc sto bk bw d (fun _ => mvcc.api.mvccW d.gx)
      (fun γB => batchLockInv γA (metaTM γB d.P)) N D (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
      (DFrac.own 1) Hbc.2.2 Hbc.1 hhw Hbe.1 Hbe.2.2.2.2.2.2.2.2.2.2.2.1 Hbe.2.2.2.2.2.2.2.2.2.2.2.2.1
      Hbe.2.2.2.2.2.2.2.2.2.2.2.2.2)
    $$ [Hc Hs Hbk Hbw Hnew Hwbt Hclg Hlid Hcid Hcbe Hmu Hver Hmem0 Hrm Hrmm Hdg Hdgv Hml Hvc]
    as %ferr ⟨Hc, Hs, Hbk, Hbw, Hnew, Hfin⟩
  · iframe Hc Hs Hbk Hbw Hnew Hwbt; iframe #
    iunfold clusterBuilt
    iexists ms, lgc, rp, dp
    iframe Hclg Hlid Hcid Hcbe Hmu Hver Hmem0 Hrm Hrmm Hdg Hdgv Hml Hvc Hlgok
  icases Hfin with (%Hne | ⟨%Heq, Hdone⟩)
  · obtain ⟨fi, rfl⟩ : ∃ fi, ferr = GoInterface.ok fi := by
      cases ferr with
      | nil => exact absurd rfl Hne
      | ok fi => exact ⟨fi, rfl⟩
    wp_auto
    iunfold backend.newPostK at Hnew
    icases Hnew with ⟨#HB, #HSC, Hleft, -⟩
    iunfold bootLeft at Hleft
    icases Hleft with ⟨-, Hopen⟩
    ihave Hbk : (bkl ↦ bk : IProp GF) $$ [Hbk]
    · rw [← hstob]; iexact Hbk
    ipersist Hbk
    wp_apply (hClose bkl bk d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P))
      d.be) $$ [Hopen]
    · iframe Hopen; iframe Hbk HB HSC; ipureintro; exact Hbe.1
    iapply HΦ; ileft; ipureintro; exact Hne
  subst Heq
  wp_auto
  -- `bootstrapRaft(cfg, cluster, s.wal)`
  wp_apply hInfo
  · iexact Hzlg
  iunfold bootClusterDone at Hdone
  iNamed Hdone
  wp_apply (hRaft cfg U c sto.wal' bc bw (DFrac.own 1) (DFrac.own 1) Hfresh.1 Hcok Hbc.2.2 hhw hst
      hents hsnap) $$ [Hc Hbw Hrauth Hmem] as %rl ⟨%bv, Hr, Hraft, Hc, Hbw, Hmem⟩
  · iframe Hc Hbw Hrauth Hmem; iframe #
  -- the record, and `bootOk` from its parts
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  obtain ⟨bl, hB, hboot⟩ := Hlog
  have hlog : srvBootLogOk (bootGo.ps U cfg.InitialClusterToken') γ.boot := by
    rw [hboot]; exact srvBootLogOk_of_BootLog _ _ _ hB
  ihave Hbk : (sto.backend' ↦ bk : IProp GF) $$ [Hbk]
  · iexact Hbk
  ihave Hwal : wal.bootOk cfg (bootGo.id cfg U) (bootGo.cid U cfg.InitialClusterToken') bw.w' $$ [Hwal]
  · rw [← Hbc.1]; iexact Hwal
  iapply (bootOk_of_parts cfg U γ N _ _ sto bk bw bc bv γA cil d D Hvs hlog Hmem Hbc.2.2 Hbc.1
    Hbc.2.1 Hbk0.2)
  isplitl [«$r0»]
  · iexact «$r0»
  isplitl [Hs]
  · iexact Hs
  isplitl [Hbk]
  · iexact Hbk
  isplitl [Hbw]
  · iexact Hbw
  isplitl [Hc]
  · iexact Hc
  isplitl [Hr]
  · iexact Hr
  isplitr
  · ipureintro; exact Htr
  isplitl [Hwal]
  · iexact Hwal
  isplitr
  · iexact Hss
  isplitl [Hsdo]
  · iexact Hsdo
  isplitl [Hsfree]
  · iexact Hsfree
  isplitl [Hraft]
  · iexact Hraft
  isplitl [Hvcn HclBe Hmem]
  · iunfold bootClusterDone
    iframe Hvcn HclBe Hmem Hcl Hrc Hcid Hclg Hmembers Hisc
  isplitl [Hthr Happ Hown Hlate Hpath]
  · iunfold bootBackendRows
    iframe Hthr Happ Hown Hlate Hpath HisCI Hcons Hbh Hmeta HmetaSnap HhkAt Hbfile
    ipureintro; exact ⟨Hci, Hbe⟩
  · iunfold bootBackendNew
    iexact Hnew

end proof

end EtcdGrove
end Perennial
