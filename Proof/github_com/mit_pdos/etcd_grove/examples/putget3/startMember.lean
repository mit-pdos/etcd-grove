/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/putget3/startMember.lean` (D21 stage M5,
2026-10-19). Lean-first (no Rocq counterpart).

The steps (putget's `Main` up to `Start`, for one member, plus the raft handler): the
configuration's literal (its client URLs, the feature gate); a fresh storage registry
(D19r (B): each member's `bootstrap` joins its own); `NewServer` (its premises from the literal,
the member's ghost state and `bootstrap`'s contract); `net.Listen` at the peer address;
`s.RaftHandler()` (from `NewServer`'s `srvNetMember`); `go http.Serve(l, h)` (the peer address one
of the member's URLs in the directory); `s.Start()`. Every step's error returns it, with the
thread token, which `Start` would take.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.putget3.startMember
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Spec.net.http.Serve
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

theorem startMember.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [MemStorReg GF] [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_Serve : net.http.Serve.spec (GF := GF) (hG := hG)) :
    startMember.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client peer cluster lg sl₁ sl₂ sl₃ ps bootLog dir id γ bud ρ E₀ Φs γn
    Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen Hγn1 Hγn2 Hdir Hlg Hck Haf Hbuq Hnoc
  wp_start as ⟨Haddr, Htok, #Hpeer, #Hcl, #Hs1, #Hs2, #Hs3, #Hboot, #Hcom, #Hcci, Hmb, Hslot⟩
  iunfold bootPremise at Hboot
  iunfold commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  iunfold memberBoot at Hmb
  icases Hmb with ⟨%Hρ, Hghost, #Hcomm, #Hcinv, #Hbinv, #Hlb, #Hidc, #HNZ0, #Hpmint, #Hrdctx,
    Hids, HrdCred, Hidx, Hcok, Hrev, Hnk, #Hkvinv⟩
  obtain ⟨hraft, hpol, hc0, hch, hlog, hcok, hwl, hpfx, hΦs⟩ := Hρ
  -- the imports' package facts
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- the configuration's client URLs
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  -- the member's storage registry (D19r (B)), its `bootstrap`'s to join
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%γreg, Hreg⟩
  letI : MemStorReg GF := ⟨γreg⟩
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  have hblen' : γ.reBoot.length ≤ 2 ^ 60 := by rw [hboot]; exact hblen
  wp_apply (wp_NewServer _ ⟨[httpURL peerAddr], [httpURL client],
      GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅)), initURLs3⟩
      γ bud id bootLog ρ E₀ N Φs γn dir hraft hpol hc0 hch hlog hcok
      (by rw [hwl]; exact putgetWorkload_noGrant) Hlg (by simp) rfl Htb Hrb48 HrbN
      -- (D21 M3) the run bound: `SnapshotCatchUpEntries` is `2 ^ 48`
      (by
        have h48 : uint.Z (W64 281474976710656 : w64) = 2 ^ 48 := by rfl
        have hne : (W64 281474976710656 : w64) ≠ W64 0 := by decide
        simp only [hne, if_false, h48]
        omega)
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩)
    $$ [Hghost HrdCred Hids Hidx Hcok Hrev Hnk Hreg Hslot] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, ?_, hcfg, hdyn, hcc, hboot, htr, htx⟩
      · unfold cfgOk; simp
      · exact ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hcl; rfl
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₂ ≠ name₃),
          GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₃)]; rfl)).2
      isplitr; · iexact Hs3
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₂)]; rfl)).2
      isplitr; · iexact Hs2
      iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
      isplitr; · iexact Hs1
      iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hnoc
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γrn, %b, %HE, #Hwb, Hbuilt, Hgap,
    Hserve, Hsv, Hmon, #Hnm⟩)
  · -- `NewServer` failed: the error returned
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `net.Listen("tcp", peerAddr)`
  wp_apply (wp_Listen go!"tcp" peerAddr) $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Hlerr
  wp_auto
  -- `go http.Serve(l, s.RaftHandler())`
  wp_apply (wp_RaftHandler srv γn id) as %h #Hh
  · iframe #
  (try wp_auto)
  wp_apply wp_fork $$ [Hlis]
  · wp_apply (wp_Serve lis h peerAddr γn id) $$ [Hlis] as %serr -
    · iframe Hlis Hh; ipureintro; rw [Hγn2]; exact Hdir
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  -- `s.Start()`
  ihave Hsb := isServerBuilt_of_gap srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV N
    $$ [Hbuilt Hgap]
  · iframe
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hwpi, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    iexists _
    iframe Hmf Hfgc
  wp_apply (wp_Start srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV N HrbN rfl)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm] as ⟨%γw, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iunfold memberUp
  iexists E, _, γw
  iframe
  iframe #
  ipureintro
  exact ⟨HE.1, HE.2, rfl, rfl, rfl⟩

end proof

end putget3
end EtcdGrove
end Perennial
