/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/startServer.lean` (the auth plan's
E3zb, 2026-10-28). Lean-first (no Rocq counterpart).

The steps (`common.StartServer`'s, `common.newServer`'s and `common.wp_Start_built`'s, with auth on):
the peer URL slice and the cluster's map `{authkv ↦ peer}` (read-only from here on, D19r (F)); the
configuration's client URLs and feature gate; `NewServer` with auth on (`NewServer.specM true`: the
simple provider, the TTL `300`), whose post gives the mode `.on γa`, the lessor finding no lease
(`srvLessorNil`) and the built part with auth on (`isServerBuilt_of_gapM true`); on success
`s.Start()` with auth on (`Start.specOn`). An error of `NewServer` returns it, with the thread token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.startServer
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem startServer.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.specM (GF := GF) (hG := hG) true)
    (wp_Start : EtcdServer.Start.specOn (GF := GF) (hG := hG)) :
    startServer.spec (GF := GF) (hG := hG) := by
  intro CS N lg bootLog ctxs dir id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs hdyn hboot hblen Hγn1 Hγn2
    Hdirok Hdir Hlg Hck Haf Hbuq Hdbo
  wp_start as ⟨Htok, #Hboot, #Hcom, #Hcci, Hmb, #Hnet⟩
  iunfold common.bootPremise at Hboot
  iunfold common.commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  iunfold common.memberBootOn at Hmb
  icases Hmb with ⟨%Hρ, Hnboot, #Hsrl, #Hidc, #HNZ0, #Hpmint, #Hrdctx,
    Hids, HrdCred, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv, Hreg, %γd, %Hsloc, Hsdir⟩
  obtain ⟨hraft, hdyn', hc0, hch, hlog, hcok, hpfx, hΦs⟩ := Hρ
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- the peer URL slice and the cluster's map, read-only from here on (D19r (F))
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer ⟨Hpeer, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  (try wp_auto)
  -- the configuration's client URLs
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert go!"authkv" (slice.mk peer (W64 1) (W64 1)) ∅,
      sl ↦*□ (fun _ => [common.httpURL go!"127.0.0.1:23926"]) k $$ []
  · iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iExactEq Hpeer; rfl
    iapply BigSepM.bigSepM_empty.2; itrivial
  letI : MemStorReg GF := ⟨γ.reg⟩
  have hblen' : γ.boot.length ≤ 2 ^ 60 := by rw [hboot]; exact hblen
  -- `NewServer(cfg)` with auth on
  wp_apply (wp_NewServer _ ⟨[common.httpURL go!"127.0.0.1:23926"],
        [common.httpURL go!"127.0.0.1:23916"],
        GMap.insert go!"authkv" (slice.mk peer (W64 1) (W64 1)) ∅,
        fun _ => [common.httpURL go!"127.0.0.1:23926"]⟩
      γ id ctxs ρ E₀ N Φs γn dir γd hraft hdyn hc0 hch hlog hcok
      Hlg ⟨by simp, by simp [mvcc.rangeLimitMax]⟩ rfl Htb Hrb48 HrbN
      (by
        have h48 : uint.Z (W64 281474976710656 : w64) = 2 ^ 48 := by rfl
        have hne : (W64 281474976710656 : w64) ≠ W64 0 := by decide
        simp only [hne, if_false, h48]
        omega)
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩ Hdirok
      (common.peerURLsDir_httpURL dir id _ Hdirok Hdir)
      (fun _ => ⟨rfl, by word, by word⟩))
    $$ [Hnboot HrdCred Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hsdir] as %srv %err Hres
  · simp only [hdyn, Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩, hvs, hdyn, hboot⟩
      unfold common.cfgOk; simp
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hpm; rfl
      iexact Hsls
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hsloc
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hdbo
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %HE, #Hwb, -, -,
    Hbuilt, Hgap, Hserve, Hsv, Hmon, Hrc, #Hnm, Htokp, -, HWR, #HLnil⟩)
  · -- `NewServer` failed: the error returned, with the thread token
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  obtain ⟨hagree, -, hγa⟩ := HE
  obtain ⟨γa, hγa⟩ := hγa trivial
  -- what `Start` takes: the built part with auth on, the monitors off
  ihave Hsb : isServerBuiltOn srv γA ci TM E ρ ρ.rd
      (srvErM true ρ E₀ (W64 0) (W64 0) (bootKVOf true) id (srvTrKey γn γk)) γrn b (W64 0) (W64 0)
      (W64 0) (bootKVOf true) N $$ [Hbuilt Hgap]
  · rw [← isServerBuiltM_true]
    iapply isServerBuilt_of_gapM
    iframe
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    iexists _
    iframe Hmf Hfgc
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hwpi, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  -- `s.Start()` with auth on
  wp_apply (wp_Start srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) (bootKVOf true) N γa
      hγa Hrb48 HrbN rfl)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, #Hlb, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists γa
  iunfold common.memberUpOn
  iexists E, _, γw
  iframe
  iframe #
  isplitr
  · ipureintro; exact ⟨hagree, hγa, rfl, rfl, rfl⟩
  iunfold common.srvPeerCtl
  iexists τ
  iframe Hnm Htokp

end proof

end authkv
end EtcdGrove
end Perennial
