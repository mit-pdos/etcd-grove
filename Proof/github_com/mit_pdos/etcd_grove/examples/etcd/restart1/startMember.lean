/-
Proofs of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/startMember.lean` (restart S7.5,
2026-11-14): the peer URL slice and the cluster's map, `etcdstart.BuildServer`, `s.Start()`.
`etcdstart.StartServer`'s proof over `BuildServer.spec` (`wp_proof`) and `BuildServer.specRestart`
(`wp_proofRestart`; restart3 A1, 2026-11-15: no restart-only rows to discharge, until then
`srvRestartRows_single`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BuildServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartStop
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

theorem startMember.wp_proof
    (wp_BuildServer : etcdstart.BuildServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    startMember.spec (GF := GF) (hG := hG) := by
  intro CS N lg bootLog ctxs id γ ρ E₀ Φs γn ThB RcB RcN HwbN hvs hrule hboot hblen Hγn1 Hγn2
    Hdirok Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hboot, #Hcci, Hmb, #Hnet, Hfresh⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  -- the peer URL slice and the cluster's map, read-only from here on
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer ⟨Hpeer, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hq : (slice.mk peer (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr] $$ []
  · iExactEq Hpeer; rfl
  ihave #Hcm : pm ↦$□ GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅ $$ []
  · iExactEq Hpm; rfl
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅,
      sl ↦*□ (fun _ => [etcdstart.httpURL peerAddr]) k $$ []
  · iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iexact Hq
    iapply BigSepM.bigSepM_empty.2; itrivial
  -- `etcdstart.BuildServer(name, peer, clientAddr, {name: peer}, name, SnapCount, SnapCatchUp, lg)`
  wp_apply (wp_BuildServer N name peerAddr clientAddr name (W64 1) (W64 1)
      (slice.mk peer (W64 1) (W64 1)) pm lg
      (GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅) (fun _ => [etcdstart.httpURL peerAddr])
      urlsOk [id] bootLog ctxs (dir id) id γ ρ E₀ Φs γn .none HwbN hvs hrule hboot hblen Hγn1 Hγn2
      Hdirok (by simp [etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _)
      ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩ (by decide) (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty)
      (by decide) Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh] as %s %err Hres
  · iframe; iframe #
  icases Hres with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, Hmb, -, #Hdd⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `s.Start()`
  wp_apply (etcdstart.wp_Start_built wp_Start s ρ E₀ lg γn id N false
      (ReceiptBoundLe.le (GF := GF) (N + 1)) .none (ReceiptBoundLe.le (GF := GF) (2 ^ 48)))
    $$ [Hmb Htok] as Hup
  · iframe
  (try wp_auto)
  iapply HΦ
  iright
  iframe
  iframe #
  ipureintro; rfl

theorem startMember.wp_proofRestart
    (wp_BuildServer : etcdstart.BuildServer.specRestart (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    startMember.specRestart (GF := GF) (hG := hG) := by
  intro CS N lg bootLog ctxs id γ ρ γn ThB RcB RcN HwbN hvs hrule hboot hblen Hγn1 Hγn2
    Hdirok Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hboot, #Hcci, #Hnet, Hrr, #Hrfs, #Hvoff⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  -- the peer URL slice and the cluster's map, read-only from here on
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer ⟨Hpeer, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hq : (slice.mk peer (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr] $$ []
  · iExactEq Hpeer; rfl
  ihave #Hcm : pm ↦$□ GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅ $$ []
  · iExactEq Hpm; rfl
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅,
      sl ↦*□ (fun _ => [etcdstart.httpURL peerAddr]) k $$ []
  · iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iexact Hq
    iapply BigSepM.bigSepM_empty.2; itrivial
  -- `etcdstart.BuildServer(...)`, on the stopped data directory
  wp_apply (wp_BuildServer N name peerAddr clientAddr name (W64 1) (W64 1)
      (slice.mk peer (W64 1) (W64 1)) pm lg
      (GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅) (fun _ => [etcdstart.httpURL peerAddr])
      urlsOk [id] bootLog ctxs (dir id) id γ ρ γn HwbN hvs hrule hboot hblen Hγn1 Hγn2
      Hdirok (by simp [etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _)
      ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩ (by decide) (by decide) Haf Hbuq Hdbo) $$ [Htok Hrr] as %s %err Hres
  · iframe; iframe #
  icases Hres with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, %ρ', %E₀, %Hρ', Hmb, #Hdd⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `s.Start()`
  wp_apply (etcdstart.wp_Start_builtR wp_Start s ρ' E₀ lg γn id N false
      (ReceiptBoundLe.le (GF := GF) (N + 1)) (ReceiptBoundLe.le (GF := GF) (2 ^ 48)))
    $$ [Hmb Htok] as Hup
  · iframe
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists ρ', E₀
  iframe
  iframe #
  ipureintro; exact Hρ'

end proof

end etcd_restart1
end EtcdGrove
end Perennial
