/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/StartServer.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

The steps: the peer URL slice and the cluster's map `{name ↦ peer}` (read-only from here on,
D19r (F)); `newServer` (its URLs `urls1`); on success `s.Start()` (`wp_Start_built`). An error of
`newServer` returns it, with the thread token, which `Start` would take.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem StartServer.wp_proof
    (wp_newServer : newServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    StartServer.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client lg bootLog dir id γ bud ρ E₀ Φs γn W HW Htb Hrb48 HrbN hcfg hdyn
    hcc hboot htr htx hblen Hγn1 Hγn2 Hdirok Hlg Hck Haf Hbuq Hdbo
  wp_start as ⟨Htok, #Hboot, #Hcom, #Hcci, Hmb, #Hnet⟩
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
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hq : (slice.mk peer (W64 1) (W64 1)) ↦*□ [httpURL peerAddr] $$ []
  · iExactEq Hpeer; rfl
  ihave #Hcm : pm ↦$□ GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅ $$ []
  · iExactEq Hpm; rfl
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅,
      sl ↦*□ (fun _ => [httpURL peerAddr]) k $$ []
  · iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iexact Hq
    iapply BigSepM.bigSepM_empty.2; itrivial
  -- `newServer(name, peer, clientAddr, {name: peer}, name, lg)`
  wp_apply (wp_newServer N name peerAddr client name (slice.mk peer (W64 1) (W64 1)) pm lg
      (GMap.insert name (slice.mk peer (W64 1) (W64 1)) ∅) (fun _ => [httpURL peerAddr])
      (urls1 name peerAddr client) [id] bootLog dir id γ bud ρ E₀ Φs γn W HW Htb Hrb48 HrbN
      hcfg hdyn hcc hboot htr htx hblen Hγn1 Hγn2 Hdirok ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩ Hlg Hck Haf Hbuq
      Hdbo) $$ [Hmb] as %s %err Hres
  · iframe; iframe #
  icases Hres with (%Herr | ⟨%Herr, Hmb⟩)
  · -- `newServer` failed: the error returned, with the thread token
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `s.Start()`
  wp_apply (wp_Start_built wp_Start s ρ E₀ lg γn id N bud _ HrbN) $$ [Hmb Htok] as Hup
  · iframe
  (try wp_auto)
  iapply HΦ
  iright
  iframe
  ipureintro; rfl

end proof

end common
end EtcdGrove
end Perennial
