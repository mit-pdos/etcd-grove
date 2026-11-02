/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/startMember.lean`'s `spec` (the
restart plan's R2a, 2026-11-02): `common.BuildServer` (its drafted `specStop`), `net.Listen` at the
peer address, the listener registered closable (the draft boundary `http.registerClosable_spec`),
`go http.Serve(pl, s.RaftHandler())`, `s.Start()` (`common.wp_Start_built`), and the `member`
record allocated. As `common.NewMember`'s and
`common.StartMember`'s proofs. Lean-first (no Rocq counterpart). `wp_proofRestart`: the same over
`BuildServer.specRestart` and the restart's start (`common.Start_builtR_spec`, R2d).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.BuildServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Proof.net.http.Axioms
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.StartStop
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

theorem startMember.wp_proof
    (wp_BuildServer : common.BuildServer.specStop (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (hReg : http.registerClosable_spec (GF := GF))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    startMember.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn
    ThB RcB RcN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hck Haf Hbuq Hdbo
  wp_start as ⟨Haddr, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hpown⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.common $$ []
  · iPkgInit
  (try wp_auto)
  -- `common.BuildServer(name, peer, client, cluster, "restart3", SnapCount, SnapCatchUp, lg)`
  wp_apply (wp_BuildServer N name peerAddr client token (W64 1) (W64 1) peer cluster lg M iu Uok
      ps bootLog ctxs dir id γ ρ E₀ Φs γn hvs hrule hboot hblen Hγn1 Hγn2 Hdirok
      Hdir HU Hlg Hck Haf Hbuq Hdbo) $$ [Hmb] as %s %err Hres
  · iframe; iframe #
  icases Hres with (%Herr | ⟨%Herr, Hmb, Hsr⟩)
  · -- `BuildServer` failed: the error returned, with the thread token
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
  iunfold common.memberBuilt at Hmb
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, HServeR, HWR⟩
  -- the listener registered, closable (the draft boundary): it serves the peer address with the
  -- member's raft protocol
  imod (hReg lis peerAddr (raftProto (netRh γn))) $$ Hlis Hpown with ⟨%Hli, Hlis, Hcloser⟩
  -- `go http.Serve(pl, s.RaftHandler())`: the member owns its peer address (the directory's)
  have Hown : (netRh γn).owner peerAddr = id := by
    rw [netRh_owner]
    exact netOwner_of_mem γn.dir (by rw [Hγn2]; exact Hdirok.2.1) id peerAddr
      (by rw [Hγn2]; exact Hdir)
  wp_apply (wp_RaftHandler s γn id τ peerAddr Hown) as %h Hh
  · iframe #
  (try wp_auto)
  wp_apply wp_fork $$ [Hlis Hh HServeR]
  · wp_apply (http.Serve_ok (raftHttpNet (netRh γn)) lis h peerAddr (srvServeRes γn τ))
      $$ [Hlis Hh HServeR] as %serr -
    · iframe Hh HServeR
      rw [show (raftHttpNet (netRh γn)).proto peerAddr = raftProto (netRh γn) from rfl]
      iexact Hlis
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  -- `s.Start()`
  wp_apply (common.wp_Start_built wp_Start s ρ E₀ lg γn id N true
      (ReceiptBoundLe.le (GF := GF) (N + 1)))
    $$ [Hsb Hserve Hsv Hlgm Hrc Htokp HWR Htok] as Hup
  · iframe Htok
    iframe #
    iunfold common.memberBuilt
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
    simp only [↓reduceIte]
    iframe
    iframe #
    ipureintro; exact HE
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists s, lis
  iframe
  iunfold memberStop
  iframe
  ipureintro; exact Hli

theorem startMember.wp_proofRestart
    (wp_BuildServer : common.BuildServer.specRestart (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (hReg : http.registerClosable_spec (GF := GF))
    (wp_StartR : common.Start_builtR_spec (GF := GF) (hG := hG)) :
    startMember.specRestart (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ γn
    ThB RcB RcN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hck Haf Hbuq Hdbo
  wp_start as ⟨Haddr, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Himg, #Hnet, Hpown⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.common $$ []
  · iPkgInit
  (try wp_auto)
  -- `common.BuildServer(name, peer, client, cluster, "restart3", SnapCount, SnapCatchUp, lg)`
  wp_apply (wp_BuildServer N name peerAddr client token (W64 1) (W64 1) peer cluster lg M iu Uok
      ps bootLog ctxs dir id γ ρ γn hvs hrule hboot hblen Hγn1 Hγn2 Hdirok
      Hdir HU Hlg Hck Haf Hbuq Hdbo) $$ [Himg] as %s %err Hres
  · iframe; iframe #
  icases Hres with (%Herr | ⟨%Herr, %ρ', %E₀, %Hρ', Hmb, Hsr⟩)
  · -- `BuildServer` failed: the error returned, with the thread token
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
  iunfold common.memberBuiltR at Hmb
  icases Hmb with ⟨%ai₀, %at₀, %c₀, %x₀, Hmb⟩
  iunfold common.memberBuilt at Hmb
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, HServeR, HWR⟩
  -- the listener registered, closable (the draft boundary): it serves the peer address with the
  -- member's raft protocol
  imod (hReg lis peerAddr (raftProto (netRh γn))) $$ Hlis Hpown with ⟨%Hli, Hlis, Hcloser⟩
  -- `go http.Serve(pl, s.RaftHandler())`: the member owns its peer address (the directory's)
  have Hown : (netRh γn).owner peerAddr = id := by
    rw [netRh_owner]
    exact netOwner_of_mem γn.dir (by rw [Hγn2]; exact Hdirok.2.1) id peerAddr
      (by rw [Hγn2]; exact Hdir)
  wp_apply (wp_RaftHandler s γn id τ peerAddr Hown) as %h Hh
  · iframe #
  (try wp_auto)
  wp_apply wp_fork $$ [Hlis Hh HServeR]
  · wp_apply (http.Serve_ok (raftHttpNet (netRh γn)) lis h peerAddr (srvServeRes γn τ))
      $$ [Hlis Hh HServeR] as %serr -
    · iframe Hh HServeR
      rw [show (raftHttpNet (netRh γn)).proto peerAddr = raftProto (netRh γn) from rfl]
      iexact Hlis
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  -- `s.Start()`
  wp_apply (wp_StartR s ρ' E₀ lg γn id N true)
    $$ [Hsb Hserve Hsv Hlgm Hrc Htokp HWR Htok] as Hup
  · iframe Htok
    iframe #
    iunfold common.memberBuiltR
    iexists ai₀, at₀, c₀, x₀
    iunfold common.memberBuilt
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
    simp only [↓reduceIte]
    iframe
    iframe #
    ipureintro; exact HE
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists s, lis, ρ', E₀
  iframe
  isplitr; · ipureintro; exact Hρ'
  iunfold memberStop
  iframe
  ipureintro; exact Hli

end proof

end restart3
end EtcdGrove
end Perennial
