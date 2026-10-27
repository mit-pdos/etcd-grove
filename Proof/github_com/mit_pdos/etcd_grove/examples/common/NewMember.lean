/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/NewMember.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

The steps (putget3's `startMember` up to `Start`): `newServer`; `net.Listen` at the peer address;
`s.RaftHandler()` (from `memberBuilt`'s `srvNetMember`); `go http.Serve(l, h)` (`http.Serve_ok`; the peer address
one of the member's URLs in the directory). Every step's error returns it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Proof.net.http.Axioms

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem NewMember.wp_proof
    (wp_newServer : newServer.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG)) :
    NewMember.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs
    γn Htb Hrb48 HrbN hvs hdyn hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hck Haf Hbuq
    Hdbo
  wp_start as ⟨Haddr, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hpown⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- `newServer(name, peer, client, cluster, token, 0, lg)`: the compactor off
  wp_apply (wp_newServer N name peerAddr client token (W64 0) peer cluster lg M iu Uok ps bootLog
      ctxs dir id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs hdyn hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg
      (by decide) Hck Haf Hbuq Hdbo) $$ [Hmb] as %s %err Hres
  · iframe; iframe #
  icases Hres with (%Herr | ⟨%Herr, Hmb⟩)
  · -- `newServer` failed: the error returned
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; simp
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
    iapply HΦ; ileft; ipureintro; simp
  subst Hlerr
  wp_auto
  iunfold memberBuilt at Hmb
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, HServeR, HWR⟩
  -- (2026-10-24, rafthttp stage 6d) the listener serves the peer address with the raft protocol
  -- (the program start's reservation)
  imod (http.register lis peerAddr (raftProto (netRh γn))) $$ Hlis Hpown with Hlis
  -- `go http.Serve(l, s.RaftHandler())`: the member owns its peer address (the directory's)
  have Hown : (netRh γn).owner peerAddr = id := by
    rw [netRh_owner]
    exact netOwner_of_mem γn.dir (by rw [Hγn2]; exact Hdirok.2.1) id peerAddr (by rw [Hγn2]; exact Hdir)
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
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iunfold memberBuilt
  iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
  simp only [↓reduceIte]
  iframe
  iframe #
  ipureintro; exact HE

end proof

end common
end EtcdGrove
end Perennial
