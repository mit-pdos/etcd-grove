/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/NewMember.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

The steps (putget3's `startMember` up to `Start`): `newServer`; `net.Listen` at the peer address;
`s.RaftHandler()` (from `memberBuilt`'s `srvNetMember`); `go http.Serve(l, h)` (the peer address
one of the member's URLs in the directory). Every step's error returns it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Spec.net.http.Serve

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

theorem NewMember.wp_proof
    (wp_newServer : newServer.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_Serve : net.http.Serve.spec (GF := GF) (hG := hG)) :
    NewMember.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token peer cluster lg M iu Uok ps bootLog dir id γ bud ρ E₀ Φs
    γn W HW Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen Hγn1 Hγn2 Hdir HU Hlg Hck Haf Hbuq
    Hdbo
  wp_start as ⟨Haddr, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, Hslot⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- `newServer(name, peer, client, cluster, token, lg)`
  wp_apply (wp_newServer N name peerAddr client token peer cluster lg M iu Uok ps bootLog dir id
      γ bud ρ E₀ Φs γn W HW Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen Hγn1 Hγn2 HU Hlg Hck
      Haf Hbuq Hdbo) $$ [Hmb Hslot] as %s %err Hres
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
  -- `go http.Serve(l, s.RaftHandler())`
  iunfold memberBuilt at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %HE, #Hwb, Hsb, Hserve, Hsv, #Hoff, Hlgm,
    #Hnm, HWR⟩
  wp_apply (wp_RaftHandler s γn id) as %h #Hh
  · iframe #
  (try wp_auto)
  wp_apply wp_fork $$ [Hlis]
  · wp_apply (wp_Serve lis h peerAddr γn id) $$ [Hlis] as %serr -
    · iframe Hlis Hh; ipureintro; rw [Hγn2]; exact Hdir
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iunfold memberBuilt
  iexists γA, ci, TM, E, γrn, b, cfg
  iframe
  iframe #
  ipureintro; exact HE

end proof

end common
end EtcdGrove
end Perennial
