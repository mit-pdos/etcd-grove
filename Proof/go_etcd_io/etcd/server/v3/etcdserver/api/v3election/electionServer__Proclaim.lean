/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3election/electionServer__Proclaim.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__Proclaim
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__session
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Proclaim
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Header
public import Spec.go_etcd_io.etcd.client.v3.concurrency.ResumeElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3election

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions]

theorem electionServer.Proclaim.wp_proof
    (hSess : electionServer.session.spec (GF := GF) (hG := hG))
    (hRE : concurrency.ResumeElection.spec (GF := GF) (hG := hG))
    (hEP : concurrency.Election.Proclaim.spec (GF := GF) (hG := hG))
    (hEH : concurrency.Election.Header.spec (GF := GF) (hG := hG)) :
    electionServer.Proclaim.spec (GF := GF) (hG := hG) := by
  intro es c req lk vsl name key val rev lease ctx cs maxReq
  wp_start as ⟨#Hes, #Hok, %Hcfg, #Hlf, Hlk, #Hvf, #Hvs, %Hrecvv, #Hctx, #Hcc⟩
  ihave #Hok' : iprop(v3lock.lockClientOk c) $$ []
  · iexact Hok
  iunfold v3lock.lockClientOk at Hok'
  icases Hok' with ⟨%cctx, -, #Hmc⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  by_cases hlk : lk = null
  · subst hlk
    ihave #Hfact : (v3electionInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    iunfold v3electionInit at Hfact
    icases Hfact with ⟨%e0, #He0⟩
    wp_auto
    iapply HΦ
    ileft
    iframe He0
    ipureintro
    exact ⟨⟨rfl, rfl⟩, by simp⟩
  icases Hlk with (%Hnull | ⟨#Hlk, %Hne, %Hrecv⟩)
  · exact absurd Hnull hlk
  iunfold leaderKeyAt at Hlk
  icases Hlk with ⟨%nsl, %ksl, #Hnf, #Hns, #Hkf, #Hks, #Hrf, #Hlsf⟩
  wp_auto
  simp only [hlk, decide_false]
  (try wp_auto)
  wp_apply hSess es c lease ctx cs $$ [$Hes $Hok $Hctx $Hcc] as %s %err Hs
  icases Hs with (⟨%Hs, %γ, %id, #Hss, %Hid⟩ | %Hs)
  rotate_left
  · obtain ⟨rfl, Herr⟩ := Hs
    cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright; iright
      ipureintro
      exact ⟨rfl, Herr⟩
  obtain ⟨rfl, Hsn⟩ := Hs
  (try wp_auto)
  wp_apply wp_bytes_to_string nsl name DFrac.discard $$ [$Hns] as -
  (try wp_auto)
  wp_apply wp_bytes_to_string ksl key DFrac.discard $$ [$Hks] as -
  (try wp_auto)
  ihave #Hmc' := Hmc $$ %name
  wp_apply hRE s γ c id name key rev $$ [$Hcpkg $Hss $Hmc'] as %e ⟨#He, Hest⟩
  · ipureintro
    exact ⟨⟨Hne, Nat.le_of_lt (v3rpc.grpcRecvBytesOk.lt Hcfg Hrecv.1)⟩,
      Nat.le_of_lt (Nat.lt_trans (v3rpc.grpcRecvBytesOk.lt Hcfg Hrecv.2) (by decide))⟩
  (try wp_auto)
  wp_apply wp_bytes_to_string vsl val DFrac.discard $$ [$Hvs] as -
  (try wp_auto)
  ihave #Hlo := etcdReached_zero (GF := GF)
  wp_apply hEP e s γ c id name { key := key, rev := rev, sess := s, hdr := null } ctx cs val (W64 0) $$
      [$Hcpkg $He $Hest $Hctx $Hlo] as %err Hp
  · ipureintro; exact Nat.le_of_lt (Nat.lt_trans (v3rpc.grpcRecvBytesOk.lt Hcfg Hrecvv) (by decide))
  icases Hp with (⟨%Hok2, %hdr, Hest, Hfacts⟩ | ⟨#Hpe, -⟩ | ⟨%Hne', -⟩)
  · obtain ⟨rfl, -⟩ := Hok2
    (try wp_auto)
    wp_apply hEH e s { key := key, rev := rev, sess := s, hdr := hdr } $$ [$Hcpkg $Hest] as Hest
    (try wp_auto)
    irename «$r0» => Hr
    generalize «$r0_ptr» = r0 at *
    (try wp_auto)
    iapply HΦ
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists hdr, _
    iframe Hr
    isplitr
    · ipureintro; rfl
    icases Hfacts with (%Hnp | ⟨%r, #Hhr, #Hr', #Hpa, -⟩)
    · ileft; ipureintro; exact Hnp
    · iright
      iexists r, id
      iframe Hhr Hr' Hpa
      ipureintro; exact Hid
  · iunfold isPkgErr at Hpe
    icases Hpe with ⟨-, %Hne'⟩
    cases err with
    | nil => exact absurd rfl Hne'
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright; iright
      ipureintro
      exact ⟨rfl, Hne'⟩
  · cases err with
    | nil => exact absurd rfl Hne'
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright; iright
      ipureintro
      exact ⟨rfl, Hne'⟩

end proof

end v3election
end EtcdGrove
end Perennial
