/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3election/electionServer__Campaign.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__Campaign
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__session
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewElection
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Campaign
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Header
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Key
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease

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

theorem electionServer.Campaign.wp_proof
    (hSess : electionServer.session.spec (GF := GF) (hG := hG))
    (hNE : concurrency.NewElection.spec (GF := GF) (hG := hG))
    (hEC : concurrency.Election.Campaign.spec (GF := GF) (hG := hG))
    (hEH : concurrency.Election.Header.spec (GF := GF) (hG := hG))
    (hEK : concurrency.Election.Key.spec (GF := GF) (hG := hG))
    (hER : concurrency.Election.Rev.spec (GF := GF) (hG := hG))
    (hSL : concurrency.Session.Lease.spec (GF := GF) (hG := hG)) :
    electionServer.Campaign.spec (GF := GF) (hG := hG) := by
  intro es c req nsl vsl name val lease ctx cs maxReq
  wp_start as ⟨#Hes, #Hok, %Hcfg, #Hnf, #Hns, #Hlf, #Hvf, #Hvs, %Hrecv, #Hctx, #Hcc⟩
  ihave #Hok' : iprop(v3lock.lockClientOk c) $$ []
  · iexact Hok
  iunfold v3lock.lockClientOk at Hok'
  icases Hok' with ⟨%cctx, -, #Hmc⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  wp_auto
  wp_apply hSess es c lease ctx cs $$ [$Hes $Hok $Hctx $Hcc] as %s %err Hs
  icases Hs with (⟨%Hs, %γ, %id, #Hss, %Hid⟩ | %Hs)
  rotate_left
  · obtain ⟨rfl, Herr⟩ := Hs
    cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Herr⟩
  obtain ⟨rfl, Hsn⟩ := Hs
  (try wp_auto)
  wp_apply wp_bytes_to_string nsl name DFrac.discard $$ [$Hns] as -
  (try wp_auto)
  ihave #Hmc' := Hmc $$ %(name ++ go!"/")
  wp_apply hNE s γ c id name $$ [$Hcpkg $Hss $Hmc'] as %e ⟨#He, Hest⟩
  · ipureintro; exact v3rpc.grpcRecvBytesOk.lt Hcfg Hrecv.1
  (try wp_auto)
  wp_apply wp_bytes_to_string vsl val DFrac.discard $$ [$Hvs] as -
  (try wp_auto)
  ihave #Hlo := etcdReached_zero (GF := GF)
  wp_apply hEC e s γ c id (name ++ go!"/") ElectionSt.init ctx cs val (W64 0) $$
      [$Hcpkg $He $Hest $Hctx $Hcc $Hlo] as %err Hc
  · ipureintro; exact Nat.le_of_lt (Nat.lt_trans (v3rpc.grpcRecvBytesOk.lt Hcfg Hrecv.2) (by decide))
  icases Hc with (⟨%Herr, %key, %rev, %r, %rv, %R, %hdr, Hest, #Hhr, #HR, #Hkv, Hout, %Hp⟩ |
    ⟨%Hne, %st', Hest⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Hne⟩
  subst Herr
  (try wp_auto)
  wp_apply hEH e s ⟨key, rev, s, hdr⟩ $$ [$Hcpkg $Hest] as Hest
  (try wp_auto)
  wp_apply hEK e s ⟨key, rev, s, hdr⟩ $$ [$Hcpkg $Hest] as Hest
  (try wp_auto)
  wp_apply wp_string_to_bytes key as %ksl ⟨Hksl, -⟩
  (try wp_auto)
  wp_apply hER e s ⟨key, rev, s, hdr⟩ $$ [$Hcpkg $Hest] as Hest
  (try wp_auto)
  wp_apply hSL s γ c id $$ [$Hcpkg $Hss]
  (try wp_auto)
  irename «$r0» => Hr
  generalize «$r0_ptr» = r0 at *
  (try wp_auto)
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists key, rev, r, rv, R, id, hdr, _, ksl, _, _
  iframe Hr Hksl Hhr HR Hkv Hout
  iframe
  ipureintro
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, Hid.1, Hid.2⟩, Hp.1⟩

end proof

end v3election
end EtcdGrove
end Perennial
