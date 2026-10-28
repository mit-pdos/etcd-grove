/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3lock/lockServer__Lock.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer__Lock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSession
public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithLease
public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithContext
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Orphan
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewMutex
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Lock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Header
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Key

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3lock

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

theorem lockServer.Lock.wp_proof
    (hNS : concurrency.NewSession.spec (GF := GF) (hG := hG))
    (hWL : concurrency.WithLease.spec (GF := GF) (hG := hG))
    (hWC : concurrency.WithContext.spec (GF := GF) (hG := hG))
    (hOr : concurrency.Session.Orphan.spec (GF := GF) (hG := hG))
    (hNM : concurrency.NewMutex.spec (GF := GF) (hG := hG))
    (hML : concurrency.Mutex.Lock.spec (GF := GF) (hG := hG))
    (hMH : concurrency.Mutex.Header.spec (GF := GF) (hG := hG))
    (hMK : concurrency.Mutex.Key.spec (GF := GF) (hG := hG)) :
    lockServer.Lock.spec (GF := GF) (hG := hG) := by
  intro ls c req nsl name lease ctx cs
  wp_start as ⟨#Hls, #Hok, #Hnf, #Hns, #Hlf, #Hctx, #Hcc⟩
  iunfold isLockServer at Hls
  iunfold lockClientOk at Hok
  icases Hok with ⟨%cctx, #Hsc, #Hmc⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  wp_auto
  wp_apply hWL $$ [$Hcpkg] as %f1 #Hf1
  (try wp_auto)
  wp_apply hWC $$ [$Hcpkg] as %f2 #Hf2
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoFunc) [f1, f2]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, -⟩
  ipersist Hsl
  ihave #Hopts : iprop(sessOptsAt (slice.mk slp (W64 2) (W64 2))
      [withLeaseSM lease, withContextM (GoInterface.ok ctx)]) $$ []
  · iunfold sessOptsAt
    iexists [f1, f2]
    isplit
    · iExactEq Hsl; rfl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hfi %Hgi
    rcases i with _ | _ | i
    · simp at Hfi Hgi; subst Hfi; subst Hgi; iexact Hf1
    · simp at Hfi Hgi; subst Hfi; subst Hgi; iexact Hf2
    · simp at Hfi
  (try wp_auto)
  wp_apply hNS c cctx _ [withLeaseSM lease, withContextM (GoInterface.ok ctx)] ctx cs $$
      [$Hcpkg $Hsc $Hctx $Hcc] as %s %err Hs
  · isplitr
    · iExactEq Hopts; rfl
    ipureintro; rfl
  icases Hs with (%Hs | ⟨%Hs, %γ, %id, #Hss, %Hid⟩)
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
  wp_apply hOr s γ c id $$ [$Hcpkg $Hss] as -
  (try wp_auto)
  wp_apply wp_bytes_to_string nsl name DFrac.discard $$ [$Hns] as -
  (try wp_auto)
  ihave #Hmc' := Hmc $$ %(name ++ go!"/")
  wp_apply hNM s γ c id name $$ [$Hcpkg $Hss $Hmc'] as %m ⟨#Hm, Hmst⟩
  (try wp_auto)
  ihave #Hlo := etcdReached_zero (GF := GF)
  wp_apply hML m s γ c id (name ++ go!"/") MutexSt.init ctx cs (W64 0) $$
      [$Hcpkg $Hm $Hmst $Hctx $Hcc $Hlo] as %err Hl
  icases Hl with (⟨%Herr, %key, %rev, %R, %hdr, Hmst, #Hhr, #HR, Hlk, %Hpk⟩ |
    ⟨#Hpe, %st', %R, Hmst, -, -, -⟩ | ⟨%Hne, %st', Hmst⟩)
  · subst Herr
    (try wp_auto)
    wp_apply hMH m ⟨key, rev, hdr⟩ $$ [$Hcpkg $Hmst] as Hmst
    (try wp_auto)
    wp_apply hMK m ⟨key, rev, hdr⟩ $$ [$Hcpkg $Hmst] as Hmst
    (try wp_auto)
    wp_apply wp_string_to_bytes key as %ksl ⟨Hksl, -⟩
    (try wp_auto)
    irename «$r0» => Hr
    generalize «$r0_ptr» = r at *
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, rev, R, hdr, ksl, _
    iframe Hr Hksl Hhr HR Hlk
    ipureintro
    exact ⟨⟨rfl, rfl⟩, Hpk.1⟩
  · iunfold isPkgErr at Hpe
    icases Hpe with ⟨-, %Hne⟩
    cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Hne⟩
  · cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Hne⟩

end proof

end v3lock
end EtcdGrove
end Perennial
