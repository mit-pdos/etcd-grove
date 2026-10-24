/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3election/electionServer__session.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__session
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSession
public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithLease
public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithContext
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Orphan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3election

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions]

theorem electionServer.session.wp_proof
    (hNS : concurrency.NewSession.spec (GF := GF) (hG := hG))
    (hWL : concurrency.WithLease.spec (GF := GF) (hG := hG))
    (hWC : concurrency.WithContext.spec (GF := GF) (hG := hG))
    (hOr : concurrency.Session.Orphan.spec (GF := GF) (hG := hG)) :
    electionServer.session.spec (GF := GF) (hG := hG) := by
  intro es c lease ctx cs
  wp_start as ⟨#Hes, #Hok, #Hctx, #Hcc⟩
  iunfold isElectionServer at Hes
  ihave #Hok' : iprop(v3lock.lockClientOk c) $$ []
  · iexact Hok
  iunfold v3lock.lockClientOk at Hok'
  icases Hok' with ⟨%cctx, #Hsc, -⟩
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
  iapply HΦ
  ileft
  isplitr
  · ipureintro; exact ⟨rfl, Hsn⟩
  iexists γ, id
  iframe Hss
  ipureintro
  simpa [sessionLeaseOk, sessOptsFold, withLeaseSM, withContextM, SessionOpts.init] using Hid

end proof

end v3election
end EtcdGrove
end Perennial
