/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3election/electionServer__Leader.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer__session
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewElection
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Leader

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

theorem electionServer.Leader.wp_proof
    (hSess : electionServer.session.spec (GF := GF) (hG := hG))
    (hNE : concurrency.NewElection.spec (GF := GF) (hG := hG))
    (hEL : concurrency.Election.Leader.spec (GF := GF) (hG := hG)) :
    electionServer.Leader.spec (GF := GF) (hG := hG) := by
  intro es c req nsl name ctx cs
  wp_start as ⟨#Hes, #Hok, #Hnf, #Hns, #Hctx, #Hcc⟩
  ihave #Hok' : iprop(v3lock.lockClientOk c) $$ []
  · iexact Hok
  iunfold v3lock.lockClientOk at Hok'
  icases Hok' with ⟨%cctx, -, #Hmc⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  wp_auto
  wp_apply hSess es c _ ctx cs $$ [$Hes $Hok $Hctx $Hcc] as %s %err Hs
  icases Hs with (⟨%Hs, %γ, %id, #Hss, -⟩ | %Hs)
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
  wp_apply hNE s γ c id name $$ [$Hcpkg $Hss $Hmc'] as %e ⟨#He, -⟩
  (try wp_auto)
  ihave #Hlo := etcdReached_zero (GF := GF)
  wp_apply hEL e s γ c id (name ++ go!"/") ctx cs (W64 0) $$ [$Hcpkg $He $Hctx $Hlo] as %l %lerr Hl
  icases Hl with (⟨%Hle, %R, %kp, %kv, #Hrr, #HR, #Hone, #Hlk, -⟩ | ⟨%Hln, #Hpe, -⟩ | %Hle)
  · subst Hle
    iunfold getRespRev at Hrr
    icases Hrr with ⟨%hdr, #Hhf, %Hhn, #Hhr⟩
    iunfold getRespOneKv at Hone
    icases Hone with ⟨%sl, #Hslf, #Hsl, #Hkv⟩
    (try wp_auto)
    ihave %Hlen := ownSlice_len $$ Hsl
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by
      simp at Hlen; word)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) kp sl DFrac.discard [kp] (by word) (by simp)
      $$ Hsl with ⟨#Hpe, -⟩
    (try wp_auto)
    wp_alloc r0 as Hr
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists hdr, kp, R, kv, _
    iframe Hr Hkv Hlk HR
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iunfold hdrRevAt
    iframe Hhr
    ipureintro; exact Hhn
  · iunfold isPkgErr at Hpe
    icases Hpe with ⟨-, %Hne'⟩
    cases lerr with
    | nil => exact absurd rfl Hne'
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Hne'⟩
  · obtain ⟨-, Hne'⟩ := Hle
    cases lerr with
    | nil => exact absurd rfl Hne'
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Hne'⟩

end proof

end v3election
end EtcdGrove
end Perennial
