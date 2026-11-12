/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__dialWithBalancer.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__dialWithBalancer
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.client.v3.Client__credentialsForEndpoint
public import Spec.go_etcd_io.etcd.client.v3.Client__dial
public import Spec.google_golang_org.grpc.WithResolvers
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The proof unfolds the method by its trusted body (`DialWithBalancerBody.lean`). -/
theorem Client.dialWithBalancer.wp_proof
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (wp_Endpoints : Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_credentialsForEndpoint : Client.credentialsForEndpoint.spec (GF := GF) (hG := hG))
    (wp_WithResolvers : grpc.WithResolvers.spec (GF := GF) (hG := hG))
    (wp_dial : Client.dial.spec (GF := GF) (hG := hG)) :
    Client.dialWithBalancer.spec (GF := GF) (hG := hG) := by
  intro c cfg cr r esl eps atb P
  wp_start as ⟨#Hc, #Hcfg, #Hdo, #Hatb, #Htb, #Hcr, #Heps, #Hesl, %Hplain, #Hr, Hro⟩
  obtain ⟨ep, rest, rfl⟩ : ∃ ep rest, eps = ep :: rest := by
    cases eps with
    | nil => exact absurd rfl Hplain.1
    | cons a l => exact ⟨a, l, rfl⟩
  have Hp1 : plainEndpoint ep := Hplain.2 ep List.mem_cons_self
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Endpoints c $$ [$Hc] as %esl' ⟨%eps, Hesl', Heq⟩
  ihave %Heq' := Heq $$ Heps Hesl
  subst Heq'
  ihave %Hlen := ownSlice_len _ _ _ $$ Hesl'
  rw [ite_eq_left (by simp at Hlen; word)]
  wp_apply wp_load_slice_index esl' (sint.Z (W64 0)) (ep :: rest) (DFrac.own 1) ep (by decide) $$ [$Hesl']
    as -
  · ipureintro; rfl
  wp_apply wp_credentialsForEndpoint c ep cr $$ [$Hcr]
  · ipureintro; exact Hp1
  wp_apply wp_slice_literal (V := GoInterface) [resolverIface r]
  isplitr
  · ipureintro; rfl
  iintro %bl ⟨Hbl, -⟩
  ipersist Hbl
  (try wp_auto)
  wp_apply wp_WithResolvers _ [resolverIface r] $$ [$Hgrpc $Hbl] as %o %Ho
  wp_apply wp_slice_literal (V := GoInterface) [o]
  isplitr
  · ipureintro; rfl
  iintro %ol ⟨Hol, -⟩
  (try wp_auto)
  ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := GoInterface) (GF := GF)
  wp_apply wp_slice_append (V := GoInterface) slice.nil [] _ [o] (DFrac.own 1) $$ [$Hnil $Hnilc $Hol]
    as %o2 ⟨Ho2, -, -⟩
  ipersist Ho2
  (try wp_auto)
  ihave Hrb := etcdResolver_grpc (GF := GF) r (ep :: rest) Hplain $$ Hro
  wp_apply wp_dial c cfg cr o2 (resolverIface r) esl (ep :: rest) atb P
    $$ [$Hc $Hcfg $Hdo $Hatb $Htb $Heps $Hesl $Hrb]
    as %conn %err Hres
  · isplitr
    · ipureintro; exact Hplain
    iunfold dialOptsAt
    iexists [o]
    rw [List.nil_append]
    iframe Ho2
    ipureintro
    exact .cons Ho .nil
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
