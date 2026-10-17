/-
Proof of the spec of the same name (pr-verify etcd#21621). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.connStatsHandler__HandleConn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.RecordClientCertExpiration
public import Spec.google_golang_org.grpc.peer.FromContext
public import Spec.time.Duration__Seconds

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode google_golang_org.grpc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.connStatsHandler.HandleConn.wp_proof
    (wp_FromContext : peer.FromContext.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_Record : v3rpc.RecordClientCertExpiration.spec (GF := GF) (hG := hG)) :
    v3rpc.connStatsHandler.HandleConn.spec (GF := GF) (hG := hG) := by
  intro h hs ctx s o oti P Q
  -- `x509.Certificate` is axiomatized: take its representation from the package assumptions,
  -- not from its generated (`sorry`) points-to instances, for the `NotAfter` field address
  haveI : go.TypeReprUnderlying crypto.x509.Certificate.underlying crypto.x509.Certificate :=
    crypto.x509.Certificate.TypeAssumptions.type_repr
  haveI : go.IsUnderlying crypto.x509.Certificate.underlying crypto.x509.Certificate.underlying :=
    crypto.x509.Certificate.TypeAssumptions.isUnderlying
  haveI : TypeRepr crypto.x509.Certificate.underlying crypto.x509.Certificate := go.type_repr_underlying
  wp_start as ⟨%Hev, #Hh, #Hctx, #Hown, #Htls, #Hhist, HP⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  -- not a `*stats.ConnBegin`: it returns, observing nothing
  by_cases hb : ∃ l : Loc, s = GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #l⟩
  case neg =>
    have hnr : ¬ v3rpc.connRecords s hs o oti := fun hr => hb hr.1
    rcases s with ⟨ity, iv⟩ | _
    · by_cases hty : ity = go.GoType.PointerType stats.ConnBegin.ty
      · subst hty
        obtain ⟨l, rfl⟩ := Hev _ rfl rfl
        exact absurd ⟨l, rfl⟩ hb
      · wp_auto
        simp only [hty, ite_false, _root_.decide_false]
        wp_auto
        iapply HΦ
        iright; iframe; ipureintro; exact hnr
    · wp_auto
      iapply HΦ
      iright; iframe; ipureintro; exact hnr
  obtain ⟨lb, rfl⟩ := hb
  wp_auto
  wp_apply wp_FromContext ctx o $$ [] as -
  · iexact Hctx
  rcases o with _ | ⟨pp, pr⟩
  · -- no peer in the context
    have hnr : ¬ v3rpc.connRecords (GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #lb⟩) hs none oti := by
      rintro ⟨-, p, pr, h, -⟩; cases h
    simp only [peer.ctxLoc, Option.isSome]
    wp_auto
    iapply HΦ
    iright; iframe; ipureintro; exact hnr
  iunfold peer.ctxOwn at Hown
  simp only [peer.ctxLoc, Option.isSome]
  iStructNamed Hown
  iunfold v3rpc.connTLSOk at Htls
  wp_auto
  cases hai : pr.AuthInfo' with
  | nil =>
    -- no `AuthInfo`
    have hnr : ¬ v3rpc.connRecords (GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #lb⟩) hs
        (some (pp, pr)) oti := by
      rintro ⟨-, p, pr', ho, ⟨v, ha⟩, -⟩; cases ho; rw [hai] at ha; cases ha
    wp_auto
    iapply HΦ
    iright; iframe; ipureintro; exact hnr
  | ok ai =>
    rcases ai with ⟨aty, av⟩
    wp_auto
    by_cases hty : aty = credentials.TLSInfo.ty
    case neg =>
      -- not TLS
      have hnr : ¬ v3rpc.connRecords (GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #lb⟩) hs
          (some (pp, pr)) oti := by
        rintro ⟨-, p, pr', ho, ⟨v, ha⟩, -⟩; cases ho; rw [hai] at ha; cases ha; exact hty rfl
      simp only [if_neg hty, decide_eq_false hty]
      wp_auto
      iapply HΦ
      iright; iframe; ipureintro; exact hnr
    subst hty
    ihave ⟨%ti, ⟨%hoti, %hti⟩, #Hcerts⟩ := Htls $$ %(GoInterfaceOk.mk credentials.TLSInfo.ty av) %hai %rfl
    simp only at hti
    subst hti hoti
    simp only [ite_true, _root_.decide_true]
    iStructNamed Hh
    wp_auto
    by_cases hca : hs.clientAuth' = W64 0
    · -- the server does not ask for client certificates
      have hnr : ¬ v3rpc.connRecords (GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #lb⟩) hs
          (some (pp, pr)) (some ti) := by
        rintro ⟨-, p, pr', ho, -, hc, -⟩; exact hc hca
      simp only [hca, _root_.decide_true, Bool.not_true]
      wp_auto
      iapply HΦ
      iright; iframe; ipureintro; exact hnr
    simp only [hca, _root_.decide_false, Bool.not_false]
    wp_auto
    iunfold v3rpc.tlsCertsOk at Hcerts
    icases Hcerts with ⟨%certs, #Hsl, #Hleaf⟩
    ihave %Hlen := ownSlice_len $$ Hsl
    wp_if_destruct
    · cases certs with
      | nil => exfalso; simp at Hlen; word
      | cons c rest =>
        iunfold v3rpc.leafOk at Hleaf
        icases Hleaf with ⟨%na, #Hna⟩
        rw [if_pos (by word)]
        wp_apply wp_load_slice_index _ (sint.Z (W64 0)) (c :: rest) DFrac.discard c (by word) $$ [Hsl]
          as -
        · isplitr
          · iexact Hsl
          · ipureintro; simp
        wp_apply time.wp_Until na as %d -
        haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
        wp_apply wp_Seconds d as %fs -
        wp_apply wp_Record fs P Q $$ [HP] as HQ
        · isplitr
          · iexact Hhist
          · iexact HP
        iapply HΦ
        ileft
        isplitr
        · ipureintro
          exact ⟨⟨lb, rfl⟩, pp, pr, rfl, ⟨_, hai⟩, hca, ti, rfl, by word⟩
        · iexists fs; iexact HQ
    · -- no certificate sent
      have hnr : ¬ v3rpc.connRecords (GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #lb⟩) hs
          (some (pp, pr)) (some ti) := by
        rintro ⟨-, p, pr', ho, -, -, ti', hti', hl⟩
        cases hti'; word
      iapply HΦ
      iright; iframe; ipureintro; exact hnr

end proof

end EtcdGrove
end Perennial
