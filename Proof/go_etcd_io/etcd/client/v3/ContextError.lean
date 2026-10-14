/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ContextError.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.google_golang_org.grpc.status.FromError
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem ContextError.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    ContextError.spec (GF := GF) (hG := hG) := by
  intro ci cd err
  wp_start as ⟨#Hce, %Herr⟩
  iunfold ctxErrClient at Hce
  cases err with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro
    exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  | ok ei =>
    wp_auto
    wp_apply wp_rpctypes_Error as %err1 ⟨%Hne1, -, %Hce1⟩
    · ipureintro; simp
    have Hc1 := Hce1 (Herr (by simp))
    obtain ⟨e1, rfl⟩ : ∃ e1, err1 = GoInterface.ok e1 := by
      cases err1 with
      | nil => exact absurd rfl Hne1
      | ok e => exact ⟨e, rfl⟩
    ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
    · iPkgInit
    obtain ⟨Htarget, Hce'⟩ := Hc1
    obtain ⟨Hleaf, Htyped⟩ := Hce' e1 rfl
    ihave #Htree := errors.isErrorTree_leaf (GF := GF) e1 Hleaf Htyped
    wp_apply errors.wp_As (T' := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError)
        (T := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) (· = GoInterface.ok e1)
        (GoInterface.ok e1) _ _ Htarget $$ [$Herrs $Htree $serverErr] as %b %v' Hse
    · ipureintro; rfl
    have Hc1 : clientErr (GoInterface.ok e1) := ⟨Htarget, Hce'⟩
    have Hfin : ∀ e : GoInterface, e ≠ GoInterface.nil → clientErr e →
        ((GoInterface.ok ei = GoInterface.nil → e = GoInterface.nil) ∧
          (GoInterface.ok ei ≠ GoInterface.nil → e ≠ GoInterface.nil ∧ clientErr e)) :=
      fun e hne hc => ⟨fun h => absurd h (by simp), fun _ => ⟨hne, hc⟩⟩
    cases b
    · wp_auto
      wp_apply wp_FromError (GoInterface.ok e1) as %sv %okv #HCode
      cases okv
      · wp_auto
        iapply HΦ
        ipureintro; exact Hfin _ Hne1 Hc1
      · wp_auto
        wp_apply HCode as %c
        wp_if_destruct
        · wp_apply Hce $$ %Broadcast.Pending as %e2 He2 %Hc2
          cases e2 with
          | nil =>
            wp_auto
            iapply HΦ
            ipureintro; exact Hfin _ Hne1 Hc1
          | ok e2 =>
            simp only [reduceCtorEq, ↓reduceIte]
            wp_auto
            wp_apply Hce $$ %Broadcast.Done [He2] as %e3 %Hne3 %Hc3
            · iexact He2
            iapply HΦ
            ipureintro; exact ⟨False.elim, fun _ => ⟨Hne3, Hc3⟩⟩
        · wp_if_destruct
          · wp_apply Hce $$ %Broadcast.Pending as %e2 He2 %Hc2
            cases e2 with
            | nil =>
              wp_auto
              iapply HΦ
              ipureintro; exact Hfin _ Hne1 Hc1
            | ok e2 =>
              simp only [reduceCtorEq, ↓reduceIte]
              wp_auto
              wp_apply Hce $$ %Broadcast.Done [He2] as %e3 %Hne3 %Hc3
              · iexact He2
              iapply HΦ
              ipureintro; exact ⟨False.elim, fun _ => ⟨Hne3, Hc3⟩⟩
          · iapply HΦ
            ipureintro; exact Hfin _ Hne1 Hc1
    · wp_auto
      iapply HΦ
      ipureintro; exact Hfin _ Hne1 Hc1

end proof

end EtcdGrove
end Perennial
