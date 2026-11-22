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
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem ContextError.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    ContextError.spec (GF := GF) (hG := hG) := by
  intro ci cd err m
  wp_start as ⟨#Hce, %Herr, #Hse, #Hm⟩
  iunfold ctxErrClient at Hce
  cases err with
  | nil =>
    wp_auto
    iapply HΦ
    isplitl
    · ipureintro
      exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
    isplitl
    · iapply statusErrOk_nil
    isplitl
    · iintro !> -; iapply go_etcd_io.etcd.cache.v3.errCellOk_nil
    isplitl
    · ileft; ileft; ipureintro; rfl
    · ileft; ipureintro; rintro ⟨e, h, -⟩; cases h
  | ok ei =>
    wp_auto
    wp_apply wp_rpctypes_Error (GoInterface.ok ei) m $$ [$Hse $Hm]
      as %err1 ⟨%Hne1, #Hse1, %Hce1, #Hd1, #Hcl1, -, %Hrm⟩
    · ipureintro; simp
    have Hci := Herr (by simp)
    have Hc1 := Hce1 Hci
    obtain ⟨e1, rfl⟩ : ∃ e1, err1 = GoInterface.ok e1 := by
      cases err1 with
      | nil => exact absurd rfl Hne1
      | ok e => exact ⟨e, rfl⟩
    obtain ⟨Htarget, Hce'⟩ := Hc1
    obtain ⟨Hleaf, Htyped, -⟩ := Hce' e1 rfl
    ihave #Htree := errors.isErrorTree_leaf (GF := GF) e1 Hleaf Htyped
    wp_apply errors.wp_AsType (T' := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError)
        (T := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) (· = GoInterface.ok e1)
        (GoInterface.ok e1) $$ [$Htree] as %v' %b -
    · ipureintro; rfl
    have Hc1 : clientErr (GoInterface.ok e1) := ⟨Htarget, Hce'⟩
    have Hfin : ∀ e : GoInterface, e ≠ GoInterface.nil → clientErr e →
        ((GoInterface.ok ei = GoInterface.nil → e = GoInterface.nil) ∧
          (GoInterface.ok ei ≠ GoInterface.nil → e ≠ GoInterface.nil ∧ clientErr e)) :=
      fun e hne hc => ⟨fun h => absurd h (by simp), fun _ => ⟨hne, hc⟩⟩
    -- returning `rpctypes.Error`'s result
    ihave #Hret : iprop(⌜(GoInterface.ok ei = GoInterface.nil → GoInterface.ok e1 = GoInterface.nil) ∧
            (GoInterface.ok ei ≠ GoInterface.nil →
              GoInterface.ok e1 ≠ GoInterface.nil ∧ clientErr (GoInterface.ok e1))⌝ ∗
          statusErrOk (GoInterface.ok e1) ∗
          □ (go_etcd_io.etcd.cache.v3.errCellOk (GoInterface.ok ei) -∗
            go_etcd_io.etcd.cache.v3.errCellOk (GoInterface.ok e1)) ∗
          ((⌜GoInterface.ok ei = GoInterface.nil⌝ ∨ go_etcd_io.etcd.cache.v3.descIs (GoInterface.ok e1) m) ∨
            go_etcd_io.etcd.cache.v3.ctxErrIs (GoInterface.ok e1)) ∗
          (⌜¬ ∃ e : GoInterfaceOk, GoInterface.ok ei = GoInterface.ok e ∧
              go_etcd_io.etcd.cache.v3.ctxErrMsg m ∧ go_etcd_io.etcd.cache.v3.ctxErrShape e⌝ ∨
            go_etcd_io.etcd.cache.v3.ctxErrIs (GoInterface.ok e1) ∨
            go_etcd_io.etcd.cache.v3.descIs (GoInterface.ok e1) m)) $$ []
    · isplitr
      · ipureintro; exact Hfin _ Hne1 Hc1
      isplitr
      · iexact Hse1
      isplitr
      · iexact Hcl1
      isplitr
      · ileft; iright; iexact Hd1
      · iright; iright; iexact Hd1
    cases b
    · wp_auto
      ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
      · iPkgInit
      ihave ⟨%m1, #Hm1⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse1
      ihave ⟨%cFE, #HcFE⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_code _ $$ Hse1
      wp_apply wp_FromError (GoInterface.ok e1) m1 cFE $$ [$Hst $Hse1 $Hm1 $HcFE] as %sv %okv ⟨-, #HCode, -⟩
      cases okv
      · wp_auto
        iapply HΦ; iexact Hret
      · wp_auto
        wp_apply HCode
        wp_if_destruct
        · wp_apply Hce $$ %Broadcast.Pending as %e2 He2 %Hc2 - - -
          cases e2 with
          | nil =>
            wp_auto
            iapply HΦ; iexact Hret
          | ok e2 =>
            simp only [reduceCtorEq, ↓reduceIte]
            wp_auto
            wp_apply Hce $$ %Broadcast.Done [He2] as %e3 %Hne3 %Hc3 #Hs3 #Hcl3 Hd3
            · iexact He2
            icases Hd3 with (%Hn3 | ⟨%e3', %m3, %Hm3, #Hmsg3⟩)
            · exact absurd Hn3 Hne3
            ihave #Hci3 : go_etcd_io.etcd.cache.v3.ctxErrIs (GF := GF) e3 $$ []
            · unfold go_etcd_io.etcd.cache.v3.ctxErrIs
              iexists e3', m3
              isplitl []
              · ipureintro; exact Hm3
              · iexact Hmsg3
            iapply HΦ
            isplitr
            · ipureintro; exact ⟨False.elim, fun _ => ⟨Hne3, Hc3⟩⟩
            isplitr
            · iexact Hs3
            isplitr
            · iintro !> -; iexact Hcl3
            isplitr
            · iright; iexact Hci3
            · iright; ileft; iexact Hci3
        · wp_if_destruct
          · wp_apply Hce $$ %Broadcast.Pending as %e2 He2 %Hc2 - - -
            cases e2 with
            | nil =>
              wp_auto
              iapply HΦ; iexact Hret
            | ok e2 =>
              simp only [reduceCtorEq, ↓reduceIte]
              wp_auto
              wp_apply Hce $$ %Broadcast.Done [He2] as %e3 %Hne3 %Hc3 #Hs3 #Hcl3 Hd3
              · iexact He2
              icases Hd3 with (%Hn3 | ⟨%e3', %m3, %Hm3, #Hmsg3⟩)
              · exact absurd Hn3 Hne3
              ihave #Hci3 : go_etcd_io.etcd.cache.v3.ctxErrIs (GF := GF) e3 $$ []
              · unfold go_etcd_io.etcd.cache.v3.ctxErrIs
                iexists e3', m3
                isplitl []
                · ipureintro; exact Hm3
                · iexact Hmsg3
              iapply HΦ
              isplitr
              · ipureintro; exact ⟨False.elim, fun _ => ⟨Hne3, Hc3⟩⟩
              isplitr
              · iexact Hs3
              isplitr
              · iintro !> -; iexact Hcl3
              isplitr
              · iright; iexact Hci3
              · iright; ileft; iexact Hci3
          · iapply HΦ; iexact Hret
    · wp_auto
      iapply HΦ; iexact Hret

end proof

end EtcdGrove
end Perennial
