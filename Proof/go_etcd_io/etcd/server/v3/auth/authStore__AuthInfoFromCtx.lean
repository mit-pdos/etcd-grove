/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__AuthInfoFromCtx.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__authInfoFromToken
public import Spec.go_etcd_io.etcd.server.v3.auth.redactToken
public import Spec.google_golang_org.grpc.metadata.FromIncomingContext
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.AuthInfoFromCtx.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_FromIncomingContext : metadata.FromIncomingContext.spec (GF := GF) (hG := hG))
    (h_authInfoFromToken : auth.authStore.authInfoFromToken.spec (GF := GF) (hG := hG))
    (h_redactToken : auth.redactToken.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG) := by
  intro st R M ctx
  wp_start as ⟨#Hinv, Hen⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, #Hs1, #Hs2, -⟩
  ihave #HeIT' := HeIT
  iunfold authErrVar at HeIT'
  icases HeIT' with ⟨%eIT, #HeITa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  wp_auto
  wp_apply (h_IsAuthEnabled st R M) $$ [$Hinv $Hen] as %en ⟨Hen, -⟩
  cases en
  · wp_auto
    iapply HΦ
    iframe
    isplitr
    · iunfold authInfoRO; ileft; ipureintro; rfl
    isplitr
    · iunfold authErrIs; ileft; ipureintro; rfl
    iunfold ctxBound; ileft; ipureintro; rfl
  wp_auto
  wp_apply h_FromIncomingContext as %md %ok Hmd
  icases Hmd with (⟨%Hok, %Hinc⟩ | ⟨%md0, %m, ⟨%Hok, %Hinc, %Hdom⟩, Hm, Hvals⟩)
  · subst Hok
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · iunfold authInfoRO; ileft; ipureintro; rfl
    isplitr
    · iunfold authErrIs; ileft; ipureintro; rfl
    iunfold ctxBound; ileft; ipureintro; rfl
  subst Hok
  wp_auto
  wp_apply wp_map_lookup2 go.string _ md m go!"token" $$ Hm as Hm
  cases h1 : m !! go!"token" with
  | some ts1 =>
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (k : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗ ⌜md0 k = some vs⌝)) h1).1 $$ Hvals
        with ⟨⟨%vs, Hts, %Hne, %Hmd0⟩, -⟩
    ihave %Htsl := ownSlice_len _ _ _ $$ Hts
    obtain ⟨v0, hv0⟩ : ∃ v0, vs[0]? = some v0 := by
      cases vs with
      | nil => exact absurd rfl Hne
      | cons x xs => exact ⟨x, rfl⟩
    have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ts1.len := by
      have : 0 < vs.length := by
        cases vs with
        | nil => exact absurd rfl Hne
        | cons _ _ => simp
      rw [Htsl.1] at this; constructor
      · decide
      · have := Htsl.2; unfold sint.nat at this; word
    simp only [Hbnd, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index ts1 (sint.Z (W64 0)) vs _ v0 (by decide) $$ [Hts] as Hts
    · iframe Hts; ipureintro; exact hv0
    wp_apply strings.wp_TrimPrefix
    (try wp_auto)
    wp_apply (h_authInfoFromToken st R M) $$ [$Hinv] as %ai %uok ⟨#Hai, #Hb⟩
    cases uok
    · (try wp_auto)
      wp_apply h_redactToken _ as %fp -
      (try wp_auto)
      wp_apply h_String _ _ as %f -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply h_Warn
      · ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iframe
      isplitr
      · iunfold authInfoRO; ileft; ipureintro; rfl
      isplitr
      · iunfold authErrIs
        iright
        iexists ErrInvalidAuthToken, eIT
        iframe HeITa
        ipureintro; simp
      iunfold ctxBound; ileft; ipureintro; rfl
    · (try wp_auto)
      iapply HΦ
      iframe
      isplitr
      · iexact Hai
      isplitr
      · iunfold authErrIs; ileft; ipureintro; rfl
      iunfold ctxBound; iright; iexists (strings.trimPrefix v0 [66#8, 101#8, 97#8, 114#8, 101#8, 114#8, 32#8])
      isplitr
      · ipureintro
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, vs = x :: xs := by
          cases vs with
          | nil => exact absurd rfl Hne
          | cons a l => exact ⟨a, l, rfl⟩
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv0
        subst hv0
        unfold ctxTokenOf
        rw [Hinc]
        simp only [Hmd0]
      iExactEq Hb
      simp
  | none =>
    simp only [Option.isSome_none, Option.getD_none]
    wp_auto
    wp_apply wp_map_lookup2 go.string _ md m go!"authorization" $$ Hm as Hm
    cases h2 : m !! go!"authorization" with
    | some ts2 =>
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun (k : GoString) (sl : GoSlice) =>
          iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗ ⌜md0 k = some vs⌝)) h2).1 $$ Hvals
          with ⟨⟨%vs, Hts, %Hne, %Hmd0⟩, -⟩
      ihave %Htsl := ownSlice_len _ _ _ $$ Hts
      obtain ⟨v0, hv0⟩ : ∃ v0, vs[0]? = some v0 := by
        cases vs with
        | nil => exact absurd rfl Hne
        | cons x xs => exact ⟨x, rfl⟩
      have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ts2.len := by
        have : 0 < vs.length := by
          cases vs with
          | nil => exact absurd rfl Hne
          | cons _ _ => simp
        rw [Htsl.1] at this; constructor
        · decide
        · have := Htsl.2; unfold sint.nat at this; word
      simp only [Hbnd, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index ts2 (sint.Z (W64 0)) vs _ v0 (by decide) $$ [Hts] as Hts
      · iframe Hts; ipureintro; exact hv0
      wp_apply strings.wp_TrimPrefix
      (try wp_auto)
      wp_apply (h_authInfoFromToken st R M) $$ [$Hinv] as %ai %uok ⟨#Hai, #Hb⟩
      cases uok
      · (try wp_auto)
        wp_apply h_redactToken _ as %fp -
        (try wp_auto)
        wp_apply h_String _ _ as %f -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Warn
        · ipureintro; exact Hlgnn
        (try wp_auto)
        iapply HΦ
        iframe
        isplitr
        · iunfold authInfoRO; ileft; ipureintro; rfl
        isplitr
        · iunfold authErrIs
          iright
          iexists ErrInvalidAuthToken, eIT
          iframe HeITa
          ipureintro; simp
        iunfold ctxBound; ileft; ipureintro; rfl
      · (try wp_auto)
        iapply HΦ
        iframe
        isplitr
        · iexact Hai
        isplitr
        · iunfold authErrIs; ileft; ipureintro; rfl
        iunfold ctxBound; iright; iexists (strings.trimPrefix v0 [66#8, 101#8, 97#8, 114#8, 101#8, 114#8, 32#8])
        isplitr
        · ipureintro
          obtain ⟨x, xs, rfl⟩ : ∃ x xs, vs = x :: xs := by
            cases vs with
            | nil => exact absurd rfl Hne
            | cons a l => exact ⟨a, l, rfl⟩
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv0
          subst hv0
          have h1' : md0 go!"token" = none := (Hdom _).1 h1
          unfold ctxTokenOf
          rw [Hinc]
          simp only [h1', Hmd0]
        iExactEq Hb
        simp
    | none =>
      simp only [Option.isSome_none, Option.getD_none]
      wp_auto
      iapply HΦ
      iframe
      isplitr
      · iunfold authInfoRO; ileft; ipureintro; rfl
      isplitr
      · iunfold authErrIs; ileft; ipureintro; rfl
      iunfold ctxBound; ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
