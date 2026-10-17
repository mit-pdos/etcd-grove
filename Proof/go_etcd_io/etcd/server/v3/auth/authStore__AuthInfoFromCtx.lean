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
public import Spec.context.ValueInternalRoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  intro st R ctx o
  wp_start as ⟨#Hinv, Hen, #Hroot⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, ⟨%s1, #Hs1⟩, ⟨%s2, #Hs2⟩⟩
  ihave #HeIT' := HeIT
  iunfold authErrVar at HeIT'
  icases HeIT' with ⟨%eIT, #HeITa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  wp_auto
  wp_apply (h_IsAuthEnabled st R) $$ [$Hinv $Hen] as %en Hen
  cases en
  · wp_auto
    iapply HΦ
    iframe
    isplitr
    · iunfold authInfoRO; ileft; ipureintro; rfl
    isplitr
    · iunfold authErrIs; ileft; ipureintro; rfl
    iapply rootInfoIf_nil
  wp_auto
  -- the PR's fast path: the context's root value, of this store
  wp_bind (App (Val #(methods ctx.ty go!"Value" ctx.v)) _)
  ihave Hroot' := Hroot
  iunfold ctxRootIs at Hroot'
  iapply Hroot'
  inext
  iintro %v %Hv
  have Hcases : (∃ x, o = some x ∧ x.store' = st) ∨ (∀ x, o = some x → x.store' ≠ st) := by
    cases o with
    | none => right; intro x h; cases h
    | some x =>
      by_cases h : x.store' = st
      · left; exact ⟨x, rfl, h⟩
      · right; intro y hy; cases hy; exact h
  rcases Hcases with ⟨x, rfl, Hxs⟩ | Hno
  · -- the fast path
    simp only [rootValIs] at Hv
    subst Hv
    wp_auto
    simp only [Hxs, decide_true]
    wp_auto
    wp_alloc a as Ha
    icases typedPointsto_not_null_dup _ _ _ $$ Ha with ⟨Ha, %Hann⟩
    iStructNamed Ha
    ipersist Username
    ipersist Revision
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · iunfold authInfoRO; iright; iexists go!"root", x.revision'
      iframe #; ipureintro; exact Hann
    isplitr
    · iunfold authErrIs; ileft; ipureintro; rfl
    unfold rootInfoIf
    iright; isplitr
    · ipureintro; rfl
    iright; iframe #; ipureintro; exact Hann
  ihave HΦ : ∀ (a : Loc) (err : GoInterface), enabledRd st ∗ authInfoRO a ∗ authErrIs err -∗
      Φ (PairV #a #err) $$ [HΦ]
  · iintro %a %err ⟨H1, H2, H3⟩
    iapply HΦ
    iframe
    iapply rootInfoIf_other st o a err Hno
  cases o
  rcases Hv with rfl | ⟨ii, rfl, Hii⟩
  wp_auto
  rotate_left
  wp_auto
  simp only [Hii, ↓reduceIte]
  wp_auto
  rotate_left
  simp only [rootValIs] at Hv
  subst Hv
  wp_auto
  rw [decide_eq_false (Hno _ rfl)]
  wp_auto
  all_goals
    wp_apply h_FromIncomingContext as %md %ok Hmd
    icases Hmd with (%Hok | ⟨%m, Hm, Hvals⟩)
    · subst Hok
      wp_auto
      iapply HΦ
      iframe
      isplitr
      · iunfold authInfoRO; ileft; ipureintro; rfl
      iunfold authErrIs; ileft; ipureintro; rfl
    cases ok
    · wp_auto
      iapply HΦ
      iframe
      isplitr
      · iunfold authInfoRO; ileft; ipureintro; rfl
      iunfold authErrIs; ileft; ipureintro; rfl
    wp_auto
    wp_apply wp_map_lookup2 go.string _ md m s1 $$ Hm as Hm
    cases h1 : m !! s1 with
    | some ts1 =>
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : GoString) (sl : GoSlice) =>
          iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝)) h1).1 $$ Hvals with ⟨⟨%vs, Hts, %Hne⟩, -⟩
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
      wp_apply (h_authInfoFromToken st R) $$ [$Hinv] as %ai %uok Hai
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
        iunfold authErrIs
        iright
        iexists ErrInvalidAuthToken, eIT
        iframe HeITa
        ipureintro; simp
      · (try wp_auto)
        iapply HΦ
        iframe
        iunfold authErrIs; ileft; ipureintro; rfl
    | none =>
      simp only [Option.isSome_none, decide_false, Option.getD_none]
      wp_auto
      wp_apply wp_map_lookup2 go.string _ md m s2 $$ Hm as Hm
      cases h2 : m !! s2 with
      | some ts2 =>
        simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
        wp_auto
        icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : GoString) (sl : GoSlice) =>
            iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝)) h2).1 $$ Hvals with ⟨⟨%vs, Hts, %Hne⟩, -⟩
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
        wp_apply (h_authInfoFromToken st R) $$ [$Hinv] as %ai %uok Hai
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
          iunfold authErrIs
          iright
          iexists ErrInvalidAuthToken, eIT
          iframe HeITa
          ipureintro; simp
        · (try wp_auto)
          iapply HΦ
          iframe
          iunfold authErrIs; ileft; ipureintro; rfl
      | none =>
        simp only [Option.isSome_none, decide_false, Option.getD_none]
        wp_auto
        iapply HΦ
        iframe
        isplitr
        · iunfold authInfoRO; ileft; ipureintro; rfl
        iunfold authErrIs; ileft; ipureintro; rfl

/-- The spec before etcd-io/etcd#22493 (on `lean`), for a context not nil: an auth info and
`nil` or `ErrInvalidAuthToken`, of any context. -/
abbrev auth.authStore.AuthInfoFromCtx.spec_old : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ enabledRd st }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromCtx")) (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); enabledRd st ∗ authInfoRO a ∗ authErrIs err }}

/-- **The PR's spec implies the old one** (for a context not nil), given that every context
carries some root value (`context.ValueInternalRoot.spec`, the trust boundary): callers that
used the old spec are unaffected. -/
theorem auth.authStore.AuthInfoFromCtx.spec_implies_old
    (h : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hV : context.ValueInternalRoot.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthInfoFromCtx.spec_old (GF := GF) (hG := hG) := by
  intro st R ctx
  iintro %Φ ⟨#Hpkg, #Hinv, Hen⟩ HΦ
  icases (hV ctx) with ⟨%o, #Hr⟩
  iapply (h st R ctx o) $$ [Hen]
  · iframe; iframe #
  iintro !> %a %err ⟨Hen, #Ha, #Herr, -⟩
  iapply HΦ
  iframe; iframe #

end proof

end EtcdGrove
end Perennial
