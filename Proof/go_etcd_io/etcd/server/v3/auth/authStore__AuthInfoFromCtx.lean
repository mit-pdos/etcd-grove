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
public import Perennial.Proof.strings.Link

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

/-- etcd-io/etcd#19775's strip of the bearer prefix (`if strings.HasPrefix(token, bearerPrefix)
{ token = token[len(bearerPrefix):] }`) is `strings.TrimPrefix(token, "Bearer ")`, the code it
replaces at the pin (etcd-io/etcd#21910, merged after the PR was opened). -/
theorem bearerStrip_eq_trimPrefix (v : GoString) :
    (if (go!"Bearer " : GoString) <+: v then v.drop (go!"Bearer " : GoString).length else v) =
      strings.trimPrefix v go!"Bearer " := rfl

theorem auth.authStore.AuthInfoFromCtx.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_FromIncomingContext : metadata.FromIncomingContext.spec (GF := GF) (hG := hG))
    (h_authInfoFromToken : auth.authStore.authInfoFromToken.spec (GF := GF) (hG := hG))
    (h_redactToken : auth.redactToken.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG) := by
  intro st R ctx
  wp_start as ⟨#Hinv, Hen⟩
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
    iunfold authErrIs; ileft; ipureintro; rfl
  wp_auto
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
    wp_apply strings.wp_HasPrefix
    -- etcd-io/etcd#19775: `if strings.HasPrefix(token, bearerPrefix) { token = token[len(bearerPrefix):] }`
    -- (through `[]byte` in the fork: no string slicing in Perennial's semantics); in both
    -- branches the token is `strings.TrimPrefix(ts[0], "Bearer ")`, the code before the PR
    -- (`bearerStrip_eq_trimPrefix`).
    by_cases hb : (go!"Bearer " : GoString) <+: v0
    case' pos =>
      simp only [hb, _root_.decide_true]
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      ihave %Hlen := ownSlice_len $$ Hsl
      ihave %Hwf := ownSlice_wf $$ Hsl
      have Hp : (go!"Bearer " : GoString).length ≤ v0.length := hb.length_le
      have Hk : 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) ≤ sint.Z sl.len := by
        have h7 : (go!"Bearer " : GoString).length = 7 := rfl
        constructor
        · decide
        · rw [h7] at Hp; have := Hlen.1; unfold sint.nat at this; word
      rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
      icases (ownSlice_split_all (W64 7) sl _ v0 Hk).1 $$ Hsl with ⟨-, Hsl⟩
      wp_apply wp_bytes_to_string $$ Hsl as -
      rw [show v0.drop 7 = strings.trimPrefix v0 go!"Bearer " by
        rw [← bearerStrip_eq_trimPrefix]; simp only [hb, ite_true]; rfl]
      (try wp_auto)
    case' neg =>
      simp only [hb, _root_.decide_false]
      ihave token : (token_ptr ↦ strings.trimPrefix v0 go!"Bearer ") $$ [token]
      · rw [← bearerStrip_eq_trimPrefix]; simp only [hb, ite_false]; iexact token
      (try wp_auto)
    all_goals
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
      wp_apply strings.wp_HasPrefix
      -- etcd-io/etcd#19775: `if strings.HasPrefix(token, bearerPrefix) { token = token[len(bearerPrefix):] }`
      -- (through `[]byte` in the fork: no string slicing in Perennial's semantics); in both
      -- branches the token is `strings.TrimPrefix(ts[0], "Bearer ")`, the code before the PR
      -- (`bearerStrip_eq_trimPrefix`).
      by_cases hb : (go!"Bearer " : GoString) <+: v0
      case' pos =>
        simp only [hb, _root_.decide_true]
        wp_auto
        wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
        ihave %Hlen := ownSlice_len $$ Hsl
        ihave %Hwf := ownSlice_wf $$ Hsl
        have Hp : (go!"Bearer " : GoString).length ≤ v0.length := hb.length_le
        have Hk : 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) ≤ sint.Z sl.len := by
          have h7 : (go!"Bearer " : GoString).length = 7 := rfl
          constructor
          · decide
          · rw [h7] at Hp; have := Hlen.1; unfold sint.nat at this; word
        rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
        icases (ownSlice_split_all (W64 7) sl _ v0 Hk).1 $$ Hsl with ⟨-, Hsl⟩
        wp_apply wp_bytes_to_string $$ Hsl as -
        rw [show v0.drop 7 = strings.trimPrefix v0 go!"Bearer " by
          rw [← bearerStrip_eq_trimPrefix]; simp only [hb, ite_true]; rfl]
        (try wp_auto)
      case' neg =>
        simp only [hb, _root_.decide_false]
        ihave token : (token_ptr ↦ strings.trimPrefix v0 go!"Bearer ") $$ [token]
        · rw [← bearerStrip_eq_trimPrefix]; simp only [hb, ite_false]; iexact token
        (try wp_auto)
      all_goals
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

end proof

end EtcdGrove
end Perennial
