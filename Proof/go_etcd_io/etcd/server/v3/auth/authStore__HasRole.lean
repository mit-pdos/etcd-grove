/-
Proof of the spec of the same name (the auth plan's S4c, 2026-10-24). Lean-first (no Rocq
counterpart). The loop over the user's roles returns at the first equal to the asked one; when
it runs out, none was.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__HasRole
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Proof.go_etcd_io.etcd.server.v3.auth.AdminLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.HasRole.wp_proof
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    auth.authStore.HasRole.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post user rn
  wp_start as ⟨#Hinv, Hown, HWR, Hcs⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, Hca⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC⟩
  subst Hbi
  (try wp_auto)
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, -, -, -, -, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨#HUG, -, -, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #user))
  iapply HUG $$ %st0 %user HL
  inext
  iintro %u ⟨HL, Hu⟩
  (try wp_auto)
  wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
  · ipureintro; exact Hl0
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    ihave %Hnone := userOut_null st0 user $$ Hu
    (try wp_auto)
    wp_apply h_String _ _ as %f1 -
    (try wp_auto)
    wp_apply h_String _ _ as %f2 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Warn
    · ipureintro; exact Hlgnn
    (try wp_auto)
    iapply HΦ
    iframe HPost Hown
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    ipureintro
    exact ⟨st0, Hl0, by simp [Hnone]⟩
  ihave Hu' := auth.userOut_some_named _ st0 user Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  obtain ⟨Hlook, Hurn, Hurr, Hsorted⟩ := Hur
  iunfold ownUser at Hu
  icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, #Hunm, #Hupw, #Hurl, #Huo⟩
  icases typedPointsto_split _ _ _ $$ Hup with Hup
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hup
  (try wp_auto)
  irename : (iprop("_" ∷ True) : IProp GF) => Hjunk
  iclear Hjunk
  ihave %Hrl := ownSlice_len _ _ _ $$ Hurl
  ihave IH : iprop(∃ (n : w64) (rv : GoString),
      "i" ∷ i_ptr ↦ n ∗ "r" ∷ r_ptr ↦ rv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ur.roles.length ∧ rn ∉ ur.roles.take (sint.nat n)⌝)
    $$ [i r]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by simp, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z url.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hn : sint.nat n < ur.roles.length := by rw [Hrl.1]; word
    obtain ⟨x, hx⟩ : ∃ x, ur.roles[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z url.len := ⟨Hn.1, hlt⟩
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index url (sint.Z n) ur.roles .discard x Hn.1 $$ [$Hurl] as -
    · iframe; ipureintro; exact hx
    (try wp_auto)
    have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_if_destruct
    · -- found
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe HPost Hown
      isplitl [Hbe HT Hen Hca]
      · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      ipureintro
      refine ⟨st0, Hl0, ?_⟩
      have hm : rn ∈ ur.roles := by
        have : x = rn := by first | exact Hif.symm | exact Hif | simpa using Hif.symm
        rw [← this]; exact List.mem_of_getElem? hx
      simp only [true_iff]
      exact ⟨roles, Hlook, Hurr ▸ hm⟩
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, x
      iframe
      ipureintro
      refine ⟨by word, by rw [hsucc]; omega, ?_⟩
      rw [hsucc, List.take_succ, hx, Option.toList_some]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact Hn.2.2 h
      · simp at h; apply Hif; first | rw [h] | (subst h; rfl) | simp [h]
  · -- the loop ran out: the role is not there
    have hall : sint.nat n = ur.roles.length := by
      have : ¬ sint.Z n < sint.Z url.len := by
        first | exact Hif | exact fun h => Hif (by simpa using h)
      rw [Hrl.1]; word
    (try wp_auto)
    iapply HΦ
    iframe HPost Hown
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    ipureintro
    refine ⟨st0, Hl0, ?_⟩
    have hnm : rn ∉ ur.roles := by have := Hn.2.2; rwa [hall, List.take_length] at this
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨u', hu', hm⟩
    rw [Hlook] at hu'; cases hu'
    exact hnm (Hurr ▸ hm)

end proof

end EtcdGrove
end Perennial
