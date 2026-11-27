/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkLeaseTimeToLiveKeys.lean` (F7 fork,
2026-11-26, SPECULATIVE). Lean-first (no Rocq counterpart): `checkLeaseTimeToLive.wp_proof`'s auth steps, its
loop over the given keys instead of a lease's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseTimeToLiveKeys
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheckLemmas
public import Perennial.Algebra.BigOp.BigSepL

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 4000000 in
theorem EtcdServer.checkLeaseTimeToLiveKeys.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkLeaseTimeToLiveKeys.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd tok keys kbs n
  wp_start as ⟨#Hau, #Hlb, #Hpub, #Hctx, #Hlib, #HtokC, HRD, Hks, Hkbs⟩
  -- the keys' bytes, named
  ihave ⟨%ks, HL⟩ := Perennial.big_sepL_exists_to_sepL2
    (fun _ (kb : GoSlice) (k : List w8) => iprop(kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝)) kbs $$ Hkbs
  ihave %HlenL := BigSepL2.bigSepL2_length $$ HL
  -- the ownership the post gives back, whatever the outcome
  ihave HL' : iprop([∗list] kb;k ∈ kbs;ks, kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝) $$ [HL]
  · iexact HL
  ihave ⟨%st, %cca, #Has, #Hreq, #Hreqb, #Hcca, #HLb⟩ := leaseCheckSetup s E n $$ [$Hau $Hlb $Hpub]
  iunfold isAuthStoreLeaseLb at HLb
  icases HLb with ⟨%ai, %Hai, #HEn, #HRev, #HAdm, -, #HRng⟩
  ihave #Hap : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave ⟨⟨%eUE, #HUE, #HUEe⟩, -⟩ := leaseCheckErrs $$ Hap
  subst Hai
  -- dropping the length facts from the returned ownership
  ihave Hback : iprop(([∗list] kb;k ∈ kbs;ks, kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝) -∗
      [∗list] kb;k ∈ kbs;ks, kb ↦* k) $$ []
  · iintro H
    iapply (BigSepL2.bigSepL2_mono_of_forall (Φ := fun _ (kb : GoSlice) (k : List w8) =>
      iprop(kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝)) (Ψ := fun _ (kb : GoSlice) (k : List w8) =>
      iprop(kb ↦* k)) (fun {_ _ _} => sep_elim_left)) $$ H
  (try wp_auto)
  -- `if !s.AuthStore().IsAuthEnabled() { return nil }`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HEn $$ [$HRD] as %b ⟨HRD, #Hen⟩
  (try wp_auto)
  cases b with
  | false =>
    (try wp_auto)
    iapply HΦ
    iframe HRD Hks
    iexists ks
    isplitl [HL' Hback]
    · iapply Hback $$ HL'
    isplitl []
    · iapply authApplyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    ileft; iexact Hen
  | true =>
  (try wp_auto)
  -- `authInfo, err := s.AuthInfoFromCtx(ctx)`
  ihave %Hon := enabledVerdictFrom_true_isOn E.authMode n $$ Hen
  wp_apply (hAI s _ E.RD E.authMode cca ctx cd n tok) $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr0, #Hb, #Hae, -⟩
  · iframe #
  ihave #Herr := authApplyErrIs_apply _ $$ Herr0
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD Hks
    iexists ks
    isplitl [HL' Hback]
    · iapply Hback $$ HL'
    isplitr
    · iunfold authApplyErrIs; iframe Herr; iapply Hae; ipureintro; exact Hon
    iintro %h; cases h
  (try wp_auto)
  iunfold authInfoOpt at Ha
  icases Ha with (%Han | ⟨%user, %rev', #Hai0⟩)
  · -- `if authInfo == nil { return auth.ErrUserEmpty }`
    subst Han
    (try wp_auto)
    iapply HΦ
    iframe HRD Hks
    iexists ks
    isplitl [HL' Hback]
    · iapply Hback $$ HL'
    isplitr
    · ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hap
      icases Hai with ⟨#HUEv, -⟩
      iapply apply.authErrVar_authApplyErrIs go_etcd_io.etcd.server.v3.auth.ErrUserEmpty
        (by simp [go_etcd_io.etcd.server.v3.auth.authErrMsgs]) _ $$ HUEv
      iexists eUE; iframe HUE; ipureintro; rfl
    iintro %h; cases h
  ihave #Hp := authInfoIs_pointsto a user rev' $$ Hai0
  ihave #Hib := principalBoundOn_of_ctxBound E.authOn s E tok a user rev' $$ [Hb Hai0]
  · iframe Hai0; iintro %h; iapply Hb $$ %h
  iunfold authInfoIs at Hai0
  icases Hai0 with ⟨%Hann, -, -⟩
  simp only [Hann, decide_false]
  (try wp_auto)
  -- `if s.AuthStore().IsAdminPermitted(authInfo) == nil { return nil }`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HAdm $$ [$Hp $HRD] as %err2 ⟨-, HRD, #Herr2, #Hv⟩
  (try wp_auto)
  rcases err2 with e2 | _
  rotate_left
  · (try wp_auto)
    iapply HΦ
    iframe HRD Hks
    iexists ks
    isplitl [HL' Hback]
    · iapply Hback $$ HL'
    isplitl []
    · iapply authApplyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    iright
    iexists _
    iframe Hib
    ileft; iexact Hv
  -- `for _, key := range keys { if err := s.AuthStore().IsRangePermitted(authInfo, key, []byte{}); ... }`
  (try wp_auto)
  ihave %Hsll := ownSlice_len _ _ _ $$ Hks
  iunfold apply.permCheck3Lb at HRng
  ihave IH : iprop(∃ (j : w64) (kb : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "key" ∷ key_ptr ↦ kb ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z keys.len⌝ ∗
      "#Hcls" ∷ [∗list] k ∈ ks.take (sint.nat j),
        auth.permVerdictFrom E.authMode n ⟨user, rev'⟩ k [] .read GoInterface.nil) $$ [i key]
  · iexists W64 0, _
    iframe i key
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z keys.len := by simpa using Hif
    have hjl : (sint.Z j).toNat < kbs.length := by unfold sint.nat at Hsll; word
    obtain ⟨kbx, Hkbx⟩ : ∃ kbx, kbs[(sint.Z j).toNat]? = some kbx := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hjl2 : (sint.Z j).toNat < ks.length := by rw [← HlenL]; exact hjl
    obtain ⟨kx, Hkx⟩ : ∃ kx, ks[(sint.Z j).toNat]? = some kx := ⟨_, List.getElem?_eq_getElem hjl2⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z keys.len := ⟨Hj.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index keys (sint.Z j) _ _ kbx Hj.1 $$ [Hks] as Hks
    · iframe; ipureintro; exact Hkbx
    (try wp_auto)
    ihave ⟨⟨Hkb, %Hkbl⟩, Hclose⟩ := BigSepL2.bigSepL2_lookup_acc Hkbx Hkx $$ HL'
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) []
    wp_auto
    rw [show go.arrayLiteralSize ([] : List keyed_element) = 0 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %re_ptr ⟨Hre, -⟩
    (try wp_auto)
    wp_apply (hAS s _) as -
    · iframe #
    (try wp_auto)
    wp_apply HRng $$ [$Hp $Hkb $Hre $HRD] as %err3 ⟨-, Hkb, -, HRD, #Herr3, #Hv3⟩
    · ipureintro; exact Hkbl
    ihave HL' := Hclose $$ [Hkb]
    · iframe Hkb; ipureintro; exact Hkbl
    cases err3 with
    | nil =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, kbx
      iframe
      isplitl []
      · ipureintro; constructor <;> word
      · have hsn : sint.nat (j + W64 1) = sint.nat j + 1 := by unfold sint.nat at *; word
        rw [hsn, List.take_add_one, show ks[sint.nat j]? = some kx from Hkx, Option.toList_some]
        iapply BigSepL.bigSepL_snoc.2
        iframe Hcls
        iexact Hv3
    | ok e3 =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe HRD Hks
      iexists ks
      isplitl [HL' Hback]
      · iapply Hback $$ HL'
      iframe Herr3
      iintro %h; cases h
  have Hif' : ¬ sint.Z j < sint.Z keys.len := by simpa using Hif
  have hall : ks.take (sint.nat j) = ks := by
    apply List.take_of_length_le; rw [← HlenL]; unfold sint.nat at *; word
  rw [hall] at *
  (try wp_auto)
  iapply HΦ
  iframe HRD Hks
  iexists ks
  isplitl [HL' Hback]
  · iapply Hback $$ HL'
  isplitl []
  · iapply authApplyErrIs_nil
  iintro %_
  iunfold leaseCheckFrom
  iright
  iexists _
  iframe Hib
  iright
  iexact Hcls

end proof

end EtcdGrove
end Perennial
