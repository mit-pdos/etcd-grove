/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkLeaseLeases.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheckLemmas

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
theorem EtcdServer.checkLeaseLeases.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG))
    (hK : lease.Lease.Keys.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkLeaseLeases.spec (GF := GF) (hG := hG) := by
  intro s E γl ctx cd sl ls dq n m
  wp_start as ⟨#Hau, #Hlb, #Hlr, #Hpub, #Hctx, HRD, Htok, %Hbound, Hsl, #Hls⟩
  ihave ⟨%st, %cca, #Has, #Hreq, #Hreqb, #Hcca, #HLb⟩ := leaseCheckSetup s E n $$ [$Hau $Hlb $Hpub]
  iunfold isAuthStoreLeaseLb at HLb
  icases HLb with ⟨%ai, %Hai, #HEn, #HRev, #HAdm, -, #HRng⟩
  iunfold srvLessorRd at Hlr
  icases Hlr with ⟨%lp, #Hlf, #Hinv⟩
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave #Hap : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave ⟨⟨%eUE, #HUE, #HUEe⟩, ⟨%eOR, #HOR, #HORe⟩⟩ := leaseCheckErrs $$ Hap
  subst Hai
  (try wp_auto)
  -- `rev := s.AuthStore().Revision()`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HRev as %rev #Hrev
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
    iframe HRD Htok Hsl
    isplitl []
    · iapply applyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    ileft; iexact Hen
  | true =>
  (try wp_auto)
  -- `authInfo, err := s.AuthInfoFromCtx(ctx)`
  wp_apply (hAI s _ E.RD E.authMode cca ctx cd) $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hb⟩
  · iframe #
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD Htok Hsl Herr
    iintro %h; cases h
  (try wp_auto)
  iunfold authInfoOpt at Ha
  icases Ha with (%Han | ⟨%user, %rev', #Hai0⟩)
  · -- `if authInfo == nil { return auth.ErrUserEmpty }`
    subst Han
    (try wp_auto)
    iapply HΦ
    iframe HRD Htok Hsl HUEe
    iintro %h; cases h
  ihave #Hp := authInfoIs_pointsto a user rev' $$ Hai0
  ihave #Hib := infoBoundM_of_ctxBound E.authOn s E _ a user rev' $$ [Hb Hai0]
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
    iframe HRD Htok Hsl
    isplitl []
    · iapply applyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    iright
    iexists _
    iframe Hib
    ileft; iexact Hv
  (try wp_auto)
  -- `for _, l := range leases { for _, key := range l.Keys() { ... IsRangePermitted ... } }`
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  iunfold apply.permCheck3Lb at HRng
  ihave IHo : iprop(∃ (j : w64) (lv : Loc),
      "i" ∷ i_ptr ↦ j ∗ "l" ∷ l_ptr ↦ lv ∗ "Htok" ∷ threadTok ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ ∗
      "#Hcls" ∷ [∗list] x ∈ ls.take (sint.nat j),
        leaseOfKeysVerdictFrom E.authMode n ⟨user, rev'⟩ γl m x.2 x.1 .read) $$ [i l Htok]
  · iexists W64 0, _
    iframe i l Htok
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for IHo
  wp_if_destruct
  · have hjl : (sint.Z j).toNat < (ls.map Prod.fst).length := by unfold sint.nat at Hsll; word
    rw [List.length_map] at hjl
    obtain ⟨x, Hx⟩ : ∃ x, ls[(sint.Z j).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have Hx1 : (ls.map Prod.fst)[(sint.Z j).toNat]? = some x.1 := by
      rw [List.getElem?_map, Hx]; rfl
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) _ _ x.1 Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hx1
    ihave ⟨#Hlo, #Hlive⟩ := (BigSepL.bigSepL_lookup (Φ := fun _ (x : Loc × w64) =>
      iprop(lease.isLeaseObj (GF := GF) γl x.1 ∗ lease.leaseLiveFrom γl m x.2 x.1)) Hx) $$ Hls
    (try wp_auto)
    wp_apply (hK γl x.1 x.2 (.reader m)) $$ [Htok] as %ksl %ks ⟨Hks, Hpre, Hpost, %Hnd⟩
    · iframe Hlo; rw [lease.keysPre_reader]; iframe Htok Hlive; ipureintro; exact Hbound
    ihave Hpre : iprop(lease.leaseLiveFrom γl m x.2 x.1 ∗ threadTok ∗
        ⌜threadBound GF ≤ 2 ^ 30 - 1⌝) $$ [Hpre]
    · rw [← lease.keysPre_reader]; iexact Hpre
    icases Hpre with ⟨-, Htok, -⟩
    ihave #Hkf : lease.leaseKeysFrom γl m x.2 x.1 ks $$ [Hpost]
    · rw [← lease.keysPost_reader]; iexact Hpost
    ihave %Hshort := lease.leaseKeysFrom_short γl m x.2 x.1 ks $$ Hkf
    ihave %Hksll := ownSlice_len _ _ _ $$ Hks
    ihave IH : iprop(∃ (k : w64) (kv : GoString),
        "ik" ∷ i_ptr ↦ k ∗ "key" ∷ key_ptr ↦ kv ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z ksl.len⌝ ∗
        "#Hkc" ∷ [∗list] k ∈ ks.take (sint.nat k),
          auth.permVerdictFrom E.authMode n ⟨user, rev'⟩ k [] .read GoInterface.nil) $$ [i key]
    · iexists W64 0, _
      iframe i key
      isplitl []
      · ipureintro
        constructor
        · decide
        · have := Hksll.2; word
      · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
        iapply BigSepL.bigSepL_nil.2; itrivial
    wp_for IH
    wp_if_destruct
    · have hkl : (sint.Z k).toNat < ks.length := by unfold sint.nat at Hksll; word
      obtain ⟨kx, Hkx⟩ : ∃ kx, ks[(sint.Z k).toNat]? = some kx := ⟨_, List.getElem?_eq_getElem hkl⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z ksl.len := ⟨Hk.1, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index ksl (sint.Z k) _ _ kx Hk.1 $$ [Hks] as Hks
      · iframe; ipureintro; exact Hkx
      wp_apply wp_string_to_bytes kx as %bsl ⟨Hb, -⟩
      ihave %Hbl := ownSlice_len _ _ _ $$ Hb
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
      wp_apply HRng $$ [$Hp $Hb $Hre $HRD] as %err3 ⟨-, -, -, HRD, #Herr3, #Hv3⟩
      · ipureintro
        have h1 := Hshort kx (List.mem_of_getElem? Hkx)
        rw [Hbl.1] at h1
        have h3 := Hbl.2
        unfold sint.nat at h1
        word
      cases err3 with
      | nil =>
        (try wp_auto)
        wp_for_post
        iframe
        iexists k + W64 1, kx
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        · have hsn : sint.nat (k + W64 1) = sint.nat k + 1 := by unfold sint.nat at *; word
          rw [hsn, List.take_add_one, show ks[sint.nat k]? = some kx from Hkx, Option.toList_some]
          iapply BigSepL.bigSepL_snoc.2
          iframe Hkc
          iexact Hv3
      | ok e3 =>
        (try wp_auto)
        wp_for_post
        wp_for_post
        iapply HΦ
        iframe HRD Htok Hsl
        iunfold authApplyErrIs at Herr3
        icases Herr3 with ⟨#Herr3, -⟩
        iframe Herr3
        iintro %h; cases h
    have hallk : ks.take (sint.nat k) = ks := by
      apply List.take_of_length_le; unfold sint.nat at *; word
    rw [hallk] at *
    wp_for_post
    iframe
    iexists j + W64 1, x.1
    iframe
    isplitl []
    · ipureintro; constructor <;> word
    · have hsn : sint.nat (j + W64 1) = sint.nat j + 1 := by unfold sint.nat at *; word
      rw [hsn, List.take_add_one, show ls[sint.nat j]? = some x from Hx, Option.toList_some]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hcls
      iunfold leaseOfKeysVerdictFrom
      iexists ks
      iframe Hkf Hkc
  have hall : ls.take (sint.nat j) = ls := by
    have h := Hsll.1
    rw [List.length_map] at h
    apply List.take_of_length_le; unfold sint.nat at *; word
  rw [hall] at *
  -- `if rev != s.AuthStore().Revision() { return auth.ErrAuthOldRevision }`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HRev as %rev2 -
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ
    iframe HRD Htok Hsl
    isplitl []
    · iapply applyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    iright
    iexists _
    iframe Hib
    iright
    iexact Hcls
  · iapply HΦ
    iframe HRD Htok Hsl HORe
    iintro %h; cases h

end proof

end EtcdGrove
end Perennial
