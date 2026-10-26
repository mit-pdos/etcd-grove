/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/SetUp.lean` (the auth plan's
E2h). Lean-first (no Rocq counterpart).

The puts: two nested loops over `Principals()` and `{"a", "c"}`, each put in a timeout context
(`client.wp_WithTimeout_bg`), through `New`'s client with the caller's persistent update
(`client.client_Put_any`), the context cancelled after the call; the admin calls: one timeout
context, cancelled by the `defer` at every return, each call through the client's `Auth` field
(`isNewClient`'s `authObjAt`) with its persistent precondition from `setupAuthOk`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.keyOf
public import Spec.go_etcd_io.etcd.client.v3.authClient__UserAdd
public import Spec.go_etcd_io.etcd.client.v3.authClient__UserGrantRole
public import Spec.go_etcd_io.etcd.client.v3.authClient__RoleAdd
public import Spec.go_etcd_io.etcd.client.v3.authClient__RoleGrantPermission
public import Spec.go_etcd_io.etcd.client.v3.authClient__AuthEnable
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem SetUp.wp_proof
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_keyOf : keyOf.spec (GF := GF) (hG := hG))
    (wp_UserAdd : authClient.UserAdd.spec (GF := GF) (hG := hG))
    (wp_UserGrantRole : authClient.UserGrantRole.spec (GF := GF) (hG := hG))
    (wp_RoleAdd : authClient.RoleAdd.spec (GF := GF) (hG := hG))
    (wp_RoleGrantPermission : authClient.RoleGrantPermission.spec (GF := GF) (hG := hG))
    (wp_AuthEnable : authClient.AuthEnable.spec (GF := GF) (hG := hG)) :
    SetUp.spec (GF := GF) (hG := hG) := by
  intro CS EA FA RA CRE CEC cl ep V E γr cid mid Su Sg Sr Sp Se Q hAs
  wp_start as ⟨#Hnc, #Hput, #Hkv, #Hauth⟩
  ihave #Pc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_Principals as %psl Hpsl
  ihave %Hpl := ownSlice_len $$ Hpsl
  (try wp_auto)
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  ihave HI : (∃ (j : w64) (w0 : GoString) (r : w64),
      "i" ∷ i_ptr ↦ j ∗ "who" ∷ who_ptr ↦ w0 ∗ "Hpsl" ∷ psl ↦* principals ∗ "rev" ∷ rev_ptr ↦ r ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z psl.len⌝ : IProp GF) $$ [i who Hpsl rev]
  · iexists W64 0, _, _
    iframe
    ipureintro
    constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z psl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem principals (sint.nat j) as w
    have hwm : w ∈ principals := List.mem_of_getElem? Hw_lookup
    wp_apply wp_load_slice_index psl (sint.Z j) principals (DFrac.own 1) w Hj.1 $$ [Hpsl] as Hpsl
    · iframe; ipureintro; exact Hw_lookup
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoString) keyParts
    isplitr
    · ipureintro; rfl
    iintro %xsl ⟨Hxsl, -⟩
    simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
      show max (max (2 : Int) 0) 0 = 2 from rfl]
    (try wp_auto)
    rename_i oi_ptr
    ihave HJ : (∃ (n : w64) (x0 : GoString) (r' : w64),
        "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x0 ∗ "Hxsl" ∷ _ ↦* keyParts ∗ "rev" ∷ rev_ptr ↦ r' ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2⌝ : IProp GF) $$ [i x Hxsl rev]
    · iexists W64 0, _, _
      iframe
      ipureintro
      constructor <;> word
    wp_for HJ
    wp_if_destruct
    · have Hlt2 : sint.Z n < sint.Z (W64 2) := by simpa using Hif
      have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨Hn.1, Hlt2⟩
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      have Hnk : sint.nat n < keyParts.length := by rw [show keyParts.length = 2 from rfl]; word
      list_elem keyParts (sint.nat n) as x
      have hxm : x ∈ keyParts := List.mem_of_getElem? Hx_lookup
      wp_apply wp_load_slice_index _ (sint.Z n) keyParts (DFrac.own 1) x Hn.1 $$ [Hxsl] as Hxsl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      wp_apply context.wp_Background
      (try wp_auto)
      wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
        as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
      (try wp_auto)
      wp_apply wp_keyOf x w go!"d"
      (try wp_auto)
      have hk : keyOfK x w go!"d" ∈ setupKeys := by
        unfold setupKeys; exact List.mem_flatMap.2 ⟨w, hwm, List.mem_map.2 ⟨x, hxm, rfl⟩⟩
      wp_apply (client.client_Put_any cl [⟨ep, E, γr, cid, mid⟩] V cctx cd (keyOfK x w go!"d")
          go!"setup" slice.nil (fun _ => iprop(True))) $$ [] as %resp %err Hout
      · iframe #
        isplitr
        · iExactEq Hnc; rfl
        isplitr
        · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitr
        · iapply BigSepL.bigSepL_nil.2; itrivial
        iintro !>
        iapply BigAndL.bigAndL_singleton.2
        iapply Hkv
        ipureintro; exact hk
      (try wp_auto)
      wp_apply Hcancel
      icases Hout with (⟨%Herr, %m, #Hm, -⟩ | ⟨%Herr, -⟩)
      · subst Herr
        iunfold putRespMsg at Hm
        icases Hm with ⟨%Hnn, %h, %pk, #Hhd, #Hhf, -⟩
        iunfold hdrFull at Hhf
        icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, x, _
        iframe
        ipureintro; constructor <;> word
      · cases err with
        | nil => exact absurd rfl Herr
        | ok e =>
          (try wp_auto)
          wp_for_post
          wp_for_post
          (try wp_auto)
          iapply HΦ
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, w, _
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    ihave #Hnc' := Hnc
    iunfold isNewClient at Hnc'
    icases Hnc' with ⟨-, -, -, -, -, ⟨%ap, #Hauf, #Hap⟩⟩
    iunfold setupAuthOk at Hauth
    icases Hauth with ⟨#Hu, #Hg, #Hr, #Hp, #He, #P0, #P1, #P2, #P3, #P4, #P5, #P6, #P7⟩
    wp_apply context.wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
    (try wp_auto)
    wp_apply (wp_UserAdd ap [ep] cctx cd go!"root" go!"root-pw" Su (fun _ => Q 0)) $$ [] as %resp0 %err0 Hout0
    · iframe #
      iintro !>
      inext
      iExactEq P0; rfl
    iunfold authCallOut at Hout0
    icases Hout0 with (⟨%Herr0, Hq0⟩ | ⟨%Herr0, -⟩)
    rotate_left
    · cases err0 with
      | nil => exact absurd rfl Herr0.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr0
    (try wp_auto)
    wp_apply (wp_UserGrantRole ap [ep] cctx cd go!"root" go!"root" Sg (fun _ => Q 1)) $$ [] as %resp1 %err1 Hout1
    · iframe #
      iintro !>
      inext
      iExactEq P1; rfl
    iunfold authCallOut at Hout1
    icases Hout1 with (⟨%Herr1, Hq1⟩ | ⟨%Herr1, -⟩)
    rotate_left
    · cases err1 with
      | nil => exact absurd rfl Herr1.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr1
    (try wp_auto)
    wp_apply (wp_RoleAdd ap [ep] cctx cd go!"r" Sr (fun _ => Q 2)) $$ [] as %resp2 %err2 Hout2
    · iframe #
      iintro !>
      inext
      iExactEq P2; rfl
    iunfold authCallOut at Hout2
    icases Hout2 with (⟨%Herr2, Hq2⟩ | ⟨%Herr2, -⟩)
    rotate_left
    · cases err2 with
      | nil => exact absurd rfl Herr2.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr2
    (try wp_auto)
    wp_apply (wp_RoleGrantPermission ap [ep] cctx cd go!"r" go!"a" go!"b" (W32 2) Sp (fun _ => Q 3)) $$ [] as %resp3 %err3 Hout3
    · iframe #
      isplitr
      · ipureintro; decide
      iintro !>
      inext
      iExactEq P3; rfl
    iunfold authCallOut at Hout3
    icases Hout3 with (⟨%Herr3, Hq3⟩ | ⟨%Herr3, -⟩)
    rotate_left
    · cases err3 with
      | nil => exact absurd rfl Herr3.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr3
    (try wp_auto)
    wp_apply (wp_UserAdd ap [ep] cctx cd go!"u" go!"u-pw" Su (fun _ => Q 4)) $$ [] as %resp4 %err4 Hout4
    · iframe #
      iintro !>
      inext
      iExactEq P4; rfl
    iunfold authCallOut at Hout4
    icases Hout4 with (⟨%Herr4, Hq4⟩ | ⟨%Herr4, -⟩)
    rotate_left
    · cases err4 with
      | nil => exact absurd rfl Herr4.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr4
    (try wp_auto)
    wp_apply (wp_UserGrantRole ap [ep] cctx cd go!"u" go!"r" Sg (fun _ => Q 5)) $$ [] as %resp5 %err5 Hout5
    · iframe #
      iintro !>
      inext
      iExactEq P5; rfl
    iunfold authCallOut at Hout5
    icases Hout5 with (⟨%Herr5, Hq5⟩ | ⟨%Herr5, -⟩)
    rotate_left
    · cases err5 with
      | nil => exact absurd rfl Herr5.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr5
    (try wp_auto)
    wp_apply (wp_UserAdd ap [ep] cctx cd go!"v" go!"v-pw" Su (fun _ => Q 6)) $$ [] as %resp6 %err6 Hout6
    · iframe #
      iintro !>
      inext
      iExactEq P6; rfl
    iunfold authCallOut at Hout6
    icases Hout6 with (⟨%Herr6, Hq6⟩ | ⟨%Herr6, -⟩)
    rotate_left
    · cases err6 with
      | nil => exact absurd rfl Herr6.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr6
    (try wp_auto)
    wp_apply (wp_AuthEnable ap [ep] cctx cd Se (fun _ => Q 7)) $$ [] as %resp7 %err7 Hout7
    · iframe #
      iintro !>
      inext
      iExactEq P7; rfl
    iunfold authCallOut at Hout7
    icases Hout7 with (⟨%Herr7, Hq7⟩ | ⟨%Herr7, -⟩)
    rotate_left
    · cases err7 with
      | nil => exact absurd rfl Herr7.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr7
    (try wp_auto)
    wp_apply Hcancel
    (try wp_auto)
    iapply HΦ
    simp only [↓reduceIte]
    iframe

end proof

end authkv
end EtcdGrove
end Perennial
