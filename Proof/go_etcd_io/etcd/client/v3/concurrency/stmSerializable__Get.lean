/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stmSerializable__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__fetch
public import Spec.go_etcd_io.etcd.client.v3.concurrency.respToValue
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithSerializable
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMReads

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stmSerializable.Get.wp_proof (hWG : writeSet.get.spec (GF := GF) (hG := hG))
    (hF : stm.fetch.spec (GF := GF) (hG := hG)) (hRV : respToValue.spec (GF := GF) (hG := hG))
    (hWR : EtcdGrove.WithRev.spec (GF := GF) (hG := hG))
    (hWS : EtcdGrove.WithSerializable.spec (GF := GF) (hG := hG)) :
    stmSerializable.Get.spec (GF := GF) (hG := hG) := by
  intro lvl p pfx st ksl ks
  wp_start as ⟨Hst, #Hks, %Hser, %Hpk⟩
  ihave %Hlen := ownSlice_len $$ Hks
  unfold stmState
  simp only [stmBase, Hser, ↓reduceIte]
  icases Hst with ⟨#Henv, Hrs, Hws, ⟨%gs, Hopts, %Hgs⟩, #Hcf, ⟨%pre, Hpre, %HpreOk⟩⟩
  wp_auto
  wp_if_destruct
  · have Hks0 : ks = [] := by
      obtain ⟨h1, h2⟩ := Hlen
      rw [Hif] at h1
      exact List.length_eq_zero_iff.1 (by rw [h1]; rfl)
    subst Hks0
    iapply HΦ
    iapply stmRet_ret
    iexists st
    isplitl
    · iframe Henv Hrs Hws Hcf
      isplitl [Hopts]
      · iexists gs; iframe Hopts; ipureintro; exact Hgs
      iexists pre; iframe Hpre; ipureintro; exact HpreOk
    ipureintro
    exact ⟨rfl, ⟨fun _ _ h => h, fun k h => Or.inl h⟩, fun _ => rfl, fun h => absurd rfl h⟩
  have Hksne : 0 < ks.length := by
    have h1 := Hlen.1
    have h2 : sint.Z ksl.len ≠ 0 := by intro h; apply Hif; word
    have h3 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 h3; omega
  unfold stmWsetOwn
  icases Hws with ⟨%wm, %wsMap, Hwf, Hwm, #Hwat⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType writeSet.ty) (m := go!"get")]
  wp_auto
  wp_apply hWG wm (DFrac.own 1) pfx wsMap st.writes ksl ks $$ [$Hpkg $Hwm $Hwat $Hks] as %wp ⟨Hwm, Hwp⟩
  icases Hwp with (⟨%Hpn, %Hnw⟩ | ⟨%k, %w, %sp, %Hw, Hwp⟩)
  rotate_left
  · ihave %Hpnn := typedPointsto_not_null $$ Hwp
    rw [decide_eq_false Hpnn]
    iStructNamed Hwp
    wp_auto
    obtain ⟨Hk, Hwk, Hv⟩ := Hw
    iapply HΦ
    iapply stmRet_ret
    iexists st
    isplitl
    · iframe Henv Hrs Hcf
      isplitl [Hwf Hwm]
      · iexists wm, wsMap; iframe Hwf Hwm Hwat
      isplitl [Hopts]
      · iexists gs; iframe Hopts; ipureintro; exact Hgs
      iexists pre; iframe Hpre; ipureintro; exact HpreOk
    ipureintro
    refine ⟨rfl, ⟨fun _ _ h => h, fun k' h => Or.inl h⟩, fun h => by simp [h] at Hk, fun _ => ?_⟩
    exact ⟨k, Hk, Or.inl ⟨w, Hwk, Hv⟩⟩
  obtain ⟨rfl, -⟩ := Hpn
  wp_auto
  unfold stmRsetOwn
  icases Hrs with ⟨%rm, %rsMap, Hrf, Hrm, #Hrat⟩
  unfold stmPreOwn
  icases Hpre with ⟨%pm, %preMap, Hpf, Hpm, #Hpat⟩
  wp_auto
  wp_apply wp_map_len $$ Hrm as Hrm
  ihave IH : iprop(∃ (n : w64) (rsMap' preMap' : GMap GoString Loc)
      (reads' pre' : GMap GoString ReadM) (kv : GoString),
      "Hi" ∷ i_ptr ↦ n ∗ "Hkey" ∷ key_ptr ↦ kv ∗
      "Hrm" ∷ rm ↦$ rsMap' ∗ "#Hrat" ∷ readsAt pfx rsMap' reads' ∗
      "Hpm" ∷ pm ↦$ preMap' ∗ "#Hpat" ∷ readsAt pfx preMap' pre' ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ks.length ∧
        MoveInv st pre ks (sint.nat n) reads' pre'⌝) $$ [i key Hrm Hpm]
  · iexists W64 0, rsMap, preMap, st.reads, pre, _
    iframe i key Hrm Hpm Hrat Hpat
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 by decide]; omega, ?_⟩
    exact MoveInv_init st pre ks
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hn0, Hnl, Hmv⟩ := Hn
    have Hlt : sint.nat n < ks.length := by
      have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hn0 ⊢; omega
    obtain ⟨k, Hk⟩ : ∃ k, ks[sint.nat n]? = some k := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksl.len := ⟨Hn0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ksl (sint.Z n) ks _ k Hn0 $$ [Hks] as -
    · iframe Hks; ipureintro; exact Hk
    wp_apply wp_map_lookup2 $$ Hpm as Hpm
    have Hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by
      have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hn0 ⊢; word
    have Hnat1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
      have h1 := Hn1; have h2 := Hn0; unfold sint.nat; simp only [sint.Z] at h1 h2 ⊢; omega
    have Hknw : st.writes !! k = none := Hnw k (List.mem_of_getElem? Hk)
    ihave #Hpat' := Hpat
    iunfold readsAt at Hpat'
    icases Hpat' with ⟨%Hpdom, #Hpall⟩
    cases Hpk' : preMap' !! k with
    | some rp =>
      obtain ⟨e, He⟩ : ∃ e, pre' !! k = some e := by
        have h := Hpdom k
        rw [Hpk'] at h
        exact Option.isSome_iff_exists.1 (by simpa using h.symm)
      ihave #Hr := Hpall $$ %k %rp %e %Hpk' %He
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      wp_auto
      wp_apply wp_mapDelete $$ Hpm as Hpm
      wp_apply wp_mapInsert $$ Hrm as Hrm
      wp_for_post
      iframe
      iexists n + W64 1, _, _, GMap.insert k e reads', GMap.delete k pre', k
      iframe Hi Hkey Hrm Hpm
      isplitr
      · iapply readsAt_insert_rd $$ [Hrat Hr]
        isplitl
        · iexact Hrat
        · iexact Hr
      isplitr
      · iapply readsAt_delete $$ Hpat
      ipureintro
      refine ⟨by omega, by rw [Hn1]; have h := Hlt; have h0 := Hn0; simp only [sint.nat, sint.Z] at h h0 ⊢; omega, ?_⟩
      rw [Hnat1]
      exact MoveInv_found st pre ks _ reads' pre' k e Hmv Hk He HpreOk Hknw
    | none =>
      have He : pre' !! k = none := by
        have h := Hpdom k
        rw [Hpk'] at h
        cases hp : pre' !! k with
        | none => rfl
        | some _ => rw [hp] at h; simp at h
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, rsMap', preMap', reads', pre', k
      iframe Hi Hkey Hrm Hpm Hrat Hpat
      ipureintro
      refine ⟨by omega, by rw [Hn1]; have h := Hlt; have h0 := Hn0; simp only [sint.nat, sint.Z] at h h0 ⊢; omega, ?_⟩
      rw [Hnat1]
      exact MoveInv_notfound st pre ks _ reads' pre' k Hmv Hk He
  · obtain ⟨Hn0, Hnl, Hmv⟩ := Hn
    have Hnk : sint.nat n = ks.length := by
      have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hnl Hn0 ⊢; omega
    rw [Hnk] at Hmv
    have Hgs' : ReadOptsOk gs := by
      unfold GetOptsOk at Hgs
      rw [Hser] at Hgs
      simp only [↓reduceIte] at Hgs
      rcases Hgs with h | ⟨S, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨S, h⟩)
    ihave Hrs : stmRsetOwn pfx (structFieldRef stmSerializable go!"stm" p) reads' $$ [Hrf Hrm]
    · unfold stmRsetOwn
      iexists rm, rsMap'
      iframe Hrf Hrm Hrat
    wp_apply hF (structFieldRef stmSerializable go!"stm" p) pfx reads' gs ksl ks $$ [$Hpkg $Henv $Hrs $Hopts $Hks] as %r Hr
    · ipureintro; exact ⟨Hgs', Hpk⟩
    iunfold stmRet at Hr
    icases Hr with (⟨%rp, %Hrp', %reads'', Hrs, Hopts, %Hgrow, Hrp⟩ | %Hab)
    rotate_left
    · obtain ⟨err, Hne, rfl⟩ := Hab
      unfold stmAbort
      wp_auto
      iapply HΦ
      iapply stmRet_abort _ Hne
    subst Hrp'
    icases Hrp with (%Hnil | ⟨%k, %e, %e', %Hke, #He⟩)
    · exact absurd Hnil.1 (List.ne_nil_of_length_pos Hksne)
    obtain ⟨Hfin1, Hfin2⟩ := MoveInv_final st pre ks reads' pre' reads'' Hmv HpreOk Hgrow
    cases hfr : decide (W64 (GMap.size rsMap : Int) = W64 0)
    · wp_auto
      wp_apply hRV rp e.value $$ [$Hpkg]
      · iright; iexists pfx, k, e; iframe He; ipureintro; rfl
      iapply HΦ
      iapply stmRet_ret
      iexists ({ reads := reads'', writes := st.writes } : STMSt)
      iunfold stmRsetOwn at Hrs
      icases Hrs with ⟨%rm2, %rsMap2, Hrf2, Hrm2, #Hrat2⟩
      isplitl
      · iframe Henv Hcf
        isplitl [Hrf2 Hrm2]
        · iexists rm2, rsMap2; iframe Hrf2 Hrm2 Hrat2
        isplitl [Hwf Hwm]
        · iexists wm, wsMap; iframe Hwf Hwm Hwat
        isplitl [Hopts]
        · iexists gs; iframe Hopts; ipureintro; exact Hgs
        iexists pre'
        isplitl [Hpf Hpm]
        · iexists pm, preMap'; iframe Hpf Hpm Hpat
        ipureintro; exact Hfin2
      ipureintro
      obtain ⟨Hk, Hre', Hkv⟩ := Hke
      exact ⟨rfl, Hfin1, fun h => absurd h (List.ne_nil_of_length_pos Hksne),
        fun _ => ⟨k, Hk, Or.inr ⟨Hnw k Hk, e', Hre', by simp [ReadM.value, Hkv]⟩⟩⟩
    · ihave #He' := He
      iunfold readRespAt at He'
      icases He' with ⟨%Hrpn, -, ⟨%h, #Hh, %Hhn, #Hhr⟩, -⟩
      wp_auto
      ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
      · iPkgInit
      wp_apply hWR e.hdr $$ [$Hcv] as %f1 #Hf1
      wp_apply hWS $$ [$Hcv] as %f2 #Hf2
      wp_apply wp_slice_literal (l := [f1, f2])
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      ipersist Hosl
      iunfold stmOptsOwn at Hopts
      icases Hopts with ⟨%gsl, Hgf, -⟩
      wp_auto
      ihave Hopts : stmOptsOwn (structFieldRef stmSerializable go!"stm" p) [withRevM e.hdr, withSerializableM] $$ [Hgf]
      · unfold stmOptsOwn
        iexists _
        iframe Hgf
        unfold optsAt
        iexists [f1, f2]
        iframe Hosl
        isplitr
        · ipureintro; rfl
        imodintro
        iintro %i %f %g %Hf %Hg
        rcases i with _ | _ | i
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf1
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg
          subst Hf Hg; iexact Hf2
        · simp at Hf
      wp_apply hRV rp e.value $$ [$Hpkg]
      · iright; iexists pfx, k, e; iframe He; ipureintro; rfl
      iapply HΦ
      iapply stmRet_ret
      iexists ({ reads := reads'', writes := st.writes } : STMSt)
      iunfold stmRsetOwn at Hrs
      icases Hrs with ⟨%rm2, %rsMap2, Hrf2, Hrm2, #Hrat2⟩
      isplitl
      · iframe Henv Hcf
        isplitl [Hrf2 Hrm2]
        · iexists rm2, rsMap2; iframe Hrf2 Hrm2 Hrat2
        isplitl [Hwf Hwm]
        · iexists wm, wsMap; iframe Hwf Hwm Hwat
        isplitl [Hopts]
        · iexists [withRevM e.hdr, withSerializableM]; iframe Hopts; ipureintro; unfold GetOptsOk; rw [Hser]; simp only [↓reduceIte]; exact Or.inr ⟨e.hdr, rfl⟩
        iexists pre'
        isplitl [Hpf Hpm]
        · iexists pm, preMap'; iframe Hpf Hpm Hpat
        ipureintro; exact Hfin2
      ipureintro
      obtain ⟨Hk, Hre', Hkv⟩ := Hke
      exact ⟨rfl, Hfin1, fun h => absurd h (List.ne_nil_of_length_pos Hksne),
        fun _ => ⟨k, Hk, Or.inr ⟨Hnw k Hk, e', Hre', by simp [ReadM.value, Hkv]⟩⟩⟩

end proof

end concurrency
end EtcdGrove
end Perennial
