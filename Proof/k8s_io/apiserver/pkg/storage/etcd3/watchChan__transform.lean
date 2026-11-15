/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__transform.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__transform
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__prepareObjs
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__filter
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__acceptAll

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem watchChan.transform.wp_proof
    (wp_prepareObjs : watchChan.prepareObjs.spec (GF := GF) (hG := hG))
    (wp_filter : watchChan.filter.spec (GF := GF) (hG := hG))
    (wp_acceptAll : watchChan.acceptAll.spec (GF := GF) (hG := hG)) :
    watchChan.transform.spec (GF := GF) (hG := hG) := by
  intro Obj S W codec vi ti wc wp ctx nf p sel emp ep x σ r hdec hkv hev
  wp_start as ⟨#Hw, #Hctx, #Hp, #Hrt, #Hcodec, #Hnf, #Hvi, #Hti, #Hsel, #Htr, #Hver, #Hwc, #Hnew,
    #Hep, #Hx⟩
  wp_auto
  wp_apply wp_prepareObjs Obj S W codec vi ti wc wp ctx p sel emp ep x σ r hdec $$ []
    as %cur %old %err ⟨%He, Hcur, Hold⟩
  · iframe #
  subst He
  ihave #Hep' := Hep
  iStructNamed Hep'
  wp_auto
  cases r with
  | bm rr a =>
    unfold kEvIs
    icases Hx with %Hx
    obtain ⟨Hrev, Hpn, Hann⟩ := Hx
    rw [Hpn]
    wp_auto
    ihave #Hnew' := Hnew
    iunfold newItemOk at Hnew'
    wp_apply Hnew' as %obj Hobj
    ihave #Hver' := Hver
    iunfold versionerOk at Hver'
    icases Hver' with ⟨-, -, #HUpd, -⟩
    (try wp_auto)
    wp_apply HUpd $$ [$Hobj] as %uerr ⟨Hobj, %Hue⟩
    subst Hue
    wp_auto
    rw [Hann]
    cases a with
    | true =>
      ihave #Hwc' := Hwc
      iunfold watchContractOk at Hwc'
      icases Hwc' with ⟨-, #HAnn⟩
      wp_auto
      wp_apply HAnn $$ [$Hobj] as %aerr ⟨%Hae, Hobj⟩
      subst Hae
      wp_auto
      icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
      simp only [Hnn, decide_false, Bool.not_false]
      wp_auto
      iapply HΦ
      simp only [kRawToEv, wevAt, kEvTypeStr, show ¬ (3 : Nat) = 4 by decide,
        show ¬ (3 : Nat) = 0 by decide, show ¬ (3 : Nat) = 1 by decide,
        show ¬ (3 : Nat) = 2 by decide, ↓reduceIte]
      rw [← Hrev]
      isplitr
      · itrivial
      iexists _
      iframe
      ipureintro; simp
    | false =>
      wp_auto
      icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
      simp only [Hnn, decide_false, Bool.not_false]
      wp_auto
      iapply HΦ
      simp only [kRawToEv, wevAt, kEvTypeStr, show ¬ (3 : Nat) = 4 by decide,
        show ¬ (3 : Nat) = 0 by decide, show ¬ (3 : Nat) = 1 by decide,
        show ¬ (3 : Nat) = 2 by decide, ↓reduceIte, Bool.false_eq_true]
      rw [← Hrev]
      isplitr
      · itrivial
      iexists _
      iframe
      ipureintro; simp
  | kv v =>
    unfold kEvIs
    icases Hx with ⟨%Hx, #Hval, %Hpv⟩
    obtain ⟨Hk, Hrev, Hcr, Hdel, Hpn, Hini⟩ := Hx
    obtain ⟨d, st, o, -, -, hko⟩ := kDec_some (C := S.toObjCodec) hdec
    have hW : W64 ((sint.nat v.modRev : Nat) : Int) = v.modRev := by
      have := hkv v rfl; unfold sint.nat; word
    simp only [kCurObj, kObjOpt, kRawRev, hko]
    rw [Hpn]
    wp_auto
    rw [Hdel]
    wp_auto
    rw [Hcr]
    wp_auto
    wp_apply wp_filter Obj S wc p sel emp cur o (S.fmtRV v.modRev) $$ [$Hcur] as Hcur
    · iframe #
    cases hs : sel o with
    | false =>
      wp_auto
      iapply HΦ
      simp only [kRawToEv, hko, hs, Option.bind_some, Bool.false_eq_true, ↓reduceIte]
      itrivial
    | true =>
      wp_auto
      icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
      simp only [Hnn, decide_false, Bool.not_false]
      wp_auto
      iapply HΦ
      simp only [kRawToEv, hko, hs, Option.bind_some, ↓reduceIte, wevAt, kEvTypeStr,
        show ¬ (0 : Nat) = 4 by decide, Bool.false_eq_true, hW]
      isplitr
      · itrivial
      iexists _
      iframe
      ipureintro; simp
  | ev e =>
    obtain ⟨hdc, hdp⟩ := hdec
    have hW : W64 ((sint.nat e.kv.modRev : Nat) : Int) = e.kv.modRev := by
      have := hev e rfl; unfold sint.nat; word
    cases hd : e.del with
    | true =>
      unfold kEvIs
      simp only [hd, Bool.true_eq_false, false_and, ↓reduceIte]
      icases Hx with ⟨%Hx, #Hval, %pr, %Hpr, #Hpvs⟩
      obtain ⟨Hk, Hrev, Hdel, Hcr, Hpn⟩ := Hx
      have hne : ¬ (e.del = false ∧ e.kv.createRev = e.kv.modRev) := by simp [hd]
      obtain ⟨d2, st2, o2, -, -, hko2⟩ := kDec_some (C := S.toObjCodec) (hdp hne pr Hpr)
      simp only [kOldObj, kObjOpt, kRawRev, hd, hko2, Hpr, Bool.true_eq_false, false_and,
        ↓reduceIte, true_or, Option.bind_some]
      rw [Hpn]
      wp_auto
      rw [Hdel]
      wp_auto
      wp_apply wp_filter Obj S wc p sel emp old o2 (S.fmtRV e.kv.modRev) $$ [$Hold] as Hold
      · iframe #
      cases hs : sel o2 with
      | false =>
        wp_auto
        iapply HΦ
        simp only [kRawToEv, kEvOfL, hd, Hpr, hko2, hs, Option.bind_some, Bool.false_eq_true,
          ↓reduceIte]
        isplitr <;> itrivial
      | true =>
        wp_auto
        icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
        simp only [Hnn, decide_false, Bool.not_false]
        wp_auto
        iapply HΦ
        simp only [kRawToEv, kEvOfL, hd, Hpr, hko2, hs, Option.bind_some, ↓reduceIte, wevAt,
          kEvTypeStr, show ¬ (2 : Nat) = 4 by decide, Bool.false_eq_true, hW]
        isplitr
        · itrivial
        iexists _
        iframe
        ipureintro; simp
    | false =>
      obtain ⟨d, st, o, -, -, hko⟩ := kDec_some (C := S.toObjCodec) (hdc hd)
      by_cases hcr : e.kv.createRev = e.kv.modRev
      · -- a create
        unfold kEvIs
        simp only [hd, hcr, _root_.and_self, ↓reduceIte]
        icases Hx with ⟨%Hx, #Hval, %Hpv⟩
        obtain ⟨Hk, Hrev, Hdel, Hcr, Hpn⟩ := Hx
        simp only [kCurObj, kObjOpt, kRawRev, hd, hko, Bool.false_eq_true, ↓reduceIte]
        rw [Hpn]
        wp_auto
        rw [Hdel]
        wp_auto
        rw [Hcr]
        wp_auto
        wp_apply wp_filter Obj S wc p sel emp cur o (S.fmtRV e.kv.modRev) $$ [$Hcur] as Hcur
        · iframe #
        cases hs : sel o with
        | false =>
          wp_auto
          iapply HΦ
          simp only [kRawToEv, kEvOfL, hd, hcr, hko, hs, Option.bind_some, Bool.false_eq_true,
            ↓reduceIte, decide_true]
          isplitr <;> itrivial
        | true =>
          wp_auto
          icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
          simp only [Hnn, decide_false, Bool.not_false]
          wp_auto
          iapply HΦ
          simp only [kRawToEv, kEvOfL, hd, hcr, hko, hs, Option.bind_some, ↓reduceIte, wevAt,
            kEvTypeStr, show ¬ (0 : Nat) = 4 by decide, Bool.false_eq_true, hW, decide_true]
          isplitr
          · itrivial
          iexists _
          iframe
          ipureintro; simp
      · -- an update
        have hne : ¬ (e.del = false ∧ e.kv.createRev = e.kv.modRev) := fun h => hcr h.2
        unfold kEvIs
        simp only [hd, hcr, _root_.and_false, ↓reduceIte]
        icases Hx with ⟨%Hx, #Hval, %pr, %Hpr, #Hpvs⟩
        obtain ⟨Hk, Hrev, Hdel, Hcr, Hpn⟩ := Hx
        obtain ⟨d2, st2, o2, -, -, hko2⟩ := kDec_some (C := S.toObjCodec) (hdp hne pr Hpr)
        simp only [kCurObj, kObjOpt, kRawRev, hd, hko, Bool.false_eq_true, ↓reduceIte]
        rw [Hpn]
        wp_auto
        rw [Hdel]
        wp_auto
        rw [Hcr]
        wp_auto
        wp_apply wp_acceptAll Obj S wc p sel emp $$ []
        · iframe #
        cases he : emp with
        | true =>
          wp_auto
          icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
          simp only [Hnn, decide_false, Bool.not_false]
          wp_auto
          iapply HΦ
          simp only [kRawToEv, kEvOfL, hd, hcr, hko, Option.bind_some, ↓reduceIte, wevAt,
            kEvTypeStr, show ¬ (1 : Nat) = 4 by decide, show ¬ (1 : Nat) = 0 by decide,
            Bool.false_eq_true, hW, decide_false]
          isplitr
          · itrivial
          iexists _
          iframe
          ipureintro; simp
        | false =>
          simp only [kOldObj, hd, hcr, hko2, Hpr, _root_.and_false, ↓reduceIte,
            Bool.false_eq_true, _root_.or_true, Option.bind_some]
          wp_auto
          wp_apply wp_filter Obj S wc p sel false cur o (S.fmtRV e.kv.modRev) $$ [$Hcur] as Hcur
          · iframe #
          (try wp_auto)
          wp_apply wp_filter Obj S wc p sel false old o2 (S.fmtRV e.kv.modRev) $$ [$Hold] as Hold
          · iframe #
          cases hs : sel o <;> cases hs2 : sel o2
          · wp_auto
            iapply HΦ
            simp only [kRawToEv, kEvOfL, hd, hcr, hko, hko2, Hpr, hs, hs2, Option.bind_some,
              ↓reduceIte, Bool.false_eq_true, decide_false, Bool.and_false]
            isplitr <;> itrivial
          · wp_auto
            icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
            simp only [Hnn, decide_false, Bool.not_false]
            wp_auto
            iapply HΦ
            simp only [kRawToEv, kEvOfL, hd, hcr, hko, hko2, Hpr, hs, hs2, Option.bind_some,
              ↓reduceIte, Bool.false_eq_true, decide_false, Bool.and_false, Bool.and_true,
              Bool.and_self, wevAt, kEvTypeStr, hW, show ¬ (2 : Nat) = 4 by decide, show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide]
            isplitr
            · itrivial
            iexists _
            iframe
            ipureintro; simp
          · wp_auto
            icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
            simp only [Hnn, decide_false, Bool.not_false]
            wp_auto
            iapply HΦ
            simp only [kRawToEv, kEvOfL, hd, hcr, hko, hko2, Hpr, hs, hs2, Option.bind_some,
              ↓reduceIte, Bool.false_eq_true, decide_false, Bool.and_false, Bool.and_true,
              Bool.and_self, wevAt, kEvTypeStr, hW, show ¬ (0 : Nat) = 4 by decide]
            isplitr
            · itrivial
            iexists _
            iframe
            ipureintro; simp
          · wp_auto
            icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨H0, %Hnn⟩
            simp only [Hnn, decide_false, Bool.not_false]
            wp_auto
            iapply HΦ
            simp only [kRawToEv, kEvOfL, hd, hcr, hko, hko2, Hpr, hs, hs2, Option.bind_some,
              ↓reduceIte, Bool.false_eq_true, decide_false, Bool.and_false, Bool.and_true,
              Bool.and_self, wevAt, kEvTypeStr, hW, show ¬ (1 : Nat) = 4 by decide, show ¬ (1 : Nat) = 0 by decide]
            isplitr
            · itrivial
            iexists _
            iframe
            ipureintro; simp

end proof

end k8s
end EtcdGrove
end Perennial
