/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__prepareObjs.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__prepareObjs
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.decodeObj
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__acceptAll

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem watchChan.prepareObjs.wp_proof
    (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG))
    (wp_acceptAll : watchChan.acceptAll.spec (GF := GF) (hG := hG)) :
    watchChan.prepareObjs.spec (GF := GF) (hG := hG) := by
  intro Obj S W codec vi ti wc wp ctx p sel emp ep x σ r hdec
  wp_start as ⟨#Hw, #Hctx, #Hp, #Hcodec, #Hvi, #Hti, #Hsel, #Htr, #Hver, #Hwc, #Hep, #Hx⟩
  ihave #Htr' := Htr
  iunfold transformerOk at Htr'
  icases Htr' with ⟨#Hfrom, -⟩
  ihave #Hep' := Hep
  iStructNamed Hep'
  cases r with
  | bm rr a =>
    unfold kEvIs
    icases Hx with %Hx
    obtain ⟨-, Hpn, -⟩ := Hx
    wp_auto
    rw [Hpn]
    wp_auto
    iapply HΦ
    simp only [kCurObj, kOldObj, kObjOpt]
    iframe; ipureintro; simp
  | kv v =>
    unfold kEvIs
    icases Hx with ⟨%Hx, #Hval, %Hpv⟩
    obtain ⟨Hk, Hrev, -, Hdel, Hpn, -⟩ := Hx
    obtain ⟨d, st, o, hfs, hdo, hko⟩ := kDec_some (C := S.toObjCodec) hdec
    wp_auto
    rw [Hpn, Hdel]
    wp_auto
    wp_apply Hfrom $$ [$Hval] as %dsl %st' %terr Htr
    rw [hfs]
    icases Htr with ⟨%Hte, #Hdsl⟩
    obtain ⟨rfl, -⟩ := Hte
    wp_auto
    wp_apply wp_decodeObj Obj S W codec vi dsl d o x.rev' hdo $$ [] as %cur %derr ⟨%Hde, Hcur⟩
    · iframe #
    subst Hde
    wp_auto
    rw [Hpv]
    have h0 : decide (sint.Z (W64 0) < sint.Z (slice.nil : GoSlice).len) = false := by
      simp [slice.nil]
    rw [h0]
    wp_auto
    iapply HΦ
    simp only [kCurObj, kOldObj, kObjOpt, kRawRev, hko]
    rw [← Hrev]
    iframe
  | ev e =>
    obtain ⟨hdc, hdp⟩ := hdec
    by_cases hc : e.del = false ∧ e.kv.createRev = e.kv.modRev
    · -- a create: the previous value is `nil`
      unfold kEvIs
      simp only [hc, _root_.and_self, ↓reduceIte]
      icases Hx with ⟨%Hx, #Hval, %Hpv⟩
      obtain ⟨Hk, Hrev, Hdel, Hcr, Hpn⟩ := Hx
      obtain ⟨d, st, o, hfs, hdo, hko⟩ := kDec_some (C := S.toObjCodec) (hdc hc.1)
      wp_auto
      rw [Hpn]
      wp_auto
      rw [Hdel]
      wp_auto
      wp_apply Hfrom $$ [$Hval] as %dsl %st' %terr Htr
      rw [hfs]
      icases Htr with ⟨%Hte, #Hdsl⟩
      obtain ⟨rfl, -⟩ := Hte
      wp_auto
      wp_apply wp_decodeObj Obj S W codec vi dsl d o x.rev' hdo $$ [] as %cur %derr ⟨%Hde, Hcur⟩
      · iframe #
      subst Hde
      wp_auto
      rw [Hpv]
      have h0 : decide (sint.Z (W64 0) < sint.Z (slice.nil : GoSlice).len) = false := by
        simp [slice.nil]
      rw [h0]
      wp_auto
      iapply HΦ
      simp only [kCurObj, kOldObj, kObjOpt, kRawRev, hc, hko, _root_.and_self, ↓reduceIte,
        Bool.false_eq_true]
      rw [← Hrev]
      iframe
    · -- not a create: the previous value is the key's record before
      unfold kEvIs
      simp only [hc, ↓reduceIte]
      icases Hx with ⟨%Hx, #Hval, %pr, %Hpr, #Hpvs⟩
      obtain ⟨Hk, Hrev, Hdel, Hcr, Hpn⟩ := Hx
      obtain ⟨d2, st2, o2, hfs2, hdo2, hko2⟩ := kDec_some (C := S.toObjCodec) (hdp hc pr Hpr)
      have hne : pr.value ≠ [] := S.toObjCodec.ne_nil_of_dec _ (hdp hc pr Hpr)
      ihave %Hlen := ownSlice_len _ _ _ $$ Hpvs
      have hpos : decide (sint.Z (W64 0) < sint.Z x.prevValue'.len) = true := by
        have : 0 < pr.value.length := List.length_pos_iff.mpr hne
        simp only [decide_eq_true_eq]; rw [show sint.Z (W64 0) = 0 from rfl]; word
      wp_auto
      rw [Hpn]
      wp_auto
      cases hd : e.del with
      | true =>
        rw [Hdel, hd]
        wp_auto
        rw [hpos]
        wp_auto
        try rw [Hdel, hd]
        try wp_auto
        wp_apply Hfrom $$ [$Hpvs] as %dsl2 %st2 %terr2 Htr2
        rw [hfs2]
        icases Htr2 with ⟨%Hte2, #Hdsl2⟩
        obtain ⟨rfl, -⟩ := Hte2
        wp_auto
        wp_apply wp_decodeObj Obj S W codec vi dsl2 d2 o2 x.rev' hdo2 $$ [] as %old %derr2 ⟨%Hde2, Hold⟩
        · iframe #
        subst Hde2
        wp_auto
        iapply HΦ
        simp only [kCurObj, kOldObj, kObjOpt, kRawRev, hd, hko2, Hpr, ↓reduceIte, true_or,
          Option.bind_some, Bool.true_eq_false, false_and]
        rw [← Hrev]
        iframe
      | false =>
        obtain ⟨d, st, o, hfs, hdo, hko⟩ := kDec_some (C := S.toObjCodec) (hdc hd)
        have hcr : e.kv.createRev ≠ e.kv.modRev := fun h => hc ⟨hd, h⟩
        rw [Hdel, hd]
        wp_auto
        wp_apply Hfrom $$ [$Hval] as %dsl %st' %terr Htr
        rw [hfs]
        icases Htr with ⟨%Hte, #Hdsl⟩
        obtain ⟨rfl, -⟩ := Hte
        wp_auto
        wp_apply wp_decodeObj Obj S W codec vi dsl d o x.rev' hdo $$ [] as %cur %derr ⟨%Hde, Hcur⟩
        · iframe #
        subst Hde
        wp_auto
        rw [hpos]
        wp_auto
        try rw [Hdel, hd]
        try wp_auto
        wp_apply wp_acceptAll Obj S wc p sel emp $$ []
        · iframe #
        cases he : emp with
        | true =>
          wp_auto
          iapply HΦ
          simp only [kCurObj, kOldObj, kObjOpt, kRawRev, hd, hcr, _root_.and_false, hko, ↓reduceIte,
            Bool.false_eq_true, Bool.true_eq_false, or_self]
          rw [← Hrev]
          iframe
        | false =>
          wp_auto
          wp_apply Hfrom $$ [$Hpvs] as %dsl2 %st2 %terr2 Htr2
          rw [hfs2]
          icases Htr2 with ⟨%Hte2, #Hdsl2⟩
          obtain ⟨rfl, -⟩ := Hte2
          wp_auto
          wp_apply wp_decodeObj Obj S W codec vi dsl2 d2 o2 x.rev' hdo2 $$ [] as %old %derr2 ⟨%Hde2, Hold⟩
          · iframe #
          subst Hde2
          wp_auto
          iapply HΦ
          simp only [kCurObj, kOldObj, kObjOpt, kRawRev, hd, hcr, _root_.and_false, hko, hko2, Hpr, ↓reduceIte,
            Bool.false_eq_true, _root_.or_true, Option.bind_some]
          rw [← Hrev]
          iframe

end proof

end k8s
end EtcdGrove
end Perennial
