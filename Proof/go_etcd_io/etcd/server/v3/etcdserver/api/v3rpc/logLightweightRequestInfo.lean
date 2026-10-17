/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/logLightweightRequestInfo.lean`
(etcd#21764, pr-verify). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logLightweightRequestInfo
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.ByteString
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Strings
public import Spec.go_uber_org.zap.Logger__Info

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3
  go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 1600000 in
theorem v3rpc.logLightweightRequestInfo.wp_proof
    (hS : zap.String.spec (GF := GF) (hG := hG))
    (hBS : zap.ByteString.spec (GF := GF) (hG := hG))
    (hD : zap.Duration.spec (GF := GF) (hG := hG))
    (hI : zap.Int'.spec (GF := GF) (hG := hG))
    (hI64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hSs : zap.Strings.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    v3rpc.logLightweightRequestInfo.spec (GF := GF) (hG := hG) := by
  intro lg method remote duration req u
  wp_start as ⟨%Hlg, #Hreq⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply hS as %f0 -
  wp_apply hS as %f1 -
  wp_apply hD as %f2 -
  wp_apply wp_slice_literal (V := zap.zapcore.Field) [f0, f1, f2]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, Hfcap⟩
  wp_auto
  cases u with
  | range r =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with ⟨%Hr, %ksl, %esl, #Hk, #He⟩
    obtain ⟨rfl, Hrn⟩ := Hr
    (try wp_auto)
    wp_apply hBS as %fk -
    wp_apply wp_slice_literal (V := zap.zapcore.Field) [fk]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs1] as %fsl1 ⟨Hfsl, Hfcap, -⟩
    (try wp_auto)
    wp_if_destruct
    · wp_apply hBS as %fe -
      wp_apply wp_slice_literal (V := zap.zapcore.Field) [fe]
      isplitr
      · ipureintro; rfl
      iintro %s2 ⟨Hs2, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs2] as %fsl2 ⟨Hfsl, Hfcap, -⟩
      (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial
  | put r =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with ⟨%Hr, %ksl, #Hk⟩
    obtain ⟨rfl, Hrn⟩ := Hr
    (try wp_auto)
    wp_apply hBS as %fk -
    wp_apply wp_slice_literal (V := zap.zapcore.Field) [fk]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs1] as %fsl1 ⟨Hfsl, Hfcap, -⟩
    (try wp_auto)
    wp_apply hInfo
    · ipureintro; exact Hlg
    iapply HΦ; itrivial
  | del r =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with ⟨%Hr, %ksl, %esl, #Hk, #He⟩
    obtain ⟨rfl, Hrn⟩ := Hr
    (try wp_auto)
    wp_apply hBS as %fk -
    wp_apply wp_slice_literal (V := zap.zapcore.Field) [fk]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs1] as %fsl1 ⟨Hfsl, Hfcap, -⟩
    (try wp_auto)
    wp_if_destruct
    · wp_apply hBS as %fe -
      wp_apply wp_slice_literal (V := zap.zapcore.Field) [fe]
      isplitr
      · ipureintro; rfl
      iintro %s2 ⟨Hs2, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs2] as %fsl2 ⟨Hfsl, Hfcap, -⟩
      (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial
  | grant r =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with ⟨%Hr, %ttl, %id, #Ht, #Hi⟩
    obtain ⟨rfl, Hrn⟩ := Hr
    (try wp_auto)
    wp_apply hI64 as %ft -
    wp_apply hI64 as %fi -
    wp_apply wp_slice_literal (V := zap.zapcore.Field) [ft, fi]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs1] as %fsl1 ⟨Hfsl, Hfcap, -⟩
    (try wp_auto)
    wp_apply hInfo
    · ipureintro; exact Hlg
    iapply HΦ; itrivial
  | revoke r =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with ⟨%Hr, %id, #Hi⟩
    obtain ⟨rfl, Hrn⟩ := Hr
    (try wp_auto)
    wp_apply hI64 as %fi -
    wp_apply wp_slice_literal (V := zap.zapcore.Field) [fi]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hs1] as %fsl1 ⟨Hfsl, Hfcap, -⟩
    (try wp_auto)
    wp_apply hInfo
    · ipureintro; exact Hlg
    iapply HΦ; itrivial
  | other =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with %Hty
    cases req with
    | nil =>
      (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial
    | ok ii =>
      have h := Hty ii rfl
      simp only [v3rpc.lwTypes, List.mem_cons, List.not_mem_nil, not_or] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
      (try wp_auto)
      (try simp only [h1, h2, h3, h4, h5, h6, ite_false, decide_false, ↓reduceIte])
      (try wp_auto)
      (try simp only [h1, h2, h3, h4, h5, h6, ite_false, decide_false, ↓reduceIte])
      (try wp_auto)
      (try simp only [h1, h2, h3, h4, h5, h6, ite_false, decide_false, ↓reduceIte])
      (try wp_auto)
      (try simp only [h1, h2, h3, h4, h5, h6, ite_false, decide_false, ↓reduceIte])
      (try wp_auto)
      (try simp only [h1, h2, h3, h4, h5, h6, ite_false, decide_false, ↓reduceIte])
      (try wp_auto)
      (try simp only [h1, h2, h3, h4, h5, h6, ite_false, decide_false, ↓reduceIte])
      (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial
  | txn r =>
    iunfold v3rpc.lwReqIs at Hreq
    icases Hreq with ⟨%Hr, %csl, %cps, #Hc, #Hcs, #Hcm⟩
    obtain ⟨rfl, Hrn⟩ := Hr
    ihave %Hlen := ownSlice_len _ _ _ $$ Hcs
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      all_goals
        (try wp_auto)
        wp_apply (wp_slice_make3 (V := GoString) (W64 0) _ (by constructor <;> word)) as %ks ⟨Hks, Hkcap, -⟩
        (try wp_auto)
        ihave IH : iprop(∃ (n c : w64) (ks res : GoSlice) (kss : List GoString),
            "i" ∷ i_ptr ↦ n ∗ "count" ∷ count_ptr ↦ c ∗ "keys" ∷ keys_ptr ↦ ks ∗
            "Hks" ∷ ks ↦* kss ∗ "Hkcap" ∷ ownSliceCap GoString ks (DFrac.own 1) ∗
            "rangeEnds" ∷ rangeEnds_ptr ↦ res ∗
            "Hres" ∷ (⌜res = slice.nil⌝ ∨ ∃ ress : List GoString,
              res ↦* ress ∗ ownSliceCap GoString res (DFrac.own 1)) ∗
            "%Hn" ∷ ⌜0 ≤ sint.Z n⌝ ∗ "%Hc" ∷ ⌜0 ≤ sint.Z c⌝) $$ [i count keys Hks Hkcap rangeEnds]
        · iexists W64 0, _, ks, slice.nil, _
          iframe
          isplitl
          · ileft; ipureintro; rfl
          ipureintro; constructor <;> word
        wp_for IH
        wp_if_destruct
        · (try wp_auto)
          split
          · rename_i Hlt10
            have Hlt : sint.nat n < cps.length := by rw [Hlen.1]; word
            obtain ⟨cp, Hcp⟩ : ∃ cp, cps[sint.nat n]? = some cp := ⟨_, List.getElem?_eq_getElem Hlt⟩
            ihave #Hcpi := Hcm $$ %(sint.nat n) %cp %Hcp
            iunfold v3rpc.lwCmpIs at Hcpi
            icases Hcpi with ⟨%Hcpn, %ksl, %esl, %k, %e, #HK, #HKs, #HE, #HEs⟩
            have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z csl.len := ⟨Hn, Hif⟩
            (try wp_auto)
            simp only [Hbnd, _root_.and_self, ↓reduceIte]
            (try wp_auto)
            wp_apply wp_load_slice_index csl (sint.Z n) _ DFrac.discard cp Hn $$ [] as -
            · iframe #; ipureintro; exact Hcp
            (try wp_auto)
            wp_apply wp_bytes_to_string $$ [HKs] as -
            · iexact HKs
            wp_apply wp_slice_literal (V := GoString) [k]
            isplitr
            · ipureintro; rfl
            iintro %s1 ⟨Hs1, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hks $Hkcap $Hs1] as %ks1 ⟨Hks, Hkcap, -⟩
            (try wp_auto)
            simp only [Hbnd, _root_.and_self, ↓reduceIte]
            (try wp_auto)
            wp_apply wp_load_slice_index csl (sint.Z n) _ DFrac.discard cp Hn $$ [] as -
            · iframe #; ipureintro; exact Hcp
            (try wp_auto)
            wp_if_destruct
            · (try wp_auto)
              wp_if_destruct
              · (try wp_auto)
                wp_apply (wp_slice_make3 (V := GoString) (W64 0) c (by constructor <;> word))
                  as %re ⟨Hre, Hrecap, -⟩
                (try wp_auto)
                simp only [Hbnd, _root_.and_self, ↓reduceIte]
                (try wp_auto)
                wp_apply wp_load_slice_index csl (sint.Z n) _ DFrac.discard cp Hn $$ [] as -
                · iframe #; ipureintro; exact Hcp
                (try wp_auto)
                wp_apply wp_bytes_to_string $$ [HEs] as -
                · iexact HEs
                wp_apply wp_slice_literal (V := GoString) [e]
                isplitr
                · ipureintro; rfl
                iintro %s2 ⟨Hs2, -⟩
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hre $Hrecap $Hs2] as %re1 ⟨Hre, Hrecap, -⟩
                (try wp_auto)
                wp_for_post
                iframe
                iexists n + W64 1, c, ks1, re1, _
                iframe
                isplitl
                · iright; iexists _; iframe
                ipureintro; constructor <;> word
              · icases Hres with (%Hnil | ⟨%ress, Hre, Hrecap⟩)
                · exact absurd Hnil Hif
                · (try wp_auto)
                  simp only [Hbnd, _root_.and_self, ↓reduceIte]
                  (try wp_auto)
                  wp_apply wp_load_slice_index csl (sint.Z n) _ DFrac.discard cp Hn $$ [] as -
                  · iframe #; ipureintro; exact Hcp
                  (try wp_auto)
                  wp_apply wp_bytes_to_string $$ [HEs] as -
                  · iexact HEs
                  wp_apply wp_slice_literal (V := GoString) [e]
                  isplitr
                  · ipureintro; rfl
                  iintro %s2 ⟨Hs2, -⟩
                  (try wp_auto)
                  wp_apply wp_slice_append $$ [$Hre $Hrecap $Hs2] as %re1 ⟨Hre, Hrecap, -⟩
                  (try wp_auto)
                  wp_for_post
                  iframe
                  iexists n + W64 1, c, ks1, re1, _
                  iframe
                  isplitl
                  · iright; iexists _; iframe
                  ipureintro; constructor <;> word
            · (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, c, ks1, res, _
              iframe
              ipureintro; constructor <;> word
          · (try wp_auto)
            wp_apply hSs as %fks -
            wp_apply wp_slice_literal (V := zap.zapcore.Field) [fks]
            isplitr
            · ipureintro; rfl
            iintro %sfks ⟨Hsfks, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsfks] as %fslfks ⟨Hfsl, Hfcap, -⟩
            (try wp_auto)
            wp_if_destruct
            · wp_apply hSs as %fre -
              wp_apply wp_slice_literal (V := zap.zapcore.Field) [fre]
              isplitr
              · ipureintro; rfl
              iintro %sfre ⟨Hsfre, -⟩
              (try wp_auto)
              wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsfre] as %fslfre ⟨Hfsl, Hfcap, -⟩
              (try wp_auto)
              wp_if_destruct
              · wp_apply hI as %ftr -
                wp_apply wp_slice_literal (V := zap.zapcore.Field) [ftr]
                isplitr
                · ipureintro; rfl
                iintro %sftr ⟨Hsftr, -⟩
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsftr] as %fslftr ⟨Hfsl, Hfcap, -⟩
                (try wp_auto)
                wp_apply hInfo
                · ipureintro; exact Hlg
                iapply HΦ; itrivial
              · (try wp_auto)
                wp_apply hInfo
                · ipureintro; exact Hlg
                iapply HΦ; itrivial
            · (try wp_auto)
              wp_if_destruct
              · wp_apply hI as %ftr -
                wp_apply wp_slice_literal (V := zap.zapcore.Field) [ftr]
                isplitr
                · ipureintro; rfl
                iintro %sftr ⟨Hsftr, -⟩
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsftr] as %fslftr ⟨Hfsl, Hfcap, -⟩
                (try wp_auto)
                wp_apply hInfo
                · ipureintro; exact Hlg
                iapply HΦ; itrivial
              · (try wp_auto)
                wp_apply hInfo
                · ipureintro; exact Hlg
                iapply HΦ; itrivial
        · (try wp_auto)
          wp_apply hSs as %fks -
          wp_apply wp_slice_literal (V := zap.zapcore.Field) [fks]
          isplitr
          · ipureintro; rfl
          iintro %sfks ⟨Hsfks, -⟩
          (try wp_auto)
          wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsfks] as %fslfks ⟨Hfsl, Hfcap, -⟩
          (try wp_auto)
          wp_if_destruct
          · wp_apply hSs as %fre -
            wp_apply wp_slice_literal (V := zap.zapcore.Field) [fre]
            isplitr
            · ipureintro; rfl
            iintro %sfre ⟨Hsfre, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsfre] as %fslfre ⟨Hfsl, Hfcap, -⟩
            (try wp_auto)
            wp_if_destruct
            · wp_apply hI as %ftr -
              wp_apply wp_slice_literal (V := zap.zapcore.Field) [ftr]
              isplitr
              · ipureintro; rfl
              iintro %sftr ⟨Hsftr, -⟩
              (try wp_auto)
              wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsftr] as %fslftr ⟨Hfsl, Hfcap, -⟩
              (try wp_auto)
              wp_apply hInfo
              · ipureintro; exact Hlg
              iapply HΦ; itrivial
            · (try wp_auto)
              wp_apply hInfo
              · ipureintro; exact Hlg
              iapply HΦ; itrivial
          · (try wp_auto)
            wp_if_destruct
            · wp_apply hI as %ftr -
              wp_apply wp_slice_literal (V := zap.zapcore.Field) [ftr]
              isplitr
              · ipureintro; rfl
              iintro %sftr ⟨Hsftr, -⟩
              (try wp_auto)
              wp_apply wp_slice_append $$ [$Hfsl $Hfcap $Hsftr] as %fslftr ⟨Hfsl, Hfcap, -⟩
              (try wp_auto)
              wp_apply hInfo
              · ipureintro; exact Hlg
              iapply HΦ; itrivial
            · (try wp_auto)
              wp_apply hInfo
              · ipureintro; exact Hlg
              iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply hInfo
      · ipureintro; exact Hlg
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
