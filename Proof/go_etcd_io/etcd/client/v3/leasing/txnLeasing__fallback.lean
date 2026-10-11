/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__fallback.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__fallback
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-- The get of a lease range `OpGet(lkey, WithRange(lend))` is one a transaction can run. -/
theorem fallback_getOp (lkey lend : GoString) :
    txnOpOf (opGetModel lkey [withRangeM lend]) = some (.get (opGetModel lkey [withRangeM lend])) ∧
      ¬ opGetPanics [withRangeM lend] := by
  constructor
  · simp [opGetModel, opFold, withRangeM, OpFull.getInit, OpFull.newOp, OpModel.zero, txnOpOf]
  · simp [opGetPanics, opFold, withRangeM, OpFull.newOp]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.fallback.wp_proof
    (hIsGet : EtcdGrove.Op.IsGet.spec (GF := GF) (hG := hG))
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hWR : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG)) :
    txnLeasing.fallback.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx dq sl os
  wp_start as ⟨Hlkvf, #HLKV, #Hops⟩
  ihave #HLKV' := HLKV
  unfold isLeasingKV
  icases HLKV' with ⟨%cl, %kv, %ctx, %cs, %cancel, %osl, %Hpfx, -, -, #Hpfxf, -⟩
  ihave #Hops' := (opsAt_listRel sl os).1 $$ Hops
  icases Hops' with ⟨%vs, #Hvs, #Hrel⟩
  ihave #Hrel' := Hrel
  unfold listRel
  icases Hrel' with ⟨%Hlen, #Hv⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (fsl : GoSlice)
      (fvs : List go_etcd_io.etcd.client.v3.Op) (fos : List OpFull),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "fb" ∷ fbOps_ptr ↦ fsl ∗ "#Hfsl" ∷ fsl ↦*□ fvs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Op fsl (DFrac.own 1) ∗
      "#Hrelf" ∷ listRel opFullAt fvs fos ∗
      "%Hfos" ∷ ⌜∀ o ∈ fos, txnOpOf o = some (.get o)⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op fbOps]
  · iexists W64 0, _, slice.nil, [], []
    simp only [named]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply listRel_nil
    ipureintro; constructor
    · intro o ho; simp at ho
    · constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Hoi⟩ : ∃ o, os[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) vs DFrac.discard v Hn.1 $$ [Hvs] as -
    · iframe #; ipureintro; exact Hvi
    ihave #Hat := Hv $$ %(sint.nat n) %v %o %Hvi %Hoi
    wp_apply hIsGet $$ [$op $Hat] as op
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (n + W64 1), v, fsl, fvs, fos
      simp only [named]
      iframe
      iframe #
      ipureintro; exact ⟨Hfos, by constructor <;> word⟩
    · wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
      wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
      ihave #Hat' := Hat
      iunfold opFullAt at Hat'
      icases Hat' with ⟨#Hbase, -⟩
      wp_apply hRange $$ [$op $Hbase] as %esl ⟨op, #He⟩
      ihave %Hel := ownSlice_len _ _ _ $$ He
      wp_join iprop(∃ lend : GoString, lend_ptr ↦ lend ∗ op_ptr ↦ v ∗ txn_ptr ↦ txn ∗
          structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv) with [op lend txn Hlkvf]
        as ⟨%lend, lend, op, txn, Hlkvf⟩
      · (try wp_auto)
        wp_apply hRange $$ [$op $Hbase] as %esl2 ⟨op, #He2⟩
        wp_apply wp_bytes_to_string esl2 o.base.rangeEnd DFrac.discard $$ [$He2] as -
        (try wp_auto)
        wp_join_done
      (try wp_auto)
      wp_apply hWR $$ [$Hcv] as %f #Hf
      wp_apply wp_slice_literal (l := [f])
      isplitr
      · ipureintro; rfl
      iintro %osl1 ⟨Hosl1, -⟩
      ipersist Hosl1
      ihave #Hopts : optsAt (GF := GF) _ [withRangeM lend] $$ []
      · unfold optsAt
        iexists [f]
        iframe Hosl1
        isplitr
        · ipureintro; rfl
        imodintro
        iintro %i %f' %g %Hf' %Hg
        rcases i with _ | i
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg; subst Hf' Hg; iexact Hf
        · simp at Hf'
      (try wp_auto)
      wp_apply hGet $$ [$Hcv $Hopts] as %gop #Hgop
      · ipureintro; exact (fallback_getOp (pfx ++ o.key) lend).2
      wp_apply wp_slice_literal (l := [gop])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append_persistent fsl fvs _ [gop] (DFrac.own 1)) $$ [$Hfsl $Hcap $Hz]
        as %fsl' ⟨#Hfsl', Hcap, -⟩
      wp_for_post
      iframe
      iexists (n + W64 1), v, fsl', fvs ++ [gop], fos ++ [opGetModel (pfx ++ o.key) [withRangeM lend]]
      simp only [named]
      iframe
      iframe Hfsl'
      isplitr
      · iapply listRel_app
        iframe #
        iapply listRel_single
        iexact Hgop
      ipureintro
      refine ⟨?_, by constructor <;> word⟩
      intro o' ho'
      rcases List.mem_append.1 ho' with h | h
      · exact Hfos o' h
      · simp only [List.mem_singleton] at h; subst h; exact (fallback_getOp _ lend).1
  · (try wp_auto)
    iapply HΦ
    iframe
    iexists fos
    isplitl
    · iapply (opsAt_listRel _ _).2
      iexists fvs
      iframe #
    ipureintro; exact Hfos

end proof

end leasing
end EtcdGrove
end Perennial
