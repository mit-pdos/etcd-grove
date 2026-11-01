/-
Proof of `Spec/go_etcd_io/etcd/client/v3/txn__Then.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.txn__Then
public import Spec.go_etcd_io.etcd.client.v3.Op__isWrite
public import Spec.go_etcd_io.etcd.client.v3.Op__toRequestOp
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option hygiene false in
/-- The rest of an iteration of `Then`'s loop, after `isWrite`. -/
local macro "then_tail" : tactic => `(tactic| (
    (try wp_method_call)
    (try wp_method_call)
    wp_auto
    wp_apply wp_toRequestOp v t $$ [] as %p #Hp
    · iframe #; ipureintro; exact OpT.txnOp_leaves t op Hto
    wp_apply wp_slice_literal (V := Loc) [p]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [Hssl Hscap Hsl2] as %sl' ⟨Hssl, Hscap, -⟩
    · iframe
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, v, _, sl', sps' ++ [p]
    simp only [named]
    iframe
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hopi]
      simp only [Option.toList_some, ← List.append_assoc, List.map_append, List.map_cons,
        List.map_nil]
      iapply reqOpsAt_snoc
      iframe #
      rw [← OpT.wire_txnOp t op Hto]
      iexact Hp
    ipureintro; constructor <;> word))

theorem txn.Then.wp_proof (wp_isWrite : Op.isWrite.spec (GF := GF) (hG := hG))
    (wp_toRequestOp : Op.toRequestOp.spec (GF := GF) (hG := hG)) :
    txn.Then.spec (GF := GF) (hG := hG) := by
  intro tp addr ci cd b sl ts ops
  wp_start as ⟨Htx, #Hos, %Hb⟩
  obtain ⟨Hops, hthen, helse⟩ := Hb
  iunfold txnObjAt at Htx
  icases Htx with ⟨%Htpn, %api, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, #Hkv, #Hctxf,
    #Hctx, #Hce, #Hmu, Hcif, Hcthen, Hcelse, Hiw, Hcmps, Hcsl, Hccap, #Hcpa, Hsus, Hssl, Hscap,
    #Hspa, Hfas, Hfsl, Hfcap, #Hfpa, #Hcof, #Hco⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  rw [hthen]
  wp_auto
  rw [helse]
  wp_auto
  iunfold opsTAt at Hos
  icases Hos with ⟨%vs, #Hvss, #Hvsa⟩
  ihave %Hvl := opListAtC_length false vs ts $$ Hvsa
  ihave %Hsll := ownSlice_len $$ Hvss
  have Hopl : ops.length = ts.length := OpT.txnOps_length ts ops Hops
  ihave IH : iprop(∃ (n : w64) (ov : go_etcd_io.etcd.client.v3.Op) (iw' : Bool) (ssl' : GoSlice)
      (sps' : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ ov ∗ "Hiw" ∷
        structFieldRef go_etcd_io.etcd.client.v3.txn go!"isWrite" tp ↦ iw' ∗
      "Hsus" ∷ structFieldRef go_etcd_io.etcd.client.v3.txn go!"sus" tp ↦ ssl' ∗
      "Hssl" ∷ ssl' ↦* sps' ∗ "Hscap" ∷ ownSliceCap Loc ssl' (DFrac.own 1) ∗
      "#Hspa" ∷ reqOpsAt sps' ((b.model.thenOps ++ ops.take (sint.nat n)).map opWire) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op Hiw Hsus Hssl Hscap]
  · iexists W64 0, _, iw, ssl, sps
    simp only [named]
    iframe
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
    iframe #
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨t, Hti⟩ : ∃ t, ts[sint.nat n]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hvl]; exact Hlt)⟩
    obtain ⟨op, Hto, Hopi⟩ := OpT.txnOps_getElem ts ops _ t Hops Hti
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    icases ownSlice_elem_acc (sint.Z n) v sl DFrac.discard vs Hn.1 Hvi $$ Hvss
      with ⟨#Hve0, -⟩
    ihave ⟨#Hvo, -⟩ := opListAtC_get false vs ts _ v t Hvi Hti $$ Hvsa
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_auto
    cases iw'
    · wp_auto
      wp_method_call
      wp_method_call
      wp_auto
      wp_apply wp_isWrite v t $$ []
      · iframe #
      then_tail
    · wp_auto
      then_tail

  · have Hge : sint.nat n = ops.length := by rw [Hopl, ← Hvl]; word
    rw [show ops.take (sint.nat n) = ops by rw [Hge, List.take_length]]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    unfold txnObjAt
    isplitl []
    · ipureintro; exact Htpn
    iexists api, cosl, csl, ssl', fsl, cps, sps', fps, iw'
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
