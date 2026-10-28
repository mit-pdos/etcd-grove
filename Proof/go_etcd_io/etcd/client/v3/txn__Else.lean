/-
Proof of `Spec/go_etcd_io/etcd/client/v3/txn__Else.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.txn__Else
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
/-- The rest of an iteration of `Else`'s loop, after `isWrite`. -/
local macro "else_tail" : tactic => `(tactic| (
    (try wp_method_call)
    (try wp_method_call)
    wp_auto
    wp_apply wp_toRequestOp v o $$ [] as %p #Hp
    · iframe #; ipureintro; exact Ht123
    wp_apply wp_slice_literal (V := Loc) [p]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [Hfsl Hfcap Hsl2] as %sl' ⟨Hfsl, Hfcap, -⟩
    · iframe
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, v, _, sl', fps' ++ [p]
    simp only [named]
    iframe
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hopi]
      simp only [Option.toList_some, ← List.append_assoc, List.map_append, List.map_cons,
        List.map_nil]
      iapply reqOpsAt_snoc
      iframe #
      rw [← leafWire_txnOpOf o op Hto]
      iexact Hp
    ipureintro; constructor <;> word))

theorem txn.Else.wp_proof (wp_isWrite : Op.isWrite.spec (GF := GF) (hG := hG))
    (wp_toRequestOp : Op.toRequestOp.spec (GF := GF) (hG := hG)) :
    txn.Else.spec (GF := GF) (hG := hG) := by
  intro tp addr ci cd b sl os ops
  wp_start as ⟨Htx, #Hos, %Hb⟩
  obtain ⟨Hops, helse⟩ := Hb
  iunfold txnObjAt at Htx
  icases Htx with ⟨%Htpn, %api, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, #Hkv, #Hctxf,
    #Hctx, #Hce, #Hmu, Hcif, Hcthen, Hcelse, Hiw, Hcmps, Hcsl, Hccap, #Hcpa, Hsus, Hssl, Hscap,
    #Hspa, Hfas, Hfsl, Hfcap, #Hfpa, #Hcof, #Hco⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  rw [helse]
  wp_auto
  iunfold opsAt at Hos
  icases Hos with ⟨%vs, #Hvss, %Hvl, #Hvsa⟩
  ihave %Hsll := ownSlice_len $$ Hvss
  have Hopl : ops.length = os.length := by
    have := congrArg List.length Hops; simp at this; omega
  ihave IH : iprop(∃ (n : w64) (ov : go_etcd_io.etcd.client.v3.Op) (iw' : Bool) (fsl' : GoSlice)
      (fps' : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ ov ∗ "Hiw" ∷
        structFieldRef go_etcd_io.etcd.client.v3.txn go!"isWrite" tp ↦ iw' ∗
      "Hfas" ∷ structFieldRef go_etcd_io.etcd.client.v3.txn go!"fas" tp ↦ fsl' ∗
      "Hfsl" ∷ fsl' ↦* fps' ∗ "Hfcap" ∷ ownSliceCap Loc fsl' (DFrac.own 1) ∗
      "#Hfpa" ∷ reqOpsAt fps' ((b.model.elseOps ++ ops.take (sint.nat n)).map opWire) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op Hiw Hfas Hfsl Hfcap]
  · iexists W64 0, _, iw, fsl, fps
    simp only [named]
    iframe
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
    iframe #
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Hoi⟩ : ∃ o, os[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hvl]; exact Hlt)⟩
    obtain ⟨op, Hopi⟩ : ∃ op, ops[sint.nat n]? = some op :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hopl, ← Hvl]; exact Hlt)⟩
    have Hto : txnOpOf o = some op := by
      have h1 := congrArg (fun l => l[sint.nat n]?) Hops
      simp only [List.getElem?_map, Hoi, Hopi, Option.map_some] at h1
      exact Option.some.inj h1
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    icases ownSlice_elem_acc (sint.Z n) v sl DFrac.discard vs Hn.1 Hvi $$ Hvss
      with ⟨#Hve0, -⟩
    ihave #Hvo := Hvsa $$ %(sint.nat n) %v %o %Hvi %Hoi
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_auto
    have Ht4 : o.t ≠ W64 4 := txnOpOf_t Hto
    have Ht123 : o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3 := by
      unfold txnOpOf at Hto
      by_cases h1 : o.t = W64 1
      · exact Or.inl h1
      · by_cases h2 : o.t = W64 2
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : o.t = W64 3
          · exact Or.inr (Or.inr h3)
          · rw [if_neg h1, if_neg h2, if_neg h3] at Hto; cases Hto
    cases iw'
    · wp_auto
      wp_method_call
      wp_method_call
      wp_auto
      wp_apply wp_isWrite v o $$ []
      · iframe #; ipureintro; exact Ht4
      else_tail
    · wp_auto
      else_tail

  · have Hge : sint.nat n = ops.length := by rw [Hopl, ← Hvl]; word
    rw [show ops.take (sint.nat n) = ops by rw [Hge, List.take_length]]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    unfold txnObjAt
    isplitl []
    · ipureintro; exact Htpn
    iexists api, cosl, csl, ssl, fsl', cps, sps, fps', iw'
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
