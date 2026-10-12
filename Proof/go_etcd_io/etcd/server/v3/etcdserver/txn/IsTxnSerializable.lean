/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnSerializable
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequestRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.IsTxnSerializable_opsIs_length :
    ∀ (ps : List Loc) (ops : List TxnOp),
      txn.requestOpsIs (GF := GF) ps ops ⊢ ⌜ps.length = ops.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | p :: ps, op :: ops => by
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    ihave %h := txn.IsTxnSerializable_opsIs_length ps ops $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H

theorem txn.IsTxnSerializable_opsIs_lookup :
    ∀ (ps : List Loc) (ops : List TxnOp) (i : Nat) (p : Loc), ps[i]? = some p →
      txn.requestOpsIs (GF := GF) ps ops ⊢ ∃ op, ⌜ops[i]? = some op⌝ ∗ txn.requestOpIs p op
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | q :: ps, op :: ops, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    unfold txn.requestOpsIs
    iintro ⟨H, -⟩
    iexists op
    iframe H
    ipureintro; rfl
  | q :: ps, op :: ops, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    simp only [List.getElem?_cons_succ]
    iapply txn.IsTxnSerializable_opsIs_lookup ps ops i p h $$ H

theorem txn.IsTxnSerializable_false (t : TxnModel) (op : TxnOp) (h : op ∈ t.thenOps ++ t.elseOps)
    (hg : txn.opIsSerGet op = false) : txn.txnSerializable t = false := by
  unfold txn.txnSerializable
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  rw [hall op h] at hg
  cases hg

theorem txn.IsTxnSerializable_true (t : TxnModel)
    (h1 : ∀ j < t.thenOps.length, ∀ op, t.thenOps[j]? = some op → txn.opIsSerGet op = true)
    (h2 : ∀ j < t.elseOps.length, ∀ op, t.elseOps[j]? = some op → txn.opIsSerGet op = true) :
    txn.txnSerializable t = true := by
  unfold txn.txnSerializable
  rw [List.all_eq_true]
  intro op hop
  rcases List.mem_append.1 hop with h | h
  · obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem h
    exact h1 j hj op (by rw [List.getElem?_eq_getElem hj, hjo])
  · obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem h
    exact h2 j hj op (by rw [List.getElem?_eq_getElem hj, hjo])

theorem txn.IsTxnSerializable.wp_proof
    (hGet : RequestOp.GetRequestRange.spec (GF := GF) (hG := hG)) :
    txn.IsTxnSerializable.spec (GF := GF) (hG := hG) := by
  intro rt t
  wp_start as #Ht
  iunfold txn.txnRequestIs at Ht
  icases Ht with ⟨%Hnn, Hf⟩
  iunfold txn.txnFieldsIs at Hf
  icases Hf with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hfl, #Hfs, #Hfm⟩
  ihave %Hsl := txn.IsTxnSerializable_opsIs_length sps t.thenOps $$ Hsm
  ihave %Hfll := txn.IsTxnSerializable_opsIs_length fps t.elseOps $$ Hfm
  ihave %Hslen := ownSlice_len _ _ _ $$ Hss
  ihave %Hflen := ownSlice_len _ _ _ $$ Hfs
  wp_auto
  ihave IH : (∃ (n : w64) (uv : Loc), "i" ∷ i_ptr ↦ n ∗ "u" ∷ u_ptr ↦ uv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z ssl.len ∧
        ∀ j < sint.nat n, ∀ op, t.thenOps[j]? = some op → txn.opIsSerGet op = true⌝ : IProp GF) $$ [i u]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hn0, hnl, hall⟩ := Hn
    have hlt : sint.nat n < sps.length := by have := Hslen.1; word
    list_elem sps (sint.nat n) as p
    simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z ssl.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index ssl (sint.Z n) sps DFrac.discard p hn0 $$ [Hss] as -
    · iframe Hss; ipureintro; exact Hp_lookup
    ihave ⟨%op, %Hop, #Hp⟩ := txn.IsTxnSerializable_opsIs_lookup sps t.thenOps (sint.nat n) p Hp_lookup $$ Hsm
    wp_apply (hGet p op) $$ [$Hp] as %rr Hrr
    cases hg : txn.opIsSerGet op
    · cases op
      case get o =>
        iunfold txn.rangeRequestIs at Hrr
        icases Hrr with ⟨%Hrn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM,
          %maxM, %minC, %maxC, -, -, -, -, -, -, -, -, #Hser, -, -, -, -, -, -, %Ho⟩
        have hser : ser = false := by subst Ho; simpa [txn.opIsSerGet, txn.rangeOpOf] using hg
        subst hser
        rw [decide_eq_false Hrn]
        wp_auto
        wp_for_post
        rw [txn.IsTxnSerializable_false t _ (List.mem_append_left _ (List.mem_of_getElem? Hop)) hg]
        iapply HΦ; itrivial
      all_goals
        icases Hrr with %Hrn
        subst Hrn
        wp_auto
        wp_for_post
        rw [txn.IsTxnSerializable_false t _ (List.mem_append_left _ (List.mem_of_getElem? Hop)) hg]
        iapply HΦ; itrivial
    · obtain ⟨o, rfl⟩ : ∃ o, op = .get o := by cases op <;> simp_all [txn.opIsSerGet]
      iunfold txn.rangeRequestIs at Hrr
      icases Hrr with ⟨%Hrn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM,
        %maxM, %minC, %maxC, -, -, -, -, -, -, -, -, #Hser, -, -, -, -, -, -, %Ho⟩
      have hser : ser = true := by subst Ho; simpa [txn.opIsSerGet, txn.rangeOpOf] using hg
      subst hser
      rw [decide_eq_false Hrn]
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj op' hop'
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hsn] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hall j hj op' hop'
      · subst hj; rw [Hop] at hop'; cases hop'; exact hg
  obtain ⟨hn0, hnl, hall⟩ := Hn
  have hnend : sint.nat n = t.thenOps.length := by have := Hslen.1; word
  ihave IH : (∃ (n : w64) (uv : Loc), "i" ∷ i_ptr ↦ n ∗ "u" ∷ u_ptr ↦ uv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z fsl.len ∧
        ∀ j < sint.nat n, ∀ op, t.elseOps[j]? = some op → txn.opIsSerGet op = true⌝ : IProp GF) $$ [i u]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
  have hthen : ∀ j < t.thenOps.length, ∀ op, t.thenOps[j]? = some op → txn.opIsSerGet op = true := by
    intro j hj; exact hall j (by omega)
  clear hall hnend hn0 hnl Hif
  wp_for IH
  wp_if_destruct
  · obtain ⟨hn0, hnl, hall⟩ := Hn
    have hlt : sint.nat n < fps.length := by have := Hflen.1; word
    list_elem fps (sint.nat n) as p
    simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z fsl.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index fsl (sint.Z n) fps DFrac.discard p hn0 $$ [Hfs] as -
    · iframe Hfs; ipureintro; exact Hp_lookup
    ihave ⟨%op, %Hop, #Hp⟩ := txn.IsTxnSerializable_opsIs_lookup fps t.elseOps (sint.nat n) p Hp_lookup $$ Hfm
    wp_apply (hGet p op) $$ [$Hp] as %rr Hrr
    cases hg : txn.opIsSerGet op
    · cases op
      case get o =>
        iunfold txn.rangeRequestIs at Hrr
        icases Hrr with ⟨%Hrn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM,
          %maxM, %minC, %maxC, -, -, -, -, -, -, -, -, #Hser, -, -, -, -, -, -, %Ho⟩
        have hser : ser = false := by subst Ho; simpa [txn.opIsSerGet, txn.rangeOpOf] using hg
        subst hser
        rw [decide_eq_false Hrn]
        wp_auto
        wp_for_post
        rw [txn.IsTxnSerializable_false t _ (List.mem_append_right _ (List.mem_of_getElem? Hop)) hg]
        iapply HΦ; itrivial
      all_goals
        icases Hrr with %Hrn
        subst Hrn
        wp_auto
        wp_for_post
        rw [txn.IsTxnSerializable_false t _ (List.mem_append_right _ (List.mem_of_getElem? Hop)) hg]
        iapply HΦ; itrivial
    · obtain ⟨o, rfl⟩ : ∃ o, op = .get o := by cases op <;> simp_all [txn.opIsSerGet]
      iunfold txn.rangeRequestIs at Hrr
      icases Hrr with ⟨%Hrn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM,
        %maxM, %minC, %maxC, -, -, -, -, -, -, -, -, #Hser, -, -, -, -, -, -, %Ho⟩
      have hser : ser = true := by subst Ho; simpa [txn.opIsSerGet, txn.rangeOpOf] using hg
      subst hser
      rw [decide_eq_false Hrn]
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj op' hop'
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hsn] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hall j hj op' hop'
      · subst hj; rw [Hop] at hop'; cases hop'; exact hg
  obtain ⟨hn0, hnl, hall⟩ := Hn
  have hnend : sint.nat n = t.elseOps.length := by have := Hflen.1; word
  rw [txn.IsTxnSerializable_true t hthen (fun j hj => hall j (by omega))]
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
