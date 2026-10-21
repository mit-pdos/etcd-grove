/-
Lean-first (no Rocq counterpart).

The proof of `runOps`: the loop's invariant is `runStep`'s fold over the operations before the
index (the store, the results and the changed flag); the store's length grows by at most one per
operation.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.runOps
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.put
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.delKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem setR_length (k : GoString) (r : VR) :
    ∀ es : List entry, (setR k r es).length ≤ es.length + 1
  | [] => by simp [setR]
  | e :: es => by
    simp only [setR]
    split
    · split <;> simp
    · have := setR_length k r es; simp only [List.length_cons]; omega

theorem putL_length (es : List entry) (r : w64) (k v : GoString) :
    (putL es r k v).length ≤ es.length + 1 := by
  unfold putL; rw [setKeyL_eq]; exact setR_length _ _ es

theorem runStep_length (r : w64) (acc : List entry × List TRes × Bool) (op : TOp) :
    (runStep r acc op).1.length ≤ acc.1.length + 1 := by
  unfold runStep
  split
  · simp
  · split
    · exact putL_length _ _ _ _
    · split
      · have := List.length_filter_le (fun e : entry => !decide (e.key' = op.Key')) acc.1
        unfold delKeyL; simp only; omega
      · simp

theorem foldl_runStep_length (r : w64) :
    ∀ (ops : List TOp) (acc : List entry × List TRes × Bool),
      (ops.foldl (runStep r) acc).1.length ≤ acc.1.length + ops.length
  | [], acc => by simp
  | op :: ops, acc => by
    have h1 := foldl_runStep_length r ops (runStep r acc op)
    have h2 := runStep_length r acc op
    simp only [List.foldl_cons, List.length_cons]; omega

theorem runOps.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_put : put.spec (GF := GF) (hG := hG)) (wp_delKey : delKey.spec (GF := GF) (hG := hG)) :
    runOps.spec (GF := GF) (hG := hG) := by
  intro sl es r osl ops dq
  wp_start as ⟨#Hs, Hops, %Hb⟩
  ihave %Hl := ownSlice_len $$ Hops
  wp_auto
  wp_apply wp_slice_make3 (V := TRes) (W64 0) osl.len ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (o1 : TOp) (ks rs : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ o1 ∗ "kvs" ∷ kvs_ptr ↦ ks ∗ "res" ∷ res_ptr ↦ rs ∗
      "changed" ∷ changed_ptr ↦ ((ops.take (sint.nat j)).foldl (runStep r) (es, [], false)).2.2 ∗
      "#Hks" ∷ ks ↦*□ ((ops.take (sint.nat j)).foldl (runStep r) (es, [], false)).1 ∗
      "Hrs" ∷ rs ↦* ((ops.take (sint.nat j)).foldl (runStep r) (es, [], false)).2.1 ∗
      "Hrscap" ∷ ownSliceCap TRes rs (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ : IProp GF)
    $$ [i op kvs res changed Ho Hocap]
  · iexists W64 0, _, sl, o0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    dsimp only
    iframe
    isplit
    · iexact Hs
    · ipureintro; word
  wp_for HI
  by_cases Hif : sint.Z j < sint.Z osl.len
  · (try simp only [decide_eq_true Hif, ↓reduceIte]); wp_pures; cleanup_bool_decide
    (try wp_auto); cleanup_bool_decide
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ops (sint.nat j) as x
    wp_apply wp_load_slice_index osl (sint.Z j) ops dq x Hj.1 $$ [Hops] as Hops
    · iframe; ipureintro; exact Hx_lookup
    have Htake : (ops.take (sint.nat (j + W64 1))).foldl (runStep r) (es, [], false) =
        runStep r ((ops.take (sint.nat j)).foldl (runStep r) (es, [], false)) x := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      simp
    have Hlen : ((ops.take (sint.nat j)).foldl (runStep r) (es, [], false)).1.length + 1 <
        2 ^ 63 := by
      have h1 := foldl_runStep_length r (ops.take (sint.nat j)) (es, [], false)
      have h2 : (ops.take (sint.nat j)).length ≤ ops.length := by rw [List.length_take]; omega
      simp only at h1; omega
    generalize (ops.take (sint.nat j)).foldl (runStep r) (es, [], false) = acc at Htake Hlen ⊢
    obtain ⟨k1, rs1, ch1⟩ := acc
    simp only at Htake Hlen ⊢
    wp_if_destruct
    · -- a get
      wp_apply wp_lookup ks k1 DFrac.discard x.Key' $$ [$Hks] as %v %ok ⟨-, %Hlk⟩
      wp_apply wp_slice_literal (l := [(⟨W64 0, ok, v, W64 0⟩ : TRes)])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Hrs $Hrscap $Hl1] as %rs' ⟨Hrs, Hrscap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, _, ks, rs'
      rw [Htake, runStep, if_pos Hif, ← Hlk]
      iframe
      isplit
      · iexact Hks
      · ipureintro; word
    · have H0 := Hif; clear Hif
      wp_if_destruct
      · -- a put
        wp_apply wp_put ks k1 DFrac.discard r x.Key' x.Val' $$ [$Hks] as %nk ⟨-, Hnk, -⟩
        · ipureintro; exact Hlen
        ipersist Hnk
        wp_apply wp_slice_literal (l := [(⟨W64 1, false, zVR, W64 0⟩ : TRes)])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Hrs $Hrscap $Hl1] as %rs' ⟨Hrs, Hrscap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, _, nk, rs'
        rw [Htake, runStep, if_neg H0, if_pos Hif]
        iframe
        isplit
        · iexact Hnk
        · ipureintro; word
      · -- a delete
        have H1 := Hif; clear Hif
        wp_apply wp_lookup ks k1 DFrac.discard x.Key' $$ [$Hks] as %v %ok ⟨-, %Hlk⟩
        wp_if_destruct
        · wp_apply wp_slice_literal (l := [(⟨W64 2, false, zVR, W64 0⟩ : TRes)])
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hl1, _⟩
          wp_apply wp_slice_append $$ [$Hrs $Hrscap $Hl1] as %rs' ⟨Hrs, Hrscap, -⟩
          wp_for_post
          iframe
          iexists j + W64 1, _, ks, rs'
          rw [Htake, runStep, if_neg H0, if_neg H1, if_neg (by rw [← Hlk]; simp)]
          iframe
          isplit
          · iexact Hks
          · ipureintro; word
        · wp_apply wp_delKey ks k1 DFrac.discard x.Key' $$ [$Hks] as %nk ⟨-, Hnk, -⟩
          ipersist Hnk
          wp_apply wp_slice_literal (l := [(⟨W64 2, false, zVR, W64 1⟩ : TRes)])
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hl1, _⟩
          wp_apply wp_slice_append $$ [$Hrs $Hrscap $Hl1] as %rs' ⟨Hrs, Hrscap, -⟩
          wp_for_post
          iframe
          iexists j + W64 1, _, nk, rs'
          rw [Htake, runStep, if_neg H0, if_neg H1, if_pos (by rw [← Hlk])]
          iframe
          isplit
          · iexact Hnk
          · ipureintro; word
  · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
    cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
    have hall : ops.take (sint.nat j) = ops := List.take_of_length_le (by word)
    rw [hall]
    unfold runOpsL
    iapply HΦ
    iframe
    isplit
    · iexact Hks
    · ipureintro; rfl

end proof

end linkvtxn
end EtcdGrove
end Perennial
