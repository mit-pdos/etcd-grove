/-
Lean-first (no Rocq counterpart).

The proof of `kvsFrom`: the loop appends each key-value's `KV`; its invariant, the prefix so far.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.kvsFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrOf
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem kvsFrom.wp_proof (wp_vrOf : vrOf.spec (GF := GF) (hG := hG)) :
    kvsFrom.spec (GF := GF) (hG := hG) := by
  intro sl ps kvs
  wp_start as ⟨#Hsl, #Hkvs⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  ihave %Hl := ownSlice_len $$ Hsl
  wp_auto
  wp_apply wp_slice_make3 (V := KV) (W64 0) sl.len ⟨by word, by word⟩ as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (k1 : Loc) (os : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "kv" ∷ kv_ptr ↦ k1 ∗ "out" ∷ out_ptr ↦ os ∗
      "Hos" ∷ os ↦* ((kvs.take (sint.nat j)).map fun kv => (⟨kv.key, kvVR kv⟩ : KV)) ∗
      "Hoscap" ∷ ownSliceCap KV os (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF)
    $$ [i kv out Ho Hocap]
  · iexists W64 0, _, o0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
    iframe
    ipureintro; word
  wp_for HI
  by_cases Hif : sint.Z j < sint.Z sl.len
  · (try simp only [decide_eq_true Hif]); wp_pures; cleanup_bool_decide
    (try wp_auto); cleanup_bool_decide
    list_elem ps (sint.nat j) as p
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p Hj.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp_lookup
    obtain ⟨v, Hv⟩ : ∃ v, kvs[sint.nat j]? = some v := by
      have : sint.nat j < kvs.length := by rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 Hp_lookup).1
      exact ⟨kvs[sint.nat j], List.getElem?_eq_getElem this⟩
    ihave #Hkv := Hall $$ %(sint.nat j) %p %v %Hp_lookup %Hv
    iunfold txn.kvIs at Hkv
    icases Hkv with ⟨%kSl, %vSl, #HkF, #HkS, -, #HmF, #HvF, #HvalF, #HvS, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string kSl v.key DFrac.discard $$ [HkS] as -
    · iframe #
    (try wp_auto)
    wp_apply wp_vrOf vSl v.value DFrac.discard v.modRev v.version $$ [HvS] as -
    · iframe #
    (try wp_auto)
    wp_apply wp_slice_literal (l := [(⟨v.key, ⟨v.value, v.modRev, v.version⟩⟩ : KV)])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl1, _⟩
    wp_apply wp_slice_append $$ [$Hos $Hoscap $Hl1] as %os' ⟨Hos, Hoscap, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, _, os'
    have Htk : (kvs.take (sint.nat (j + W64 1))).map (fun kv => (⟨kv.key, kvVR kv⟩ : KV)) =
        (kvs.take (sint.nat j)).map (fun kv => (⟨kv.key, kvVR kv⟩ : KV)) ++
          [(⟨v.key, ⟨v.value, v.modRev, v.version⟩⟩ : KV)] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hv]
      simp [kvVR]
    rw [Htk]
    iframe
    ipureintro; word
  · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
    cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
    have hall : kvs.take (sint.nat j) = kvs := List.take_of_length_le (by rw [← Hlen, Hl.1]; word)
    rw [hall]
    iapply HΦ
    iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
