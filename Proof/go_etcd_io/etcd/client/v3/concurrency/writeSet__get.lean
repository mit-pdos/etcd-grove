/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/writeSet__get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__get
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMMaps

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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem writeSet.get.wp_proof : writeSet.get.spec (GF := GF) (hG := hG) := by
  intro m dq pfx wsMap writes ksl ks
  wp_start as ⟨Hm, #Hws, #Hks⟩
  wp_auto
  ihave %Hksl := ownSlice_len _ _ _ $$ Hks
  ihave HI : (∃ (j : w64) (kx : GoString),
      "i" ∷ i_ptr ↦ j ∗ "key" ∷ key_ptr ↦ kx ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ksl.len ∧
        ∀ k ∈ ks.take (sint.nat j), writes !! k = none⌝ : IProp GF) $$ [i key]
  · iexists W64 0, _
    simp only [named]
    iframe i key
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    intro k hk; cases hk
  wp_for HI
  wp_if_destruct
  · have hj : sint.nat j < ks.length := by
      rw [Hksl.1]; have := Hj.1; simp only [sint.nat, sint.Z] at *; omega
    list_elem ks (sint.nat j) as k
    rw [ite_eq_left ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index ksl (sint.Z j) ks DFrac.discard k Hj.1 $$ [] as -
    · iframe #; ipureintro; exact Hk_lookup
    wp_apply wp_map_lookup2 $$ Hm as Hm
    ihave #Hws' := Hws
    unfold writesAt
    icases Hws' with ⟨%Hdom, #Hall⟩
    cases Hsp : wsMap !! k with
    | some sp =>
      obtain ⟨w, Hw⟩ : ∃ w, writes !! k = some w := by
        have h := Hdom k
        rw [Hsp] at h
        exact Option.isSome_iff_exists.1 (by simpa using h.symm)
      ihave #Hwa := Hall $$ %k %sp %w %Hsp %Hw
      unfold writeAt
      icases Hwa with ⟨%Hval, -⟩
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe Hm
      iright
      iexists k, w, sp
      iframe wv
      ipureintro
      exact ⟨List.mem_of_getElem? Hk_lookup, Hw, Hval.1⟩
    | none =>
      have Hwn : writes !! k = none := by
        have h := Hdom k
        rw [Hsp] at h
        cases hw : writes !! k <;> simp_all
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, k
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have hsucc : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [hsucc, List.take_add_one, Hk_lookup]
      intro k' hk'
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hk'
      rcases hk' with hk' | rfl
      · exact Hj.2.2 k' hk'
      · exact Hwn
  have hlen : sint.nat j = ks.length := by
    rw [Hksl.1]; have := Hj.1; have := Hj.2.1; simp only [sint.nat, sint.Z] at *; omega
  have Hnone := Hj.2.2
  rw [hlen, List.take_length] at Hnone
  iapply HΦ
  iframe Hm
  ileft
  ipureintro
  exact ⟨rfl, Hnone⟩

end proof

end concurrency
end EtcdGrove
end Perennial
