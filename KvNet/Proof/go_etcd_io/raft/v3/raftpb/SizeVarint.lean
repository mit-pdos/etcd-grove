-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/SizeVarint.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`sizeVarint` (`raftpb/noax.go`): the Go loop computes the model's `varintSize` (`UfWire.lean`).
The part's own (raft without hand-written axioms, `notes/raft-noax-part.md`, "Stage 3a"); a helper
of `EntrySize`'s proof, outside the spec/proof discipline (an unexported function).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.EntrySize

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure

theorem varintSize_lt128 (n : Nat) (h : n < 128) : varintSize n = 1 := by
  unfold varintSize
  rw [varintEnc]
  simp [h]

theorem varintSize_ge128 (n : Nat) (h : 128 ≤ n) : varintSize n = 1 + varintSize (n / 128) := by
  unfold varintSize
  rw [varintEnc]
  simp only [show ¬ n < 128 by omega, ↓reduceDIte, List.length_cons]
  omega

theorem nx_varintSize_pos (n : Nat) : 1 ≤ varintSize n := by
  by_cases h : n < 128
  · rw [varintSize_lt128 n h]; omega
  · rw [varintSize_ge128 n (by omega)]; omega

theorem nx_varintSize_le_of_lt : ∀ (k n : Nat), n < 2 ^ (7 * (k + 1)) → varintSize n ≤ k + 1
  | 0, n, h => by rw [varintSize_lt128 n (by simpa using h)]; omega
  | k + 1, n, h => by
    by_cases h0 : n < 128
    · rw [varintSize_lt128 n h0]; omega
    · rw [varintSize_ge128 n (by omega)]
      have e : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
        rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add]
      rw [e] at h
      have h1 : n / 128 < 2 ^ (7 * (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; exact h
      have := nx_varintSize_le_of_lt k (n / 128) h1
      omega

theorem varintSize_le_10 (n : Nat) (h : n < 2 ^ 64) : varintSize n ≤ 10 :=
  nx_varintSize_le_of_lt 9 n (by omega)

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `sizeVarint(v)`: the length of `v`'s varint. -/
theorem wp_sizeVarint (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
      (App (Val #(functions raftpb.sizeVarint [])) (Val #v))
    {{ (n : w64), RET #n; ⌜sint.Z n = varintSize (uint.Z v).toNat⌝ }} := by
  wp_start
  wp_auto
  have hv0 : (uint.Z v).toNat < 2 ^ 64 := by word
  have h10 := varintSize_le_10 _ hv0
  ihave HI : (∃ (n x : w64), "v" ∷ v_ptr ↦ x ∗ "n" ∷ n_ptr ↦ n ∗
      "%Hn" ∷ ⌜1 ≤ sint.Z n ∧
        sint.Z n + varintSize (uint.Z x).toNat = 1 + varintSize (uint.Z v).toNat⌝ : IProp GF)
      $$ [v n]
  · iexists W64 1, v
    iframe
    ipureintro; constructor <;> simp
  wp_for HI
  wp_if_destruct
  · wp_for_post
    have hx : 128 ≤ (uint.Z x).toNat := by word
    have e := varintSize_ge128 _ hx
    have hpos := nx_varintSize_pos ((uint.Z x).toNat / 128)
    iframe
    iexists n + W64 1, x >>> W64 7
    iframe
    ipureintro
    have hsh : (uint.Z (x >>> W64 7)).toNat = (uint.Z x).toNat / 128 := by
      word
    rw [hsh]
    constructor <;> word
  · have hx : (uint.Z x).toNat < 128 := by word
    rw [varintSize_lt128 _ hx] at Hn
    iapply HΦ
    ipureintro; omega

end lemmas

end EtcdGrove
end Perennial
