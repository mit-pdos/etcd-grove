/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/names.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.names
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]


private theorem namesL_succ (k : Nat) :
    AntSim.namesL (k + 1) = AntSim.namesL k ++ [AntSim.nameOf (W64 ((k : Int) + 1))] := by
  simp [AntSim.namesL, List.range_succ]

theorem names.wp_proof (wp_Name : Name.spec (GF := GF) (hG := hG)) :
    names.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  ihave Hnil := ownSlice_nil (V := GoString) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := GoString) (GF := GF)
  ihave IH : iprop(∃ (i : w64) (o : GoSlice) (xs : List GoString),
      "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "Ho" ∷ o ↦* xs ∗
      "Hc" ∷ ownSliceCap GoString o (DFrac.own 1) ∗
      "%Hi" ∷ ⌜n = W64 (-1) ∨
        (1 ≤ uint.Z i ∧ uint.Z i ≤ uint.Z n + 1 ∧ xs = AntSim.namesL (uint.nat i - 1))⌝) $$ [i out Hnil Hcap0]
  · iexists W64 1, slice.nil, []
    iframe i out
    iframe Hnil
    iframe Hcap0
    ipureintro; right; refine ⟨by decide, by word, rfl⟩
  iapply wp_fupd
  wp_for IH
  wp_if_destruct
  · have Hle : uint.Z i ≤ uint.Z n := Hif
    wp_apply wp_Name i $$ [$Hpkg]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append o xs _ [AntSim.nameOf i] (DFrac.own 1) $$ [$Ho $Hc $Hsl1]
      as %o' ⟨Ho, Hc, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    rcases Hi with Hi | ⟨h1, h2, h3⟩
    · left; exact Hi
    by_cases hmax : n = W64 (-1)
    · left; exact hmax
    right
    have hn : uint.Z n < 2 ^ 64 - 1 := by
      have : uint.Z n ≠ 2 ^ 64 - 1 := fun h => hmax (by word)
      word
    have hi1 : uint.Z (i + W64 1) = uint.Z i + 1 := by word
    refine ⟨by omega, by omega, ?_⟩
    rw [h3, show uint.nat (i + W64 1) - 1 = (uint.nat i - 1) + 1 by word, namesL_succ]
    congr 3
    word
  · have Hnle : ¬ uint.Z i ≤ uint.Z n := Hif
    have hxs : xs = AntSim.namesL (uint.nat n) := by
      rcases Hi with Hi | ⟨h1, h2, h3⟩
      · subst Hi; exfalso; apply Hnle; word
      rw [h3]; congr 1; word
    subst hxs
    imod ownSlice_persist $$ Ho with #Ho
    imodintro
    iapply HΦ
    iunfold AntCheck.strsRO
    iexact Ho

end proof

end AntHarness
end EtcdGrove
end Perennial
