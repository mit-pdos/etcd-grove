/-
`hraftnet.peers`'s proof: the loop inserting servers `1..NS`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.peers
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverAddr
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ServerAddrs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem peers.wp_proof (wp_serverAddr : serverAddr.spec (GF := GF))
    (wp_ServerAddrs : ServerAddrs.spec (GF := GF)) : peers.spec (GF := GF) := by
  wp_start as -
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) github_com.hashicorp.raft.ServerAddress.ty
    go.string) as %mp Hm
  try wp_auto
  wp_apply wp_ServerAddrs as %sl ⟨%L, Hsl, %HL⟩
  subst HL
  ihave %Hlen := ownSlice_len $$ Hsl
  try wp_auto
  ihave HI : (∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "Hm" ∷ mp ↦$ peersUpTo (uint.nat k - 1) ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ 7⌝ : IProp GF) $$ [i Hm]
  · iexists W64 1
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hb : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z sl.len := by
      have : serverAddrs.length = 6 := rfl
      constructor <;> word
    try (rw [ite_eq_left hb])
    wp_apply (wp_load_slice_index sl (sint.Z (k - W64 1)) serverAddrs _
        (serverAddrs.getD (uint.nat k - 1) go!"") hb.1)
      $$ [Hsl] as Hsl
    · iframe
      ipureintro
      have hidx : (sint.Z (k - W64 1)).toNat = uint.nat k - 1 := by word
      rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        have : serverAddrs.length = 6 := rfl; rw [this]; word)]
      rfl
    wp_apply wp_serverAddr
    wp_apply (wp_mapInsert github_com.hashicorp.raft.ServerAddress.ty mp _ _ _) $$ [$Hm] as Hm
    wp_for_post
    iframe
    iexists k + W64 1
    have hk1 : uint.nat (k + W64 1) - 1 = (uint.nat k - 1) + 1 := by word
    have hk2 : W64 (((uint.nat k - 1 + 1 : Nat)) : Int) = k := by word
    rw [hk1]
    simp only [peersUpTo, hk2]
    iframe
    ipureintro; constructor <;> word
  · rw [show uint.nat k - 1 = 6 by word]
    iapply HΦ
    iframe

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
