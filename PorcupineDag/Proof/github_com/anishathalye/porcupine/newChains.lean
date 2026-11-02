/- Lean-first (no Rocq counterpart). Proof of
`PorcupineDag/Spec/github_com/anishathalye/porcupine/newChains.lean`.

UNFINISHED (2026-11-02): the first loop (the clients, `clientAt`, `n` the chains' sizes so far)
is proved; the rest is a `sorry`. What remains, with the lemmas already in `NewChainsLemmas.lean`:
- `firstUnks := make([]int, n*numClients)`: `n = h.length` (`chains_length_sum`), no overflow
  (`AllocOk`); cut into one piece per operation id (`ownSlice_pieces`, after
  `ownSlice_trivial_slice`).
- the second (nested) loop: each client's `j`-th `clientOperation` (its `id` is the chain's
  `j`-th, `CoFresh`) gets the piece of its id, taken from a big separating conjunction over the
  ids not yet handed out (a `Nodup` list; ids are distinct by `ChainsOk`); the struct store needs
  `iStructNamed` (field access through `Access` fails on slice elements).
- `ch := chains{...}`, at the state `heads = replicate nc 0`, `nDeps` zero, `frontier = []`,
  nothing visited (`CoFresh`'s `visited = false`), `fu` all zeros: `chainsOwnCl`.
- the third loop: `computeFirstUnk(i)` (its premise on the previous operation is vacuous at
  head 0), then `nDeps` counted by the inner loop (`deps_init`, `count_succ`; `op` is a copy of
  the first `clientOperation`, its `firstUnk` holds `FUe … 0` by `FuOk`).
- the fourth loop: `addToFrontier(i)` for the clients with operations and `nDeps = 0`
  (`init_unrelated` for its premise; `cs.length < 2^62` from `AllocOk`); then
  `chainsInv_init`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newChains
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__computeFirstUnk
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__addToFrontier
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.NewChainsLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option maxHeartbeats 4000000 in
theorem newChains.wp_proof
    (wp_computeFirstUnk : chains.computeFirstUnk.spec (GF := GF) (hG := hG))
    (wp_addToFrontier : chains.addToFrontier.spec (GF := GF) (hG := hG)) :
    newChains.spec (GF := GF) (hG := hG) := by
  intro ohsl h cs cons hok hwf halloc
  wp_start as ⟨Hoh, #Hlin⟩
  iunfold ohistOwn at Hoh
  icases Hoh with ⟨%sls, Hsls, %Hslslen, Hcls⟩
  ihave %Hslen := ownSlice_len $$ Hsls
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := client) ohsl.len)
  · ipureintro; exact Hslen.2
  iintro %clsl ⟨Hcl, Hclcap⟩
  wp_auto
  revert i_ptr
  intro icnt_ptr
  irename : (i_ptr ↦ zero_val w64 : IProp GF) => ikey
  have hnc : sint.nat ohsl.len = cs.length := by rw [← Hslslen, Hslen.1]
  have hncZ : sint.Z ohsl.len = (cs.length : Int) := by
    rw [← hnc]; exact (Int.toNat_of_nonneg Hslen.2).symm
  -- the clients
  ihave IH1 : iprop(∃ (k nv kv : w64) (cv : GoSlice),
      "i" ∷ icnt_ptr ↦ k ∗ "ikey" ∷ i_ptr ↦ kv ∗ "c" ∷ c_ptr ↦ cv ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hcl" ∷ clsl ↦* ((List.range (sint.nat k)).map (clientAt sls) ++
        List.replicate (cs.length - sint.nat k) (zero_val client)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ cs.length ∧
        sint.Z nv = (((cs.take (sint.nat k)).map List.length).sum : Nat)⌝) $$ [i ikey c n Hcl]
  · iexists W64 0, W64 0, zero_val w64, zero_val GoSlice
    simp only [show sint.nat (W64 0) = 0 from rfl, List.range_zero, List.map_nil, List.nil_append,
      Nat.sub_zero, List.take_zero]
    rw [hnc]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp⟩
  wp_for IH1
  ihave %Hcllen := ownSlice_len $$ Hcl
  wp_if_destruct
  · have hkn : sint.nat k < cs.length := by word
    have hbk : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z ohsl.len := ⟨Hk.1, Hif⟩
    obtain ⟨sl, hsl⟩ : ∃ sl, sls[sint.nat k]? = some sl :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [hbk, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index ohsl (sint.Z k) sls _ sl Hk.1) $$ [Hsls] as Hsls
    · iframe Hsls; ipureintro; exact hsl
    have hcllen : ((List.range (sint.nat k)).map (clientAt sls) ++
        List.replicate (cs.length - sint.nat k) (zero_val client)).length = cs.length := by
      simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
      omega
    have hbk2 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z clsl.len := by
      refine ⟨Hk.1, ?_⟩
      have h1 := Hcllen.1
      have h2 : ((sint.nat clsl.len : Nat) : Int) = sint.Z clsl.len := Int.toNat_of_nonneg Hcllen.2
      rw [← h1, hcllen] at h2
      rw [← h2, ← hncZ]; exact Hif
    simp only [hbk2, _root_.and_self, ↓reduceIte]
    have hval : ({ id' := k, cltOps' := sl, head' := W64 0, nDeps' := 0 } : client) =
        clientAt sls (sint.nat k) := by
      unfold clientAt
      rw [List.getD_eq_getElem?_getD, hsl]
      congr 1
      word
    rw [hval]
    wp_apply (wp_store_slice_index (V := client) clsl (sint.Z k) _ (clientAt sls (sint.nat k)))
      $$ [Hcl] as Hcl
    · iframe Hcl; ipureintro; exact ⟨Hk.1, by omega⟩
    rw [show (sint.Z k).toNat = sint.nat k from rfl, set_prefix_replicate _ _ hkn]
    icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
      (Φ := fun c sl => iprop(∃ cos, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝)) hsl).1 $$ Hcls
      with ⟨Hc, Hcls⟩
    icases Hc with ⟨%cos, Hcos, %Hcof⟩
    ihave %Hcoslen := ownSlice_len $$ Hcos
    ihave Hcls := Hcls $$ %sl [Hcos]
    · iexists cos; iframe; ipureintro; exact Hcof
    rw [list_set_lookup_self _ _ _ hsl]
    have hsum := sum_take_le cs (sint.nat k + 1)
    have htot := chains_length_sum hok
    have hsucc := sum_take_succ cs hkn
    have hlenk : sint.Z sl.len = ((chain cs (sint.nat k)).length : Int) := by
      rw [← Hcof.1, Hcoslen.1]; exact (Int.toNat_of_nonneg Hcoslen.2).symm
    wp_for_post
    iframe
    iexists k + W64 1, nv + sl.len, k, sl
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hk1]
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have h60 := hwf.1
    have : sint.Z (nv + sl.len) = sint.Z nv + sint.Z sl.len := by word
    rw [this, Hk.2.2, hlenk, hsucc]
    omega
  · -- NOT YET PROVED (see the file header): the rest of `newChains` after the clients' loop.
    sorry

end proof

end porcupine
end EtcdGrove
end Perennial
