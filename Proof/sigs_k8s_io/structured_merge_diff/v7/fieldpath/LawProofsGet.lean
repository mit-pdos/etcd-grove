/-
**Looking up a `SetNodeMap`'s node** (`SetNodeMap.Get`'s binary search): a node's key as the
comparison sees it, and what a found/missing key means for the set's paths.

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpG
open fpC

/-- A key of a node list is one of its paths' heads. -/
theorem heads_iff {l : NL} (hl : NLok l) (D : PathSet) (hD : ∀ q, q ∈ D ↔ q ∈ nlPaths l)
    (pe : PE) : pe ∈ D.heads ↔ pe ∈ keys l := by
  rw [PathSet_mem_heads_law_holds, fpK.nl_key_iff hl]
  constructor
  · rintro ⟨q, -, hq⟩; exact ⟨q, (hD _).1 hq⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_, (hD _).2 hr⟩
    rintro rfl
    obtain ⟨k, S, r', hm, hr', he⟩ := (mem_nlPaths l _).1 hr
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact (hl.2 _ S hm).2.2 hr'

/-- The paths below a node's key are its set's. -/
theorem under_eq {l : NL} (hl : NLok l) (D : PathSet) (hD : ∀ q, q ∈ D ↔ q ∈ nlPaths l)
    {k : PE} {S : PathSet} (hm : (k, S) ∈ l) : D.under k = S := by
  apply FSet.ext'
  intro r
  rw [PathSet_mem_under_law_holds, hD, nl_col hl hm r]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨fun e => (hl.2 k S hm).2.2 (e ▸ h), h⟩

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A node's key as the comparison sees it (`fpA.mdl` over the keys). -/
theorem nodesL_mdl (ns : List fieldpath.setNode) (l : NL) (d : PE) :
    nodesL (GF := GF) ns l ⊢
      ⌜∀ (k : Nat) (n : fieldpath.setNode), ns[k]? = some n →
        (keys l)[k]? = some (fpA.mdl ns (keys l) d n)⌝ := by
  iintro #H
  iapply (pure_forall (PROP := IProp GF)).2; iintro %k
  iapply (pure_forall (PROP := IProp GF)).2; iintro %n
  by_cases hk : ns[k]? = some n
  · have hm : n ∈ ns := List.mem_of_getElem? hk
    ihave ⟨%x1, %S1, %h1, #H1, -⟩ := nodesL_lookup ns l k n hk $$ H
    ihave ⟨%x2, %S2, %h2, #H2, -⟩ := nodesL_lookup ns l (fpA.peIdx ns n) n (fpA.peIdx_get ns n hm) $$ H
    ihave %he := fpL.isPE_agree' n.pathElement' x1 x2 $$ [$H1 $H2]
    ipureintro
    intro _
    unfold fpA.mdl
    simp only [keys, List.getElem?_map, h1, h2, he]
    rfl
  · ipureintro; intro h; exact absurd h hk

end rep

end fpG

end smd
end EtcdGrove
end Perennial
