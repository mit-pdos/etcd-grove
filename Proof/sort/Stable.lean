/-
The proof of `sort.Stable` (`Spec/sort/Stable.lean`) over Perennial's translation of Go's
`sort.Stable` (`stable`: insertion sorts of blocks of 20, then `symMerge`s of doubling blocks).
Until 2026-11-21 an axiom (the trust boundary).

The proof runs `stable`'s spec on the sorter seen through the positions it started with
(`sorterSpec_map`: a list `l.zipIdx`, compared by `lt` on the elements); `stable` computes its
model `stableM` (`Spec/sort/stable.lean`), which on such a list is the stable sort of `l`
(`stableModel.stableM_eq_mergeSort`, `Proof/sort/StableCorrect.lean`).
-/
module

public import Spec.sort.Stable
public import Spec.sort.stable
public import Proof.sort.StableTagged

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.Stable.wp_proof (wp_stable : sort.stable.spec (GF := GF) (hG := hG)) :
    sort.Stable.spec (GF := GF) (hG := hG) := fun E x R lt l hswo => by
  wp_start as ⟨#Hs, Hl, %Hlen⟩
  ihave #Hsrt := sorterSpec_isSorter x R lt $$ Hs
  wp_auto
  wp_apply _root_.Perennial.sort.wp_sorter_Len x R (fun a b => lt a b = true) l $$ [$Hsrt $Hl]
    as Hl
  ihave #Hs' := sorterSpec_map x R lt (Prod.fst : E × Nat → E) $$ Hs
  rw [← List.zipIdx_map_fst 0 l]
  wp_apply wp_stable (E × Nat) x (fun tl => R (tl.map Prod.fst)) (fun a b => lt a.1 b.1)
    l.zipIdx (W64 (l.zipIdx.map Prod.fst).length) $$ [Hl] as Hl
  · iframe Hl; iframe #; ipureintro
    simp only [List.length_map, List.length_zipIdx]
    exact ⟨by word, Hlen⟩
  iapply HΦ
  rw [List.zipIdx_map_fst, ← stableModel.stableM_eq_mergeSort lt (swo_of_strictWeakOrder lt hswo) l]
  rw [List.length_zipIdx]
  iexact Hl

end proof

end EtcdGrove
end Perennial
