/-
The proof of `sort.Sort` for a `Less` that answers anything (`Spec/sort/SortAnyLess.lean`): Perennial's
proof of `sort.Sort` (`Perennial/Proof/sort/Sort.lean`) over `pdqsort`'s any-`Less` spec
(`Spec/sort/pdqsortAnyLess.lean`). Go's `pdqsort` and its helpers (`zsortinterface.go`) bound every
index they pass to `Less` and `Swap` by the slice's bounds (`j > a`, `child+1 < hi`, `i <= j`,
`i < b`, `j >= 1`, ...), never by `Less`'s answers, and only permute by `Swap`: the any-`Less`
proofs of the helpers (`Proof/sort/*AnyLess.lean`) are Perennial's without the order.
Until 2026-11-21 an axiom (the trust boundary); `sort.Sort.wp_anyLess`, its linked form, is in
`Proof/sort/SortAnyLessLinked.lean`.
-/
module

public import Spec.sort.SortAnyLess
public import Spec.sort.pdqsortAnyLess
public import Proof.sort.AnyLessBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open sortAny

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.«Sort».wp_proofAnyLess
    (wp_pdqsort : EtcdGrove.sort.pdqsort.anyLessSpec (GF := GF) (hG := hG))
    (wp_Len : _root_.Perennial.math.bits.Len.spec (GF := GF) (hG := hG)) :
    sort.Sort''.anyLessSpec (GF := GF) (hG := hG) := fun E x R l => by
  wp_start as ⟨#Hs, Hl, %Hlen⟩
  wp_auto
  wp_apply wp_any_Len x R l $$ [$Hs $Hl] as Hl
  wp_if_destruct
  · iapply HΦ
    iframe Hl
    ipureintro
    exact List.Perm.refl _
  wp_apply wp_Len with %n _
  wp_apply wp_pdqsort E x R l (W64 0) (W64 l.length) n $$ [Hl] with %l' ⟨Hl, %Hperm⟩
  · iframe Hl; iframe #; ipureintro
    refine ⟨by word, by word, by word, Hlen⟩
  iapply HΦ
  iframe Hl
  ipureintro
  exact Hperm

end proof

end EtcdGrove
end Perennial
