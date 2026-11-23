/-
The swiftpaxos kit's representation of gods' treemap (lab `Proof/treemap/Specs.lean`'s
`treemap.isTreeMap`): gods' own, `treemap.isTreeMapR`
(`Dsverify/Proof/github_com/emirpasic/gods/maps/treemap/Rep.lean`), over which the shared treemap
specs (`Dsverify/Spec/github_com/emirpasic/gods/maps/treemap/Specs.lean`) are proved
(`treemap.hyps_true`; notes/gods-verified.md). Until gods was verified, a libraries' choice
(`SwiftLibs`) with the specs among the kit's hypotheses (`SwiftHyps`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.maps.treemap.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Rep

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The `*Map` at `tm` holds the sorted entries `es` (keys encoded by `enc`): gods' own
representation (`treemap.isTreeMapR`; the lab's was over its model's slice of entries). -/
def isTreeMap (tm : Loc) (enc : w64 → GoInterface)
    (es : github_com.emirpasic.gods.maps.treemap.Entries) : IProp GF :=
  github_com.emirpasic.gods.maps.treemap.isTreeMapR tm enc es

/-- A map's entries are sorted (lab `treemap.isTreeMap_sorted`). -/
theorem isTreeMap_sorted (tm : Loc) (enc : w64 → GoInterface)
    (es : github_com.emirpasic.gods.maps.treemap.Entries) :
    isTreeMap (GF := GF) tm enc es ⊢
      isTreeMap tm enc es ∗ ⌜github_com.emirpasic.gods.maps.treemap.sortedE es⌝ := by
  unfold isTreeMap github_com.emirpasic.gods.maps.treemap.isTreeMapR
  iintro ⟨%tr, Hm, Ht⟩
  iunfold github_com.emirpasic.gods.trees.redblacktree.isTree at Ht
  icases Ht with ⟨%cmp, %T, %h, %D, Hraw, #Hcmp, %Hp⟩
  obtain ⟨hs, hes, hrb⟩ := Hp
  isplitl
  · iexists tr
    isplitl [Hm]
    · iexact Hm
    iunfold github_com.emirpasic.gods.trees.redblacktree.isTree
    iexists cmp, T, h, D
    isplitl [Hraw]
    · iexact Hraw
    isplitr
    · iexact Hcmp
    ipureintro; exact ⟨hs, hes, hrb⟩
  · ipureintro; rw [← hes]; exact hs

end defs

end Perennial.github_com.imdea_software.swiftpaxos
