/-
The swiftpaxos kit's representation of gods' treemap (lab `Proof/treemap/Specs.lean`'s
`treemap.isTreeMap`): the libraries' choice `SwiftLibs.isTreeMap` (Base.lean), over which the
kit's `SwiftHyps` states the shared treemap specs
(`Dsverify/Spec/github_com/emirpasic/gods/maps/treemap/Specs.lean`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.maps.treemap.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The `*Map` at `tm` holds the sorted entries `es` (keys encoded by `enc`): the libraries'
choice (`SwiftLibs.isTreeMap`; the lab's was over its model's slice of entries). -/
def isTreeMap [l : SwiftLibs GF] (tm : Loc) (enc : w64 → GoInterface)
    (es : github_com.emirpasic.gods.maps.treemap.Entries) : IProp GF :=
  l.isTreeMap hG tm enc es

/-- A map's entries are sorted (`SwiftLibs.isTreeMap_sorted`). -/
theorem isTreeMap_sorted [l : SwiftLibs GF] (tm : Loc) (enc : w64 → GoInterface)
    (es : github_com.emirpasic.gods.maps.treemap.Entries) :
    isTreeMap (GF := GF) tm enc es ⊢
      isTreeMap tm enc es ∗ ⌜github_com.emirpasic.gods.maps.treemap.sortedE es⌝ :=
  l.isTreeMap_sorted hG tm enc es

end defs

end Perennial.github_com.imdea_software.swiftpaxos
