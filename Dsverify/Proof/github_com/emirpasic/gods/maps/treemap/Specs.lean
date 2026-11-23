/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/Specs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The specs of the treemap functions SwiftPaxos's `state` calls (internal, the replica group's):
`NewWith`, `(*Map).find`, `Put`, `Get`, over `isTreeMap` (`Defs.lean`).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions]

/-- The comparator `cmp` compares encoded keys as signed integers (persistent). -/
def cmpOk (cmp : GoFunc) (enc : w64 → GoInterface) : IProp GF :=
  iprop(□ ∀ (a b : w64) (Φ : val → IProp GF),
    ▷ (∀ c : w64, ⌜(sint.Z c < 0 ↔ sint.Z a < sint.Z b) ∧ (c = W64 0 ↔ a = b)⌝ -∗ Φ #c) -∗
    WP (App (App (Val #cmp) (Val #(enc a))) (Val #(enc b))) {{ Φ }})

instance cmpOk_persistent (cmp : GoFunc) (enc : w64 → GoInterface) :
    Persistent (cmpOk (GF := GF) cmp enc) := by unfold cmpOk; infer_instance

/-- The `*Map` at `tm` holds the sorted entries `es` (keys encoded by `enc`): a hypothesis
(`SwiftLibs.isTreeMap`; the lab's was over its model's slice of entries). -/
def isTreeMap [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] (tm : Loc)
    (enc : w64 → GoInterface) (es : Entries) : IProp GF :=
  l.isTreeMap hG tm enc es

/-- A map's entries are sorted (`SwiftLibs.isTreeMap_sorted`). -/
theorem isTreeMap_sorted [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] (tm : Loc)
    (enc : w64 → GoInterface) (es : Entries) :
    isTreeMap (GF := GF) tm enc es ⊢ isTreeMap tm enc es ∗ ⌜sortedE es⌝ :=
  l.isTreeMap_sorted hG tm enc es

end defs

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `NewWith(cmp)`: an empty map. -/
abbrev NewWith.spec : Prop :=
  ∀ (cmp : GoFunc) (enc : w64 → GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
      cmpOk cmp enc }}
    (App (Val (@! treemap.NewWith)) (Val #cmp))
  {{ (tm : Loc), RET #tm; isTreeMap tm enc [] }}

/-- `m.Put(key, value)`. -/
abbrev Map.Put.spec : Prop :=
  ∀ (tm : Loc) (enc : w64 → GoInterface) (es : Entries) (k : w64) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
      isTreeMap tm enc es }}
    (App (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Put")) (Val #(enc k))) (Val #v))
  {{ RET #(); isTreeMap tm enc (putE es k v) }}

/-- `m.Get(key)`: `key`'s value and `true`, or `nil` and `false`. -/
abbrev Map.Get.spec : Prop :=
  ∀ (tm : Loc) (enc : w64 → GoInterface) (es : Entries) (k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
      isTreeMap tm enc es }}
    (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Get")) (Val #(enc k)))
  {{ RET (PairV #((lookupE es k).getD interface.nil) #((lookupE es k).isSome));
      isTreeMap tm enc es }}

end spec

end Perennial.github_com.emirpasic.gods.maps.treemap
