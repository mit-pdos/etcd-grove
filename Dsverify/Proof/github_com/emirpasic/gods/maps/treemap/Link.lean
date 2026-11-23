/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The treemap model's linked results (the functions `state` calls).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.NewWith
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Map__find
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Map__Get
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Map__Put

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

theorem wp_NewWith : NewWith.spec (GF := GF) := NewWith.wp_proof
theorem Map.wp_find : Map.find.spec (GF := GF) := Map.find.wp_proof
theorem Map.wp_Get : Map.Get.spec (GF := GF) := Map.Get.wp_proof Map.wp_find
theorem Map.wp_Put : Map.Put.spec (GF := GF) := Map.Put.wp_proof Map.wp_find

end link

end Perennial.github_com.emirpasic.gods.maps.treemap
