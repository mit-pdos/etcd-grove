/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The concurrent-map model's linked results (the functions SwiftPaxos's `swift` calls).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.fnv32
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__GetShard
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__Set
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__Remove
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__Has
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__Get
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__Upsert
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__Count
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__IsEmpty
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__IterCb
public import Dsverify.Proof.github_com.orcaman.concurrent_map.New
public import Dsverify.Proof.github_com.orcaman.concurrent_map.UpsertL
public import Dsverify.Proof.github_com.orcaman.concurrent_map.RemoveL

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

theorem wp_fnv32 : fnv32.spec (GF := GF) := fnv32.wp_proof
theorem ConcurrentMap.wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF) :=
  ConcurrentMap.GetShardV.wp_proof wp_fnv32

/-! The strong specs (over the view `cmapView γ M`). -/
theorem wp_NewV : NewV.spec (GF := GF) := NewV.wp_proof
theorem ConcurrentMap.wp_SetV : ConcurrentMap.SetV.spec (GF := GF) :=
  ConcurrentMap.SetV.wp_proof ConcurrentMap.wp_GetShardV
theorem ConcurrentMap.wp_RemoveV : ConcurrentMap.RemoveV.spec (GF := GF) :=
  ConcurrentMap.RemoveV.wp_proof ConcurrentMap.wp_GetShardV
theorem ConcurrentMap.wp_UpsertV : ConcurrentMap.UpsertV.spec (GF := GF) :=
  ConcurrentMap.UpsertV.wp_proof ConcurrentMap.wp_GetShardV
theorem ConcurrentMap.wp_GetV : ConcurrentMap.GetV.spec (GF := GF) :=
  ConcurrentMap.GetV.wp_proof ConcurrentMap.wp_GetShardV
theorem ConcurrentMap.wp_HasV : ConcurrentMap.HasV.spec (GF := GF) :=
  ConcurrentMap.HasV.wp_proof ConcurrentMap.wp_GetShardV
theorem ConcurrentMap.wp_CountV : ConcurrentMap.CountV.spec (GF := GF) :=
  ConcurrentMap.CountV.wp_proof
theorem ConcurrentMap.wp_IsEmptyV : ConcurrentMap.IsEmptyV.spec (GF := GF) :=
  ConcurrentMap.IsEmptyV.wp_proof ConcurrentMap.wp_CountV
theorem ConcurrentMap.wp_IterCbV : ConcurrentMap.IterCbV.spec (GF := GF) :=
  ConcurrentMap.IterCbV.wp_proof

/-! The old specs (over `isCMap m R`, `reader m R`), corollaries of the strong ones. -/
theorem ConcurrentMap.wp_GetShard : ConcurrentMap.GetShard.spec (GF := GF) :=
  ConcurrentMap.GetShard.wp_proof ConcurrentMap.wp_GetShardV
theorem wp_New : New.spec (GF := GF) := New.wp_proof wp_NewV
theorem ConcurrentMap.wp_Set : ConcurrentMap.Set.spec (GF := GF) :=
  ConcurrentMap.Set.wp_proof ConcurrentMap.wp_SetV
theorem ConcurrentMap.wp_Remove : ConcurrentMap.Remove.spec (GF := GF) :=
  ConcurrentMap.Remove.wp_proof ConcurrentMap.wp_RemoveV
theorem ConcurrentMap.wp_Has : ConcurrentMap.Has.spec (GF := GF) :=
  ConcurrentMap.Has.wp_proof ConcurrentMap.wp_HasV
theorem ConcurrentMap.wp_Get : ConcurrentMap.Get.spec (GF := GF) :=
  ConcurrentMap.Get.wp_proof ConcurrentMap.wp_GetV
theorem ConcurrentMap.wp_Upsert : ConcurrentMap.Upsert.spec (GF := GF) :=
  ConcurrentMap.Upsert.wp_proof ConcurrentMap.wp_UpsertV
theorem ConcurrentMap.wp_Count : ConcurrentMap.Count.spec (GF := GF) :=
  ConcurrentMap.Count.wp_proof ConcurrentMap.wp_CountV
theorem ConcurrentMap.wp_IsEmpty : ConcurrentMap.IsEmpty.spec (GF := GF) :=
  ConcurrentMap.IsEmpty.wp_proof ConcurrentMap.wp_IsEmptyV
theorem ConcurrentMap.wp_IterCb : ConcurrentMap.IterCb.spec (GF := GF) :=
  ConcurrentMap.IterCb.wp_proof ConcurrentMap.wp_IterCbV
theorem ConcurrentMap.wp_UpsertVL : ConcurrentMap.UpsertVL.spec (GF := GF) :=
  ConcurrentMap.UpsertVL.wp_proof ConcurrentMap.wp_GetShardV
theorem ConcurrentMap.wp_RemoveL : ConcurrentMap.RemoveL.spec (GF := GF) :=
  ConcurrentMap.RemoveL.wp_proof ConcurrentMap.wp_GetShardV

end link

end Perennial.github_com.orcaman.concurrent_map
