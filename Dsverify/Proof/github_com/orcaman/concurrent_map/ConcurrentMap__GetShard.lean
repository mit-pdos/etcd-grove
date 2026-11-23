/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__GetShard.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option linter.unusedSectionVars false

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem shard_index (h : w32) (n : w64) (hn : 0 < sint.Z n) :
    uint.Z (W64 (uint.Z h) % n) = uint.Z h % sint.Z n := by
  have : uint.Z (W64 (uint.Z h) % n) = uint.Z (W64 (uint.Z h)) % uint.Z n := by
    simp only [uint.Z, BitVec.toNat_umod]; push_cast; rfl
  rw [this]
  have h1 : uint.Z (W64 (uint.Z h)) = uint.Z h := by word
  have h2 : uint.Z n = sint.Z n := by word
  rw [h1, h2]

theorem ConcurrentMap.GetShardV.wp_proof (wp_fnv32 : fnv32.spec (GF := GF)) :
    ConcurrentMap.GetShardV.spec (GF := GF) := fun m n shs key => by
  wp_start as ⟨#Hn, #Hsl, %Hns⟩
  wp_auto
  wp_apply wp_fnv32
  have hn0 : ¬ uint.Z n = 0 := by word
  rw [if_neg hn0]
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  have hidx := shard_index (fnv32F key) n Hns.1
  have hmod : uint.Z (fnv32F key) % sint.Z n < sint.Z n := Int.emod_lt_of_pos _ Hns.1
  have hmod0 : 0 ≤ uint.Z (fnv32F key) % sint.Z n := Int.emod_nonneg _ (by omega)
  have hi0 : 0 ≤ sint.Z (W64 (uint.Z (fnv32F key)) % n) ∧
      sint.Z (W64 (uint.Z (fnv32F key)) % n) < sint.Z m.len := by
    constructor <;> word
  rw [if_pos hi0]
  have hsh : (sint.Z (W64 (uint.Z (fnv32F key)) % n)).toNat = shardOf (sint.nat n) key := by
    unfold shardOf
    have : sint.Z (W64 (uint.Z (fnv32F key)) % n) = uint.Z (fnv32F key) % sint.Z n := by word
    rw [this]
    have hu : (uint.Z (fnv32F key) : Int) = (uint.nat (fnv32F key) : Int) := by word
    have hs : sint.Z n = (sint.nat n : Int) := by word
    rw [hu, hs]
    omega
  have hlt : shardOf (sint.nat n) key < shs.length := by
    have : 0 < sint.nat n := by word
    rw [Hns.2]; exact shardOf_lt _ _ this
  obtain ⟨sh, hsh'⟩ : ∃ sh, shs[shardOf (sint.nat n) key]? = some sh :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  wp_apply wp_load_slice_index _ _ _ _ sh hi0.1 $$ [$Hsl] as -
  · ipureintro; rw [hsh]; exact hsh'
  iapply HΦ
  ipureintro; exact hsh'

theorem ConcurrentMap.GetShard.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.GetShard.spec (GF := GF) := fun m R key => by
  wp_start_folded as #Hm
  iunfold isCMap at Hm
  icases Hm with ⟨%γ, Hm, -⟩
  iunfold isCMapV at Hm
  icases Hm with ⟨%n, %shs, Hm⟩
  iunfold cmapCore at Hm
  icases Hm with ⟨#Hn, #Hsl, %Hns, -, #Hshs⟩
  wp_apply wp_GetShardV $$ [$Hn $Hsl] as %sh %Hsh
  · ipureintro; exact ⟨Hns.1, by simpa using Hns.2⟩
  rw [List.getElem?_map] at Hsh
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp Hsh
  iapply HΦ
  isplitl
  · ihave #Hp := (BigSepL.bigSepL_lookup hp) $$ Hshs
    iunfold isShard; iexists p.2; iexact Hp
  iexists (shs.map Prod.fst), _
  iframe Hsl
  ipureintro; rw [List.getElem?_map, hp]; rfl

end proof

end Perennial.github_com.orcaman.concurrent_map
