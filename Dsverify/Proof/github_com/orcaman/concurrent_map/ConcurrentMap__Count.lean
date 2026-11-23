/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__Count.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
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

theorem ConcurrentMap.CountV.wp_proof : ConcurrentMap.CountV.spec (GF := GF) := fun m γ R => by
  wp_start as Hr
  iunfold readerV at Hr
  icases Hr with ⟨%n, %shs, #Hc, Htoks⟩
  ihave #Hc' := Hc
  iunfold cmapCore at Hc'
  icases Hc' with ⟨#Hn, #Hsl, %Hns, #Hinv, #Hshs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hl
  wp_auto
  ihave HL : (∃ (iv cnt : w64), "i" ∷ i_ptr ↦ iv ∗ "count" ∷ count_ptr ↦ cnt ∗
      "Htoks" ∷ ([∗list] p ∈ shs, shardTok p.1 R p.2) ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iv⌝ : IProp GF)
      $$ [i count Htoks]
  · iexists _, _; iframe; ipureintro; decide
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z iv < sint.Z n := by simpa using Hif
    have hb : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z m.len := ⟨Hi, by word⟩
    rw [if_pos hb]
    obtain ⟨p, hp⟩ : ∃ p, shs[(sint.Z iv).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    wp_apply wp_load_slice_index _ _ _ _ p.1 Hi $$ [$Hsl] as -
    · ipureintro; rw [List.getElem?_map, hp]; rfl
    icases (BigSepL.bigSepL_lookup_acc hp).1 $$ Htoks with ⟨Htok, Hback⟩
    iunfold shardTok at Htok
    icases Htok with ⟨%mp, #Hitems, Htok⟩
    wp_method_call; wp_call
    wp_apply sync.RWMutex.wp_RLock $$ [$Htok] as ⟨Hrl, HP⟩
    iunfold shardP at HP
    icases HP with ⟨%M, HM, Hgi, #HR⟩
    wp_apply (wp_map_len_lt (K := GoString) (V := GoInterface)) $$ [$HM] as ⟨HM, -⟩
    wp_method_call; wp_call
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HM Hgi] as Htok
    · inext; iunfold shardP; iexists M; iframe HM Hgi HR
    ihave Htoks := Hback $$ %p [Htok]
    · iunfold shardTok; iexists mp; iframe Hitems Htok
    rw [list_set_lookup_self _ _ _ hp]
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; word
  · iapply HΦ
    iunfold readerV; iexists n, shs; iframe Hc Htoks

theorem ConcurrentMap.Count.wp_proof (wp_CountV : ConcurrentMap.CountV.spec (GF := GF)) :
    ConcurrentMap.Count.spec (GF := GF) := fun m R => by
  wp_start_folded as ⟨-, Hr⟩
  iunfold reader at Hr
  icases Hr with ⟨%γ, Hr, #Hold⟩
  wp_apply wp_CountV $$ [$Hr] as %c Hr
  iapply HΦ
  iapply reader_intro; iframe Hr Hold

end proof

end Perennial.github_com.orcaman.concurrent_map
