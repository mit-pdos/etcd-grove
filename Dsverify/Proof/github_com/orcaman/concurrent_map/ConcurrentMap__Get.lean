/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__Get.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
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

theorem ConcurrentMap.GetV.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.GetV.spec (GF := GF) := fun m γ R key => by
  wp_start as Hr
  iunfold readerV at Hr
  icases Hr with ⟨%n, %shs, #Hc, Htoks⟩
  ihave #Hc' := Hc
  iunfold cmapCore at Hc'
  icases Hc' with ⟨#Hn, #Hsl, %Hns, #Hinv, #Hshs⟩
  wp_auto_lc 1
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_GetShardV $$ [$Hn $Hsl] as %sh %Hsh
  · ipureintro; exact ⟨Hns.1, by simpa using Hns.2⟩
  rw [List.getElem?_map] at Hsh
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp Hsh
  icases (BigSepL.bigSepL_lookup_acc hp).1 $$ Htoks with ⟨Htok, Hback⟩
  iunfold shardTok at Htok
  icases Htok with ⟨%mp, #Hitems, Htok⟩
  wp_method_call; wp_call
  wp_apply sync.RWMutex.wp_RLock $$ [$Htok] as ⟨Hrl, HP⟩
  iunfold shardP at HP
  icases HP with ⟨%Mi, HM, Hgi, #HR⟩
  wp_apply (wp_map_lookup2 (K := GoString) (V := GoInterface)) $$ [$HM] as HM
  imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
  imod cmap_observe γ (sint.nat n) shs _ p hp _ Mi _ $$ [Hgi HΦ] with ⟨Hgi, %M, %HMi, HΦ⟩
  · iframe Hinv Hgi HΦ
  wp_method_call; wp_call
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HM Hgi] as Htok
  · inext; iunfold shardP; iexists Mi; iframe HM Hgi HR
  ihave Htoks := Hback $$ %p [Htok]
  · iunfold shardTok; iexists mp; iframe Hitems Htok
  rw [list_set_lookup_self _ _ _ hp]
  have hk : Mi !! key = M !! key := by rw [HMi, lookup_shardPart_same]
  iapply HΦ
  isplitl [Htoks]
  · iunfold readerV; iexists n, shs; iframe Hc Htoks
  rw [hk]
  isplitr
  · ipureintro; constructor
    · rfl
    · simp
  rcases hM : M !! key with _ | v
  · simp; itrivial
  · simp only [Option.isSome_some, _root_.decide_true, ite_true, Option.getD_some]
    iapply HR $$ %key %v %(by rw [hk]; exact hM)

theorem ConcurrentMap.Get.wp_proof (wp_GetV : ConcurrentMap.GetV.spec (GF := GF)) :
    ConcurrentMap.Get.spec (GF := GF) := fun m R key => by
  wp_start_folded as ⟨-, Hr⟩
  iunfold reader at Hr
  icases Hr with ⟨%γ, Hr, #Hold⟩
  iapply (wp_GetV m γ R key) $$ [Hr] [HΦ]
  · iframe Hpkg Hr
  · inext
    iapply cmapOld_au_dep γ (fun M => M)
    iframe Hold
    iintro %M %v %ok ⟨Hr, %Hv, HR⟩
    iapply HΦ
    isplitl [Hr]
    · iapply reader_intro; iframe Hr Hold
    cases ok
    · simp only [Bool.false_eq_true, ite_false]
      ipureintro
      obtain ⟨h1, h2⟩ := Hv
      rcases hM : M !! key with _ | w <;> simp_all
    · simp only [ite_true]
      iexact HR

end proof

end Perennial.github_com.orcaman.concurrent_map
