/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__Set.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
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

theorem ConcurrentMap.SetV.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.SetV.spec (GF := GF) := fun m γ R key v => by
  wp_start as ⟨#Hm, #Hv⟩
  iunfold isCMapV at Hm
  icases Hm with ⟨%n, %shs, Hm⟩
  iunfold cmapCore at Hm
  icases Hm with ⟨#Hn, #Hsl, %Hns, #Hinv, #Hshs⟩
  wp_auto_lc 1
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_GetShardV $$ [$Hn $Hsl] as %sh %Hsh
  · ipureintro; exact ⟨Hns.1, by simpa using Hns.2⟩
  rw [List.getElem?_map] at Hsh
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp Hsh
  ihave #Hp := (BigSepL.bigSepL_lookup hp) $$ Hshs
  iunfold isShardV at Hp
  icases Hp with ⟨%mp, #Hitems, #Hg⟩
  wp_method_call; wp_call
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  iunfold shardP at HP
  icases HP with ⟨%M, HM, Hgi, #HR⟩
  wp_apply (wp_mapInsert (K := GoString) (V := GoInterface)) $$ [$HM] as HM
  imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
  imod cmap_update γ (sint.nat n) shs _ p hp M (fun M => <[key := v]> M) (fun M => <[key := v]> M)
      (fun M => by rw [shardPart_insert, if_pos rfl])
      (fun j M hj => by rw [shardPart_insert, if_neg (Ne.symm hj)])
      (fun _ => iprop(True -∗ Φ #())) $$ [Hgi HΦ] with ⟨Hgi, %M', HΦ⟩
  · iframe Hinv Hgi
    imod HΦ with ⟨%M', Hview, Hcont⟩
    imodintro
    iexists M'
    iframe Hview
    iintro _ Hview
    iapply Hcont $$ Hview
  wp_method_call; wp_call
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HM Hgi]
  · inext
    iunfold shardP
    iexists _
    iframe HM Hgi
    iintro !> %k %v' %Hk
    by_cases hk : k = key
    · subst hk
      rw [GMap.lookup_insert_eq] at Hk; cases Hk; iexact Hv
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at Hk
      iapply HR $$ %k %v' %Hk
  iapply HΦ; itrivial

theorem ConcurrentMap.Set.wp_proof (wp_SetV : ConcurrentMap.SetV.spec (GF := GF)) :
    ConcurrentMap.Set.spec (GF := GF) := fun m R key v => by
  wp_start_folded as ⟨#Hm, #Hv⟩
  iunfold isCMap at Hm
  icases Hm with ⟨%γ, #HmV, #Hold⟩
  iapply (wp_SetV m γ R key v) $$ [] [HΦ]
  · iframe Hpkg HmV Hv
  · inext
    iapply cmapOld_au γ (fun M => <[key := v]> M)
    iframe Hold
    iexact HΦ

end proof

end Perennial.github_com.orcaman.concurrent_map
