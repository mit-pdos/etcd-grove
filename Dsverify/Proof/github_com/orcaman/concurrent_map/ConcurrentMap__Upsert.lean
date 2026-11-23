/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__Upsert.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.ConcurrentMap__UpsertDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem ConcurrentMap.UpsertV.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.UpsertV.spec (GF := GF) := fun m γ R key v cb Q => by
  wp_start as ⟨#Hm, Hcb⟩
  iunfold isCMapV at Hm
  icases Hm with ⟨%n, %shs, Hm⟩
  iunfold cmapCore at Hm
  icases Hm with ⟨#Hn, #Hsl, %Hns, #Hinv, #Hshs⟩
  wp_auto_lc 1
  wp_method_call; wp_call
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
  wp_apply (wp_map_lookup2 (K := GoString) (V := GoInterface)) $$ [$HM] as HM
  wp_apply Hcb $$ [] as %res #Hres HQ
  · rcases hk : M !! key with _ | old
    · simp; itrivial
    · simp only [Option.isSome_some, _root_.decide_true, ite_true, Option.getD_some]
      iapply HR $$ %key %old %hk
  wp_apply (wp_mapInsert (K := GoString) (V := GoInterface)) $$ [$HM] as HM
  ihave HΦ := HΦ $$ HQ
  imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
  imod cmap_update γ (sint.nat n) shs _ p hp M (fun M => <[key := res]> M)
      (fun M => <[key := res]> M)
      (fun M => by rw [shardPart_insert, if_pos rfl])
      (fun j M hj => by rw [shardPart_insert, if_neg (Ne.symm hj)])
      (fun _ => iprop(Φ #res)) $$ [Hgi HΦ] with ⟨Hgi, %M', HΦ⟩
  · iframe Hinv Hgi
    imod HΦ with ⟨%M', Hview, Hcont⟩
    imodintro
    iexists M'
    iframe Hview
    iintro %HMi Hview
    iapply Hcont $$ [] Hview
    ipureintro
    apply upsert_old
    rw [HMi, lookup_shardPart_same]
  wp_method_call; wp_call
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HM Hgi]
  · inext
    iunfold shardP
    iexists _
    iframe HM Hgi
    iintro !> %k %v' %Hk
    by_cases hk : k = key
    · subst hk
      rw [GMap.lookup_insert_eq] at Hk; cases Hk; iexact Hres
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at Hk
      iapply HR $$ %k %v' %Hk
  iexact HΦ

theorem ConcurrentMap.Upsert.wp_proof (wp_UpsertV : ConcurrentMap.UpsertV.spec (GF := GF)) :
    ConcurrentMap.Upsert.spec (GF := GF) := fun m R key v cb Q => by
  wp_start_folded as ⟨#Hm, Hcb⟩
  iunfold isCMap at Hm
  icases Hm with ⟨%γ, #HmV, #Hold⟩
  iapply (wp_UpsertV m γ R key v cb (fun _ _ res => Q res)) $$ [Hcb] [HΦ]
  · iframe Hpkg HmV Hcb
  · iintro %ex %old %res HQ
    inext
    iapply cmapOld_au_pure γ (fun M => <[key := res]> M)
    iframe Hold
    iapply HΦ $$ HQ

end proof

end Perennial.github_com.orcaman.concurrent_map
