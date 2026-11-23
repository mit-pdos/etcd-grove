/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__Remove.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

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

theorem ConcurrentMap.RemoveV.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.RemoveV.spec (GF := GF) := fun m γ R key => by
  wp_start as #Hm
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
  wp_apply (wp_mapDelete (K := GoString) (V := GoInterface)) $$ [$HM] as HM
  imod lc_fupd_elim_later $$ Hlc1 HΦ with HΦ
  imod cmap_update γ (sint.nat n) shs _ p hp M (fun M => GMap.delete key M)
      (fun M => GMap.delete key M)
      (fun M => by rw [shardPart_delete, if_pos rfl])
      (fun j M hj => by rw [shardPart_delete, if_neg (Ne.symm hj)])
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
    rw [GMap.lookup_delete_Some] at Hk
    iapply HR $$ %k %v' %Hk.2
  iapply HΦ; itrivial

theorem ConcurrentMap.Remove.wp_proof (wp_RemoveV : ConcurrentMap.RemoveV.spec (GF := GF)) :
    ConcurrentMap.Remove.spec (GF := GF) := fun m R key => by
  wp_start_folded as #Hm
  iunfold isCMap at Hm
  icases Hm with ⟨%γ, #HmV, #Hold⟩
  iapply (wp_RemoveV m γ R key) $$ [] [HΦ]
  · iframe Hpkg HmV
  · inext
    iapply cmapOld_au γ (fun M => GMap.delete key M)
    iframe Hold
    iexact HΦ

end proof

end Perennial.github_com.orcaman.concurrent_map
