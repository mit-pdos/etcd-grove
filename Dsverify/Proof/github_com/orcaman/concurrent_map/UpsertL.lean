/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/UpsertL.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Upsert` with the key's binding stable during the callback (decision D18, G1; additive: the
strong `UpsertV.spec` and its users are unchanged).

`UpsertV.spec`'s callback gets only `R key old` (persistent) and the view only at the commit,
after the callback. A client whose invariant holds the view `cmapView γ M` with resources keyed
by `M`'s entries (the swift descriptors' `descInv`) cannot locate `key`'s entry during the
callback. `UpsertVL.spec` also gives the callback a **lock token** `cmapLocked γ key o t`
(`o = if ex then some old else none`): while it is held (the shard's write lock is held),
`key`'s binding in the view is `o` (`cmapLocked_lookup`, at any mask containing `cmapN`); the
callback returns the token with its result. The token is the write-locked shard's half of its
ghost variable (the library's), so nobody else changes `key`'s binding while it is out.

`t : CmapLock` names the locked shard (abstract to the client: it only passes `t` back).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.UpsertLDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

/-- `UpsertVL`, from the Goose code (`UpsertV.wp_proof`'s proof, the shard's ghost half lent to
the callback as the token). -/
theorem ConcurrentMap.UpsertVL.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.UpsertVL.spec (GF := GF) := fun m γ R key v cb Q => by
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
  wp_apply Hcb $$ [] [Hgi] as %res #Hres Htok HQ
  · rcases hk : M !! key with _ | old
    · simp; itrivial
    · simp only [Option.isSome_some, _root_.decide_true, ite_true, Option.getD_some]
      iapply HR $$ %key %old %hk
  · iapply cmapLocked_intro γ key _ (sint.nat n) shs p M hp (upsert_old _ _ rfl)
    iframe Hinv Hgi
  iunfold cmapLocked at Htok
  icases Htok with ⟨-, -, Hgi⟩
  wp_auto
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


end spec

end Perennial.github_com.orcaman.concurrent_map
