/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/RemoveL.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Remove` with the shard lock exposed (round 36; additive: `RemoveV.spec`, its proof, `Link.lean`
and every user are unchanged). Requested for the swift descriptor goroutine's retirement
(`r.cmdDescs.Remove(key)`, swift.go :1054; lifecycle table T16a), whose proof must refute that
the entry is lent to `stopDescs` (which holds the shard's **read** lock while its `IterCb`
callback runs, `IterCbVP`'s pin `cmapPin`).

`RemoveV.spec` is logically atomic: its commit runs with `cmapN` open and gives nothing about the
lock. `RemoveL.spec` instead runs a **client step** while the shard's write lock is held, before
the Go map's `delete`: the step gets the lock token `cmapLocked γ key o t` (Proof/cmap/UpsertL.lean;
`o` is `key`'s binding) and a later credit, at mask `⊤`, so it can open its own invariant and, in
it,
* refute a reader's pin on `key`: `cmapLocked_pin_false` (a write-locked shard and a read-locked
  one cannot coexist: the token's half, the invariant's half and the pin's fraction of the shard's
  ghost variable add up to more than 1);
* remove `key` from its view: `cmapLocked_delete` (the ghost delete; nobody can see the shard's
  contents meanwhile, the shard is locked), which turns the token into `cmapLocked γ key none
  (t.del key)`, the one the step returns.
The library then deletes the key from the Go map and unlocks with the deleted shard.

`cmapPin_split`: a pin halves (`π.half`), so `stopDescs` can deposit one half in its lend state
and keep the other for `cmapPin_lookup`; the deposited half is what `cmapLocked_pin_false`
refutes.

The two invariants (the lock token's and the pin's, possibly destructed from `isCMapV` at
different times) are identified through the client's view: the view's ghost variable records the
core `(n, shs)` (Proof/cmap/Defs.lean, `cmapInv`).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.UpsertLDefs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbPDefs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.RemoveLDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

end laws

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

/-- `RemoveL`, from the Goose code (`RemoveV.wp_proof`'s proof, the client's step in place of the
atomic update, with the shard's ghost half lent to it as the token). -/
theorem ConcurrentMap.RemoveL.wp_proof (wp_GetShardV : ConcurrentMap.GetShardV.spec (GF := GF)) :
    ConcurrentMap.RemoveL.spec (GF := GF) := fun m γ R key Q => by
  wp_start as ⟨#Hm, Hstep⟩
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
  ihave Htok := cmapLocked_intro γ key (M !! key) (sint.nat n) shs p M hp rfl $$ [Hgi]
  · iframe Hinv Hgi
  imod Hstep $$ %(M !! key) %_ Hlc1 Htok with ⟨Htok, HQ⟩
  iunfold cmapLocked at Htok
  simp only [CmapLock.del]
  icases Htok with ⟨-, -, Hgi⟩
  wp_apply (wp_mapDelete (K := GoString) (V := GoInterface)) $$ [$HM] as HM
  wp_method_call; wp_call
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HM Hgi]
  · inext
    iunfold shardP
    iexists _
    iframe HM Hgi
    iintro !> %k %v' %Hk
    rw [GMap.lookup_delete_Some] at Hk
    iapply HR $$ %k %v' %Hk.2
  iapply HΦ; iexact HQ

theorem ConcurrentMap.wp_RemoveL : ConcurrentMap.RemoveL.spec (GF := GF) :=
  ConcurrentMap.RemoveL.wp_proof ConcurrentMap.wp_GetShardV

end spec

end Perennial.github_com.orcaman.concurrent_map
