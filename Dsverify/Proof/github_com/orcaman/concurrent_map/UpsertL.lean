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

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option linter.unusedSectionVars false

section defs
variable [go_gctx : GoGlobalContext]

/-- The locked shard a lock token is about (the map's shard count and shards, the shard, its
ghost contents). -/
structure CmapLock where
  n : Nat
  shs : List (Loc × GName)
  p : Loc × GName
  Mi : GMap GoString GoInterface

variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

/-- **The lock token** of `key` in the map with view `γ`: `key`'s shard is write-locked (its
lock resource's half of the shard's ghost variable, at `t.Mi`), in which `key` is bound to `o`. -/
def cmapLocked (γ : GName) (key : GoString) (o : Option GoInterface) (t : CmapLock) :
    IProp GF :=
  iprop(inv cmapN (cmapInv γ t.n t.shs) ∗
    ⌜t.shs[shardOf t.n key]? = some t.p ∧ t.Mi !! key = o⌝ ∗
    ghostVar t.p.2 (1 : Qp).half t.Mi)

theorem cmapLocked_intro (γ : GName) (key : GoString) (o : Option GoInterface) (n : Nat)
    (shs : List (Loc × GName)) (p : Loc × GName) (Mi : GMap GoString GoInterface)
    (hp : shs[shardOf n key]? = some p) (ho : Mi !! key = o) :
    inv cmapN (cmapInv γ n shs) ∗ ghostVar p.2 (1 : Qp).half Mi ⊢
      cmapLocked (GF := GF) γ key o ⟨n, shs, p, Mi⟩ := by
  iintro ⟨#Hinv, Hg⟩
  iunfold cmapLocked
  iframe Hinv Hg
  ipureintro; exact ⟨hp, ho⟩

/-- While the lock token is held, `key`'s binding in the view is `o`. -/
theorem cmapLocked_lookup (E : CoPset) (hE : (↑cmapN : CoPset) ⊆ E) (γ : GName)
    (key : GoString) (o : Option GoInterface) (t : CmapLock) (M : GMap GoString GoInterface) :
    cmapLocked (GF := GF) γ key o t ∗ cmapView γ M ⊢
      |={E}=> cmapLocked γ key o t ∗ cmapView γ M ∗ ⌜M !! key = o⌝ := by
  iintro ⟨Hl, Hview⟩
  iunfold cmapLocked at Hl
  icases Hl with ⟨#Hinv, %Hp, Hg⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases (BigSepL.bigSepL_lookup_acc Hp.1).1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  ihave Hs := Hback $$ %t.p Hi
  rw [list_set_lookup_self _ _ _ Hp.1]
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  imodintro
  isplitl [Hg]
  · iunfold cmapLocked; iframe Hinv Hg; ipureintro; exact Hp
  isplitl [Hview]
  · iunfold cmapView; iexists _; iexact Hview
  ipureintro
  rw [← lookup_shardPart_same t.n M key, ← HeqI, Hp.2]

end defs

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `m.Upsert(key, value, cb)` as `UpsertV.spec`, and the callback also gets the lock token
`cmapLocked γ key (if ex then some old else none) t` (`key`'s binding in the view, stable while
the callback runs: `cmapLocked_lookup`), which it returns with its result. -/
abbrev ConcurrentMap.UpsertVL.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString)
    (v : GoInterface) (cb : GoFunc) (Q : Bool → GoInterface → GoInterface → IProp GF),
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMapV m γ R ∗
      (∀ (ex : Bool) (old : GoInterface) (t : CmapLock) (Ψ : val → IProp GF),
        (if ex then R key old else ⌜old = interface.nil⌝) -∗
        cmapLocked γ key (if ex then some old else none) t -∗
        ▷ (∀ res : GoInterface, □ R key res -∗
            cmapLocked γ key (if ex then some old else none) t -∗ Q ex old res -∗ Ψ #res) -∗
        WP (App (App (App (Val #cb) (Val #ex)) (Val #old)) (Val #v)) {{ Ψ }}) -∗
    (∀ (ex : Bool) (old res : GoInterface), Q ex old res -∗
      ▷ |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
        (⌜M !! key = if ex then some old else none⌝ -∗ cmapView γ (<[key := res]> M) -∗
          |={∅, ⊤ \ ↑cmapN}=> Φ #res)) -∗
    WP (App (App (App (Val #(methods ConcurrentMap.ty go!"Upsert" #m)) (Val #key)) (Val #v))
      (Val #cb)) {{ Φ }}

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

/-- `UpsertV` is a corollary (the callback drops the token's use). -/
theorem ConcurrentMap.UpsertV.of_UpsertVL (wp_UpsertVL : ConcurrentMap.UpsertVL.spec (GF := GF)) :
    ConcurrentMap.UpsertV.spec (GF := GF) := fun m γ R key v cb Q => by
  iintro %Φ ⟨Hpkg, #Hm, Hcb⟩ HΦ
  iapply (wp_UpsertVL m γ R key v cb Q) $$ [Hpkg Hcb] HΦ
  iframe Hpkg Hm
  iintro %ex %old %t %Ψ Hold Htok HΨ
  iapply Hcb $$ Hold
  inext
  iintro %res #Hres HQ
  iapply HΨ $$ Hres Htok HQ

theorem ConcurrentMap.wp_UpsertVL : ConcurrentMap.UpsertVL.spec (GF := GF) :=
  ConcurrentMap.UpsertVL.wp_proof ConcurrentMap.wp_GetShardV

end spec

end Perennial.github_com.orcaman.concurrent_map
