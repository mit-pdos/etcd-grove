/-
The definitions, specs and lemmas of `UpsertL.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
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

end spec

end Perennial.github_com.orcaman.concurrent_map
