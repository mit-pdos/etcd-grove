/-
The definitions, specs and lemmas of `IterCbP.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbNDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section pind
variable [GooseExts]

/-- A pin's data: the shard count, the shards, the shard's index and entry, the fraction of its
ghost variable, and the shard's contents. -/
structure PinD where
  n : Nat
  shs : List (Loc × GName)
  i : Nat
  p : Loc × GName
  q : Qp
  Mi : GMap GoString GoInterface

end pind

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **A pinned entry** `k ↦ v` of the map with view `γ` (see the file header). -/
def cmapPin (γ : GName) (k : GoString) (v : GoInterface) (π : PinD) : IProp GF :=
  iprop(inv cmapN (cmapInv γ π.n π.shs) ∗ ghostVar π.p.2 π.q π.Mi ∗
    ⌜π.shs[π.i]? = some π.p ∧ π.Mi !! k = some v⌝)

end defs

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- With a pin, the client's view has the pinned entry. -/
theorem cmapPin_lookup (γ : GName) (k : GoString) (v : GoInterface) (π : PinD)
    (M : GMap GoString GoInterface) (E : CoPset) (hE : ↑cmapN ⊆ E) :
    cmapPin (GF := GF) γ k v π ∗ cmapView γ M ⊢
      |={E}=> ⌜M !! k = some v⌝ ∗ cmapPin γ k v π ∗ cmapView γ M := by
  iintro ⟨Hpin, Hview⟩
  iunfold cmapPin at Hpin
  icases Hpin with ⟨#Hinv, Hg, %Hp⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases (BigSepL.bigSepL_lookup_acc Hp.1).1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  ihave Hs := Hback $$ %π.p Hi
  rw [list_set_lookup_self _ _ _ Hp.1] at *
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  imodintro
  have hk := Hp.2
  rw [HeqI, lookup_shardPart] at hk
  split at hk
  · isplitr
    · ipureintro; exact hk
    isplitl [Hg]
    · iunfold cmapPin; iframe Hinv Hg; ipureintro; exact Hp
    iunfold cmapView; iexists _; iexact Hview
  · cases hk

end steps

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `IterCbVN` whose `fn` step also gets the entry's pin, given back (see the file header). -/
abbrev ConcurrentMap.IterCbVP.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (fn : GoFunc)
    (I : List (GMap GoString GoInterface) → List (GoString × GoInterface) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
      I [] [] ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
          I obs vis -∗
          |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
            (cmapView γ M ={∅, ⊤ \ ↑cmapN}=∗ I (obs ++ [M]) vis)) ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface))
          (k : GoString) (v : GoInterface) (π : PinD) (Φ : val → IProp GF),
          ⌜(∃ M, obs.getLast? = some M ∧ M !! k = some v) ∧ k ∉ vis.map Prod.fst⌝ -∗
          cmapPin γ k v π -∗ R k v -∗ I obs vis -∗
          ▷ (cmapPin γ k v π -∗ I obs (vis ++ [(k, v)]) -∗ Φ #()) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
    (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
  {{ RET #(); readerV m γ R ∗
      ∃ (n : Nat) (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
        cmapShards n ∗ I obs vis ∗ ⌜iterTrace n obs vis⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

end proof

end Perennial.github_com.orcaman.concurrent_map
