/-
**The crash deployment's stable machines** (hraft_robust R7): the orchestrator's and the clients'
obligations in the crash bridge (`Net.StableBootWp`, `Net/Statement/NetFsBridge.lean`), over the net and
file extensions (`kvraftExts`), from the same boots and `main` specs as the no-crash deployment's
(`wp_bootR`): a command's boot program `bootFs init main` (`TopLevelCrashDefs.lean`) from its
first-run boot and its `main`'s spec (`wp_bootFs`), and `StableBootWp` from such a WP at every heap of
the statement's Go context (`stableBootWp_of`): the file extension's start resources and the main
thread's token are dropped (the orchestrator and the clients use no file). The commands' own
instances are applied in `TopLevelRobustness.lean`, over the kit's links.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.StartCrash
public import Net.Statement.NetFsBridgeT

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net NetFs

namespace github_com.hashicorp.raft.examples.hraftnet

attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExtsInterp kvraftExts_hasNet
  kvraftExts_hasFs GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program over `kvraftExts`, from its first-run boot (from the empty package
state, it returns the boot resource `R`) and a spec of its `main` with precondition `P ∗ R`
(`wp_bootR`, for `bootFs`). -/
theorem wp_bootFs [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (main pkg : GoString) [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (R : IProp GF)
    (Hinit : {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg ∗ R }})
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P ∗ R }}
        (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (bootFs init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold bootFs
  wp_apply Hinit $$ [Hgs] as ⟨-, #Hpkg, HR⟩
  · iexact Hgs
  wp_pures
  wp_apply Hf $$ [HP HR]
  · iframe
  ipureintro; rfl

/-- **A stable machine's obligation from its boot's WP**: `StableBootWp e σ Q` when, at every heap
over `G` whose Go context is `lctx` (given by its components), `e` is safe from `Q` and the empty
package state. -/
theorem stableBootWp_of [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr)
    (σ : state) (Q : IProp GF)
    (H : ∀ (Lexts : Exts.LocalGS _ GooseInterp.interps GF) (Lheap : NaHeapGS Loc val GF)
        (Lgs : GoStateGS GF) (Lthr : ThreadGS GF) (Lcr : CrashGS GF),
      letI : HeapGS .hasLC GF := ⟨G, ⟨Lexts, lctx, Lheap, Lgs, Lthr, Lcr⟩⟩
      Q ⊢ ownGoState ∅ -∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}) :
    StableBootWp e σ Q := by
  intro L hL
  obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
  dsimp only at hL
  subst hL
  iintro HQ - Hgs -
  imodintro
  iapply H Lexts Lheap Lgs Lthr Lcr $$ HQ Hgs

end boot

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
