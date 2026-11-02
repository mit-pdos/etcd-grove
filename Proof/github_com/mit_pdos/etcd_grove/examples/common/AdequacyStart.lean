/- Lean-first (no Rocq counterpart).

# The examples' closed theorems, with the extensions' start resources (2026-10-31)

`Adequacy.lean`'s `init_adequate` drops the resources Perennial's `goose_adequacy` hands the
program for its extensions' initial states (`extsGlobalStart`, `extsLocalStart`): right for an
extension that has none (`trivialExt`), wrong for one whose program owns its initial state (the
durable state's files, `durableExt`). `init_adequate_start` is the same theorem, the body's WP
also taking those resources (`progOkS`), stated for any list of extensions. Generic in Perennial's
terms: a proposal for Perennial with `init_adequate` (`notes/perennial-changes.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **A program `init #() ;; body` whose body takes the resource `S`, proved** (at the instance
`hG`): `progOk0`, the body's WP also from `S` (the extensions' start resources, in
`init_adequate_start`). -/
def progOkS [hG : HeapGS .hasLC GF] (S : IProp GF) (init : val) (body : Expr) (φ : val → Prop) :
    Prop :=
  ∃ (getInit : GoString → IProp GF) (I : IProp GF),
    ({{ ownInitializing getInit }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getInit ∗ I }}) ∧
    (⊢ I -∗ threadTok -∗ S -∗ WP body @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})

/-- **A program's closed theorem over `goose_adequacy`, with its extensions' start resources**:
`init_adequate`, the body proved also from the extensions' resources of the initial state
(`extsGlobalStart g.globalWorld ∗ extsLocalStart σ.world`, at the instance's ghost state). -/
theorem init_adequate_start [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      progOkS (hG := heapWith hG lctx)
        iprop(extsGlobalStart (G := (heapWith hG lctx).goose_globalGS) g.globalWorld ∗
          extsLocalStart (L := (heapWith hG lctx).goose_localGS) σ.world) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply adequate_of_unrecovered
  refine goose_adequacy (GF := GF) (n + 1) (n + 2) _ σ g φ hφ Hinitg Hinitw ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  have Hp := Hprog hG HN HT
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC GF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  obtain ⟨getInit, I, Hinitwp, Hbody⟩ := Hp
  iintro Hg Hl Hgs Htok
  ihave Hown := (ownInitializing_of_empty getInit) $$ Hgs
  imodintro
  wp_apply Hinitwp $$ Hown as ⟨-, HI⟩
  iapply Hbody $$ HI Htok
  iframe

end adequacy

end EtcdGrove
end Perennial
