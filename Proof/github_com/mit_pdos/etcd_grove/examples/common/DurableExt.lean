/- Lean-first (no Rocq counterpart).

# The examples with durable files: the closed list `[durableExt]` (2026-10-31)

An example that keeps files (`examples/kvdurable`, through the `durable` package) runs against the
durable-state extension alone (`durableExts`, `GooseLang/Ext/Durable/Specs.lean`), as the others
against `trivialExt` (`TrivialExt.lean`). This file closes it for them:

* `durableGF`: a ghost-state bundle for `[durableExt]` (kvreconf's `kvrGF` for `trivialExt`: the
  universal camera `AllG` at slot 0, which also serves the extension's ghost variable of the files,
  then invariants, credits, the heap, prophecies and package state, and iris-lean's non-atomic
  invariants `NaInvG` at slot 11, for porcupine's results), with its `GooseGpreS`;
* `durable_localStart`: the extensions' local start resources are the program's half of the
  initial files (`durableOwn`);
* `durable_init_adequate`: `init_adequate_start` (`AdequacyStart.lean`) for `[durableExt]`: the
  program's body is proved from `durableOwn` of the initial files, whatever they are (the
  extension's `initP` is `True`; a closed theorem assumes what it needs of them).

No crash: the semantics' crashes (`ExtSemantics.crash`) are not taken by these theorems
(`goose_adequacy` is crash-free); a program's crashes are its own (kvdurable's `Replica.crash`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.AdequacyStart
public import GooseLang.Ext.Durable.Specs
public import Iris.Instances.Lib.NaInvariants

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] durableExts durableExtsSemantics durableExtsInterp durableExts_hasExt

/-! ## The ghost-state bundle -/

/-- The functors (kvreconf's `kvrGF`): the universal camera (`AllG`) at slot 0, then invariants,
later credits, GooseLang's heap, prophecies and package state, and iris-lean's non-atomic
invariants at slot 11. Every other slot is the unit functor. -/
def durableGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0 (not an instance: under a `HeapGS` the `AllG` is the one
it carries, `GooseGlobalGS.gooseAllG`). -/
@[instance_reducible] def durableGF_allG : AllG durableGF := ⟨⟨0, rfl⟩⟩

/-- The ghost state for `[durableExt]`: the extension's (`DurableGpreS`: a ghost variable) in the
universal camera. -/
instance durableGF_gooseGpreS : GooseGpreS durableGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨durableGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := durableGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11. -/
instance durableGF_naInvG : NaInvG durableGF := ⟨⟨11, rfl⟩⟩

/-! ## The start resources and the closed theorem -/

section adequacy
variable [GoGlobalContext] [go.IntoValInj GoString] {GF : BundledGFunctors}

/-- **The start resources of `[durableExt]`** are the program's half of the initial files. -/
theorem durable_localStart [L : GooseLocalGS GF] (w : ExtsLocalState exts) :
    extsLocalStart (GF := GF) w ⊢ durableOwn (L := L) (extLocal durableExt w) :=
  sep_elim_left

/-- **A program with durable files, its closed theorem** (`init_adequate_start` for
`[durableExt]`): every real execution of `init #() ;; body` from a fresh state with one thread,
of `n` steps, whose body is proved from the program's half of the initial files
(`extLocal durableExt σ.world`): if the main thread has finished, its result is in `φ`; no thread
is stuck; no thread has ended in a panic. -/
theorem durable_init_adequate [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      progOkS (hG := heapWith hG lctx)
        (durableOwn (L := (heapWith hG lctx).goose_localGS) (extLocal durableExt σ.world))
        init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine init_adequate_start (GF := GF) init body φ hφ σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit
    Hthreads n κs t2 σ2 Hsteps ?_
  intro hG HN HT
  obtain ⟨getInit, I, Hinitwp, Hbody⟩ := Hprog hG HN HT
  refine ⟨getInit, I, Hinitwp, ?_⟩
  iintro HI Htok ⟨-, Hl⟩
  iapply Hbody $$ HI Htok
  iapply durable_localStart (L := (heapWith hG lctx).goose_localGS) σ.world $$ Hl

end adequacy

end EtcdGrove
end Perennial
