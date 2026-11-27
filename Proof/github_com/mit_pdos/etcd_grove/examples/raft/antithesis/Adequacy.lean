/- Lean-first (no Rocq counterpart).

# `raft/antithesis`: adequacy

`antithesis_adequate_of`: from `Main`'s spec at `antGF` (`antMainSpec`), every real execution of
`antithesisProgram` (the package's initialization, then `Main()`) from a fresh state with one thread,
of `n` steps with `n < antStepBound`, along which fewer than `antThreadBound` threads are live at once
(`RealNstepsBelow`): no thread is stuck and none has ended in a panic; the main thread's result, if it
has one, is `#()`. Over `init_adequate_below` (`examples/lib/etcdstart/Adequacy.lean`) as the trace
check's (`RaftTla/.../tracecheck/Adequacy.lean`): the trivial extension, the receipt bound `n + 1`
(so `antRunFits`, `receiptBound + 3 ≤ 2 ^ 61`, from `n + 4 ≤ 2 ^ 61`), the thread bound
`antThreadBound` (`ThreadBoundLe (2 ^ 31)`), the package's initialization (`Init.lean`, `PkgTable.lean`,
generated), and the main thread's token (`threadTok`, which `Main.spec` takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.PkgTable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.TopLevelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The ghost-state bundle -/

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

/-- The universal camera at slot 0. -/
@[instance_reducible] def antGF_allG : AllG antGF := ⟨⟨0, rfl⟩⟩

instance antGF_gooseGpreS : GooseGpreS antGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨antGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := antGF_allG

/-! ## The closed theorem, from `Main`'s spec -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s spec at `antGF`, for every `HeapGS`, every semantics and every package assumptions
(with, inside `Main.spec`, the thread bound and `antRunFits`): the hypothesis of
`antithesis_adequate_of`. -/
abbrev antMainSpec : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC antGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions],
    AntHarness.Main.spec (GF := antGF) (hG := hG)

/-- **The harness never fails**, from `Main`'s spec (see the file header). -/
theorem antithesis_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
    [hLog : log.NewModel]
    (wp_Main : antMainSpec)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < antStepBound) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow antThreadBound n ([antithesisProgram], ((σ, g) : CfgState)) κs
      (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine init_adequate_below (GF := antGF)
    github_com.mit_pdos.etcd_grove.examples.raft.antithesis.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ Hlctx Hinit Hthreads antThreadBound n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC antGF := heapWith hG lctx
  haveI : ThreadBoundLe antGF (2 ^ 31) := ⟨Nat.le_of_eq HT⟩
  have Hfits : AntHarness.antRunFits antGF := by
    unfold AntHarness.antRunFits; unfold antStepBound at Hn; rw [HN]; omega
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.raft.antithesis.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.raft.antithesis.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg Htok
  wp_apply (wp_Main Hfits) $$ [Hpkg Htok]
  · iframe #
    iexact Htok
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
