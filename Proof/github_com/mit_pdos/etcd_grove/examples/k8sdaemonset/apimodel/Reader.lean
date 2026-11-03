/-
**Read access to the model API server's state** (the DaemonSet run's cross-track contract,
`notes/k8s-daemonset-run/design.md`, "Who owns the API state"). Lean-first.

The clients' half of the server's state, `apiState γ σ`, is owned by whoever reasons about the
writes (in the DaemonSet run, S1's invariant). A client that only reads (an informer's list and
watch) needs not that owner's invariant but the right to fire a read's linearization point:

* `apiReader γ` (persistent): at any time, the current state's `apiState γ σ` can be had for one
  atomic step (mask `⊤` to `∅`, the typed clients' `List`/`Watch`/`Get` are logically atomic with
  inner mask `∅`) and must be given back **unchanged**. So a reader cannot change the state, and
  the owner's invariant (any `P σ` of the state) survives every read.

Laws:
* `apiReader_of_inv`: an invariant holding the state with any fact `P σ` gives read access (the
  owner's side: S1's invariant).
* `apiReader_past`: read access gives a past state (`pastSt`), e.g. to start an informer's
  invariant.
* `apiReader_read`: read access fires a read's atomic update (`<<{ ∀∀ σ, apiState γ σ }>> ... @@ ∅
  <<{ apiState γ σ }>>`), the state read a past state afterwards (`apiState_pastSt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Read access to the server's state** (persistent): see the file header. -/
def apiReader (γ : ApiNames) : IProp GF :=
  iprop(□ |={⊤, ∅}=> ∃ σ, apiState γ σ ∗ (apiState γ σ ={∅, ⊤}=∗ True))

instance apiReader_persistent (γ : ApiNames) : Persistent (apiReader (GF := GF) γ) := by
  unfold apiReader; infer_instance

instance apiState_timeless' (γ : ApiNames) (σ : St) : Timeless (apiState (GF := GF) γ σ) := by
  unfold apiState; infer_instance

/-- **The owner's side**: an invariant holding the state, with any fact `P σ` of it, gives read
access (a read gives the state back unchanged, so `P σ` is put back as it was). -/
theorem apiReader_of_inv (N : Namespace) (γ : ApiNames) (P : St → IProp GF) :
    inv N iprop(∃ σ, apiState γ σ ∗ P σ) ⊢ apiReader γ := by
  iintro #Hinv
  iunfold apiReader
  imodintro
  iinv Hinv with Hi Hclose
  haveI : Inhabited St := ⟨St.empty⟩
  ihave Hi := (later_exists (Φ := fun σ => iprop(apiState (GF := GF) γ σ ∗ P σ))).2 $$ Hi
  icases Hi with ⟨%σ, Hi⟩
  ihave ⟨>Hst, HP⟩ := later_sep.1 $$ Hi
  imod (fupd_mask_subseteq (E1 := ⊤ \ ↑N) (E2 := ∅) (by simp)) with Hback
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  imod Hback with -
  imod Hclose $$ [Hst HP] with -
  · inext; iexists σ; iframe
  imodintro
  itrivial

/-- **A past state from read access.** -/
theorem apiReader_past (γ : ApiNames) :
    apiReader γ ⊢ |={⊤}=> ∃ σ, pastSt (GF := GF) γ σ := by
  unfold apiReader
  iintro #Hr
  imod Hr with ⟨%σ, Hst, Hcl⟩
  iunfold apiState at Hst
  icases Hst with ⟨%H, Ha, %Hok⟩
  ihave #Hp := pastSt_of_auth γ _ H σ Hok $$ Ha
  imod Hcl $$ [Ha] with -
  · iunfold apiState; iexists H; iframe; ipureintro; exact Hok
  imodintro
  iexists σ
  iexact Hp

/-- The clients' half of the state gives its past state. -/
theorem apiState_pastSt (γ : ApiNames) (σ : St) :
    apiState (GF := GF) γ σ ⊢ apiState γ σ ∗ pastSt γ σ := by
  iintro Hst
  iunfold apiState at Hst
  icases Hst with ⟨%H, Ha, %Hok⟩
  ihave #Hp := pastSt_of_auth γ _ H σ Hok $$ Ha
  iframe #
  iunfold apiState; iexists H; iframe; ipureintro; exact Hok

/-- **A read's linearization point from read access**, the state read a past state after it. -/
theorem apiReader_read (γ : ApiNames) :
    apiReader γ ⊢ |={⊤, ∅}=> ∃ σ, apiState (GF := GF) γ σ ∗ (apiState γ σ ={∅, ⊤}=∗ pastSt γ σ) := by
  unfold apiReader
  iintro #Hr
  imod Hr with ⟨%σ, Hst, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  ihave ⟨Hst, #Hp⟩ := apiState_pastSt γ σ $$ Hst
  imod Hcl $$ Hst with -
  imodintro
  iexact Hp

end defs

end apimodel
end EtcdGrove
end Perennial
