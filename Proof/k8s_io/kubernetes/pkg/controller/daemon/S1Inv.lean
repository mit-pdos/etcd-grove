/-
**S1's invariant, in Iris** (phase 5 of `notes/k8s-daemonset-plan.md`; restated in Stage 3 of the
autoverify run, `notes/k8s-daemonset-run/design.md`, "S1's invariant"). Lean-first.

**Two invariants.** The consistency store's abstract state and the work queue's tokens, which S1's
accounting needs, are allocated by `NewDaemonSetsController` (`NewConsistencyStore` allocates its
ghost names), after the informers (whose list-watch closures need read access to the API state)
and after the admin's node create. So:
* `apiInv γa γ` (allocated by `Main` right after `apimodel.NewServer`): the API state's clients'
  half `apiState γa σ` and one half of its mirror (`apiMirror γ σ`, a ghost variable of the same
  state). A read (the informers' list and watch, the checker's list) opens it alone and closes it
  unchanged; a write needs the mirror's other half, which `Main` holds until it allocates `s1Inv`,
  and `s1Inv` from then on.
* `s1Inv γ c` (allocated by `Main` after `NewDaemonSetsController`, before the controller runs and
  the admin's DaemonSet create): the mirror's other half and S1's bookkeeping over that state, for
  the controller's components `c` (its consistency store's state, its owner tokens' authority, its
  work queue's tokens).

**The sync token** `syncTok γ c o`: what the sync of owner `o` holds from its start to its end: the
consistency store's permission for `o` whole (`ownerTok c o 1`, which `EnsureReady(o)` needs and
whose fractions the create goroutines' `WroteAt`s take) and the owner's half of its bound
(`seenTok γ o L`: the other half is the invariant's, so the bound changes only with both, at the
sync's `EnsureReady`). The worker trades the work queue's `keyTok` of the owner's canonical key
(`ownerKey o`) for it at `processNextWorkItem`, inside `s1Inv` (for each registered owner,
`syncTok ∨ keyTok`; an owner is registered at its first sync), and trades it back before `Done`.

**The claims** (`claimTok γ o n v`, the create goroutine's for node `n`; `S1Steps.lean`'s `Claims`):
each claim in the invariant holds a fraction of the owner's `ownerTok`, so the holder of
`ownerTok c o 1` knows `o` has no claim: at a sync's start nothing of its owner is pending.

**The ambiguous create**: a create that commits and returns the timeout leaves its claim with the
pod pending and the claim's fraction of `ownerTok` in the invariant: the worker cannot reassemble
`ownerTok c o 1`, so `syncNodes` cannot give back `syncTok` (`syncNodes`' proof, the create
goroutine's ambiguous branch; `ambiguous_create_breaks_S1` shows no proof can: the next sync
duplicates the pod).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Steps
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.Defs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer consistency workqueue

/-! ## The ghost state and the invariants -/

/-- The ghost names of S1's invariant (allocated by `Main`). -/
structure S1Names where
  /-- the API state's mirror (a ghost variable: `apiInv`'s half and `s1Inv`'s) -/
  mirror : GName
  /-- the owners' bounds: owner ↦ a version the pod informer has reached and whether the owner
  is ready (halves: the invariant's, the sync token holder's) -/
  lb : GName
  /-- the claims: (owner, node) ↦ the claimant's pod, once created -/
  claim : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The API state's writers' half** (`Main`'s, then `s1Inv`'s). -/
def apiMirror (γ : S1Names) (σ : St) : IProp GF := ghostVar γ.mirror (1 : Qp).half σ

/-- The API invariant's namespace. -/
def apiN : Namespace := nroot.@"daemonset_api"

/-- **The API invariant**: the API state's clients' half and the mirror's readers' half. -/
def apiInv (γa : ApiNames) (γ : S1Names) : IProp GF :=
  inv apiN iprop(∃ σ : St, apiState γa σ ∗ ghostVar γ.mirror (1 : Qp).half σ)

instance apiInv_persistent (γa : ApiNames) (γ : S1Names) :
    Persistent (apiInv (GF := GF) γa γ) := by
  unfold apiInv; infer_instance

/-- **The owner's half of its bound and ready flag** `Lr`. -/
def seenTok (γ : S1Names) (o : Owner) (Lr : Nat × Bool) : IProp GF :=
  ghostMapElem γ.lb o (DFrac.own (1 : Qp).half) Lr

/-- **The sync token of owner `o`**: see the file header. -/
def syncTok (γ : S1Names) (c : DscComp) (o : Owner) : IProp GF :=
  iprop(ownerTok c o 1 ∗ ∃ Lr, seenTok γ o Lr)

/-- **A claim** of node `n` for owner `o` (the create goroutine's): `v` its pod, once created
(`S1Steps.lean`'s `Claims`). -/
def claimTok (γ : S1Names) (o : Owner) (n : GoString) (v : Option (Bool × Key × Nat)) :
    IProp GF :=
  ghostMapElem γ.claim (o, n) (DFrac.own 1) v

/-- **A registered owner's entry**: the invariant's half of its bound, a lower bound of the pod
informer's version, and its sync token or the work queue's token of its key. -/
def s1Entry (γ : S1Names) (c : DscComp) (o : Owner) (Lr : Nat × Bool) : IProp GF :=
  iprop(seenTok γ o Lr ∗ infRvLb c.podI.γi Lr.1 ∗ (syncTok γ c o ∨ keyTok c.γq.tq (ownerKey o)))

/-- **A claim's deposit**: a fraction of its owner's token. -/
def claimDep (c : DscComp) (on : Owner × GoString) : IProp GF :=
  iprop(∃ q, ownerTok c on.1 q)

/-- **S1's invariant's content**: the mirror's half at `σ`, the consistency store's state `M`,
the owner tokens' authority and the bounds `Lm` (each registered owner: the invariant's half of
its bound, a lower bound of the pod informer's version, and its sync token or the work queue's
token of its key), the claims `C` (each with a fraction of its owner's token), a lower bound `Ld`
of the DaemonSet informer's version, and `s1Ok`. -/
def s1Res (γ : S1Names) (c : DscComp) : IProp GF :=
  iprop(∃ (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool)) (C : Claims)
      (D : GMap Owner Unit) (Ld : Nat),
    apiMirror γ σ ∗ consState c.γc M ∗
    ghostMapAuth c.tok 1 D ∗ ⌜∀ o, (D !! o).isSome = (Lm !! o).isSome⌝ ∗
    ghostMapAuth γ.lb 1 Lm ∗
    ([∗map] o ↦ Lr ∈ Lm, s1Entry γ c o Lr) ∗
    ghostMapAuth γ.claim 1 C ∗ ([∗map] on ↦ _v ∈ C, claimDep c on) ∗
    infRvLb c.dsI.γi Ld ∗ ⌜s1Ok σ M Lm C Ld⌝)

/-- The invariant's namespace. -/
def s1N : Namespace := nroot.@"daemonset_s1"

/-- **S1's invariant.** -/
def s1Inv (γ : S1Names) (c : DscComp) : IProp GF := inv s1N (s1Res γ c)

instance s1Inv_persistent (γ : S1Names) (c : DscComp) : Persistent (s1Inv (GF := GF) γ c) := by
  unfold s1Inv; infer_instance

end defs

end dsctl
end EtcdGrove
end Perennial
