/-
The witness's storage contract (2026-10-20, witness support, `notes/raft-witness.md`): what
`witness.go` assumes of the application's `WitnessStorage` and the `WitnessState`s it hands out
(interfaces raft does not implement: the trust boundary, as a premise of the witness's specs,
not an axiom).

The storage holds the witness's state; its ghost counterpart is an abstract `P σ` of the stored
state `σ` (W2's instance: `wGhost γ` of its protocol projection, `Protocol/Witness.lean`), which
only the storage owns, in an invariant of namespace `N`. A read (`GetWitnessState`) and a write
(`WitnessState.Update`, a compare-and-swap against the state read) are atomic: each runs a view
shift of the caller's on `P` at its linearization point (an atomic update reduced to what
`witness.go` needs, `P` being the storage's whole state):

- `GetWitnessState()`: a `WitnessState` of the state `σ` stored when it ran the caller's
  `P σ ={⊤ ∖ N}=∗ P σ ∗ Ψ σ` (a lower bound of the history, say: `wGhost_read`), or an error,
  the shift unrun;
- `ws.GetState()`: that state, read-only (not nil: `issues/raft-witness-getstate-nil.md`);
- `ws.Update(q)`: if the stored state is still `σ`, it is now `q`'s (`σ'`), the caller's
  `P σ ={⊤ ∖ N}=∗ P σ' ∗ Ψ` run (`wGhost_push`, `_write`, `_vote`, `_raise`); else an error
  (`ErrWitnessStateModified`, or another), the shift handed back.
-/
module

public import Proof.go_etcd_io.raft.v3.InvWitness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section storage
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `WitnessState` read at the stored state `σ`. -/
def isWState (sv : GoInterface) (N : Namespace) (P : WHS → IProp GF) (σ : WHS) : IProp GF :=
  iprop(∃ (j : GoInterfaceOk) (p : Loc),
    "%Hsv" ∷ ⌜sv = interface.ok j⌝ ∗
    "#Hp" ∷ whsRO p σ ∗
    "#HGetState" ∷ □ ({{ True }}
        (App (Val #(methods j.ty go!"GetState" j.v)) (Val #()))
      {{ RET #p; True }}) ∗
    "#HUpdate" ∷ □ (∀ (q : Loc) (σ' : WHS) (Ψ : IProp GF),
      {{ whsRO q σ' ∗ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Ψ) }}
        (App (Val #(methods j.ty go!"Update" j.v)) (Val #q))
      {{ (err : GoError), RET #err;
          (⌜err = interface.nil⌝ ∗ Ψ) ∨
          (⌜err ≠ interface.nil⌝ ∗ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Ψ)) }}))

instance isWState_persistent (sv : GoInterface) (N : Namespace) (P : WHS → IProp GF) (σ : WHS) :
    Persistent (isWState sv N P σ) := by
  unfold isWState; infer_instance

/-- The application's `WitnessStorage` (`WitnessConfig.Storage`), its stored state's ghost
counterpart `P`, in an invariant of namespace `N`. -/
def isWitnessStorage (s : GoInterface) (N : Namespace) (P : WHS → IProp GF) : IProp GF :=
  iprop(∃ (i : GoInterfaceOk),
    "%Hs" ∷ ⌜s = interface.ok i⌝ ∗
    "#HGet" ∷ □ (∀ (Ψ : WHS → IProp GF),
      {{ ∀ σ, P σ ={⊤ \ ↑N}=∗ P σ ∗ Ψ σ }}
        (App (Val #(methods i.ty go!"GetWitnessState" i.v)) (Val #()))
      {{ (sv : GoInterface) (err : GoError), RET (PairV #sv #err);
          (⌜err ≠ interface.nil⌝ ∗ (∀ σ, P σ ={⊤ \ ↑N}=∗ P σ ∗ Ψ σ)) ∨
          (⌜err = interface.nil⌝ ∗ ∃ σ, isWState sv N P σ ∗ Ψ σ) }}) ∗
    "#HClose" ∷ □ ({{ True }}
        (App (Val #(methods i.ty go!"Close" i.v)) (Val #()))
      {{ RET #(); True }}))

instance isWitnessStorage_persistent (s : GoInterface) (N : Namespace) (P : WHS → IProp GF) :
    Persistent (isWitnessStorage s N P) := by
  unfold isWitnessStorage; infer_instance

end storage

end EtcdGrove
end Perennial
