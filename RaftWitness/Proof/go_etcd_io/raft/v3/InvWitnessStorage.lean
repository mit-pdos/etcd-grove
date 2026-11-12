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
- `ws.GetState()`: that state, read-only, or nil for the zero state (`whsOpt`; fork `9ed005d46`
  reads a nil state as the zero state, `notes/raft-witness-vs-pr168/getstate-nil.md`);
- `ws.Update(q)`: if the stored state is still `σ`, it is now `q`'s (`σ'`), the caller's
  `P σ ={⊤ ∖ N}=∗ P σ' ∗ Ψ` run (`wGhost_push`, `_write`, `_vote`, `_raise`); else an error
  (`ErrWitnessStateModified`, or another), the shift handed back. The error is a pointer error
  (`IsNewError`: `errors.New`'s, as `ErrWitnessStateModified` is), which `Process` compares
  against `ErrWitnessStateModified` (2026-10-20, W3b: a comparison of interface values of the
  same dynamic type compares their values, which for a pointer is decidable).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section storage
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `WitnessState` read at the stored state `σ`. -/
def isWState (sv : GoInterface) (N : Namespace) (P : WHS → IProp GF) (σ : WHS) : IProp GF :=
  iprop(∃ (j : GoInterfaceOk) (p : Loc),
    "%Hsv" ∷ ⌜sv = interface.ok j⌝ ∗
    "#Hp" ∷ whsOpt p σ ∗
    "#HGetState" ∷ □ ({{ True }}
        (App (Val #(methods j.ty go!"GetState" j.v)) (Val #()))
      {{ RET #p; True }}) ∗
    "#HUpdate" ∷ □ (∀ (q : Loc) (σ' : WHS) (Ψ : IProp GF),
      {{ whsRO q σ' ∗ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Ψ) }}
        (App (Val #(methods j.ty go!"Update" j.v)) (Val #q))
      {{ (err : GoError), RET #err;
          (⌜err = interface.nil⌝ ∗ Ψ) ∨
          (⌜err ≠ interface.nil ∧ IsNewError err⌝ ∗ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Ψ)) }}))

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

/-! ### The witness proxy (2026-10-20, W3b)

`ownWitness w id s cq pv c h`: a `*witness` (one node's access to the shared witness): its
configuration (`id`, `storage`, `checkQuorum`, `preVote`) read-only, its cache `w.state` holding
`c` (`whsOpt`: nil before the first read), its last storage error `w.lastError`, `nil` iff `h`
(`isHealthy`). -/
def ownWitness (w : Loc) (id : w64) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool) :
    IProp GF :=
  iprop(∃ (p : Loc) (e : GoError),
    "#Hid" ∷ w.[witness, go!"id"] ↦□ id ∗
    "#Hstorage" ∷ w.[witness, go!"storage"] ↦□ s ∗
    "#HpreVote" ∷ w.[witness, go!"preVote"] ↦□ pv ∗
    "#HcheckQuorum" ∷ w.[witness, go!"checkQuorum"] ↦□ cq ∗
    "Hstate" ∷ w.[witness, go!"state"] ↦ p ∗ "#Hcache" ∷ whsOpt p c ∗
    "HlastError" ∷ w.[witness, go!"lastError"] ↦ e ∗ "%Hh" ∷ ⌜h = decide (e = interface.nil)⌝)

/-- What a round of `Process` on the state `σ` just read obliges the caller to give (`wStep`):
the answer's `Φr` when nothing is written; else the shift that the write runs at the storage's
linearization point, from `P σ` to the written state's, with the new cache's `Lb` and the
answer's `Φr`. -/
def wObl (id : w64) (cq pv : Bool) (N : Namespace) (P Lb : WHS → IProp GF)
    (Φr : Option WResp → IProp GF) (μ : WMsg) (σ : WHS) : IProp GF :=
  match wStep id cq pv σ μ with
  | (none, r) => Φr r
  | (some σ', r) => iprop(P σ ={⊤ \ ↑N}=∗ P σ' ∗ Lb σ' ∗ Φr r)

end storage

end EtcdGrove
end Perennial
