/-
etcd's cache `ready` (`cache/ready.go`): the shared vocabulary of `Spec/newReady.lean` and
`Spec/ready__*.lean`. Lean-first (no Rocq counterpart).

`ready` is a boolean `isReady` under a `sync.Mutex`, with a channel `stateCh` that is closed
on every change of the boolean and immediately replaced by a fresh one (a sequence of
close-to-broadcast channels, Perennial's `ownBroadcastChan`).

**The epoch ghost.** A monotone counter `γ.epoch` (`monoNat`) counts the changes of
`isReady`: it starts at `0` with `isReady = false` and `Set`/`Reset` increment it exactly
when they flip the boolean, so the boolean in epoch `e` is `readyParity e` (`e` odd). The
lock invariant `readyLockInv` holds the authoritative counter `e`, the two fields, and the
current channel as a pending broadcast channel whose broadcast proposition is
`readyEpochLb γ (e + 1)`: whoever receives from the channel of epoch `e` (it is closed when
the epoch ends) learns that epoch `e + 1` has started. `readyEpochLb γ e` (persistent) is a
lower bound on the epoch; the readers' specs (`Ready`, `waitForState`) return a state
(`readySeen`) at an epoch at least the caller's lower bound.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

/-- The ghost names of a `ready`: the epoch counter. -/
structure ReadyNames where
  epoch : GName

/-- The value of `isReady` in epoch `e`: `false` in epoch `0`, flipped by every change. -/
def readyParity (e : Nat) : Bool := e % 2 == 1

theorem readyParity_succ (e : Nat) : readyParity (e + 1) = !readyParity e := by
  unfold readyParity
  rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h, Nat.add_mod]

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `r.mu`. -/
abbrev readyMuAddr (r : Loc) : Loc := structFieldRef ready go!"mu" r

/-- The address of `r.isReady`. -/
abbrev readyIsReadyAddr (r : Loc) : Loc := structFieldRef ready go!"isReady" r

/-- The address of `r.stateCh`. -/
abbrev readyStateChAddr (r : Loc) : Loc := structFieldRef ready go!"stateCh" r

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The epoch of the `ready` with names `γ` is at least `e` (persistent). -/
def readyEpochLb (γ : ReadyNames) (e : Nat) : IProp GF := monoNatLbOwn γ.epoch e

instance readyEpochLb_persistent (γ : ReadyNames) (e : Nat) :
    Persistent (readyEpochLb (GF := GF) γ e) := by
  unfold readyEpochLb; infer_instance

/-- The lock invariant of `r.mu`: `isReady` is `readyParity e` in the current epoch `e`, and
`stateCh` is a pending broadcast channel that will announce epoch `e + 1`. -/
def readyLockInv (r : Loc) (γ : ReadyNames) : IProp GF :=
  iprop(∃ (b : Bool) (ch : GoChan) (γch : ChanNames) (e : Nat),
    "HisReady" ∷ readyIsReadyAddr r ↦ b ∗
    "HstateCh" ∷ readyStateChAddr r ↦ ch ∗
    "Hch" ∷ ownBroadcastChan ch γch (readyEpochLb γ (e + 1)) .Pending ∗
    "Hauth" ∷ monoNatAuthOwn γ.epoch 1 e ∗
    "%Hb" ∷ ⌜b = readyParity e⌝)

/-- `r` is a `*ready` with ghost names `γ` (persistent): its mutex guards `readyLockInv`. -/
def isReady (r : Loc) (γ : ReadyNames) : IProp GF :=
  sync.isMutex (readyMuAddr r) (readyLockInv r γ)

instance isReady_persistent (r : Loc) (γ : ReadyNames) : Persistent (isReady (GF := GF) r γ) := by
  unfold isReady; infer_instance

/-- The `ready` was in state `b` in some epoch at least `e0`, which it reached (a lower bound
for it). -/
def readySeen (γ : ReadyNames) (e0 : Nat) (b : Bool) : IProp GF :=
  iprop(∃ e, readyEpochLb γ e ∗ ⌜e0 ≤ e ∧ readyParity e = b⌝)

instance readySeen_persistent (γ : ReadyNames) (e0 : Nat) (b : Bool) :
    Persistent (readySeen (GF := GF) γ e0 b) := by
  unfold readySeen; infer_instance

/-- The triple of `waitForState`'s `pred` closure: called with the lock held (the caller has
the `isReady` field), it returns `P b` for the field's value `b`. `WaitReady` passes
`func() bool { return r.isReady }` (`P = id`), `WaitNotReady` its negation (`P = not`). -/
def readyPredSpec (r : Loc) (pred : GoFunc) (P : Bool → Bool) : IProp GF :=
  iprop(∀ b : Bool,
    {{ readyIsReadyAddr r ↦ b }} (App (Val #pred) (Val #())) {{ RET #(P b); readyIsReadyAddr r ↦ b }})

instance readyPredSpec_persistent (r : Loc) (pred : GoFunc) (P : Bool → Bool) :
    Persistent (readyPredSpec (GF := GF) r pred P) := by
  unfold readyPredSpec; infer_instance

/-- What `waitForState(ctx, pred)` returns: `nil` after it saw, under the lock, a state
satisfying `P` in an epoch at least the caller's lower bound `e0`; or a non-nil error, and
then the context `s` is done (`ContextClosed`, with its `PDone`). (It returns `ctx.Err()` in
both cases, so a done context can hide an observed state.) -/
def readyWaitResult (γ : ReadyNames) (e0 : Nat) (s : context.ContextDesc (IProp GF))
    (P : Bool → Bool) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ b, readySeen γ e0 b ∗ ⌜P b = true⌝) ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn))

end defs

end EtcdGrove
end Perennial
