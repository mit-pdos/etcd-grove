/-
etcd's cache `notifier` (the end of `cache/demux.go`): the shared vocabulary of
`Spec/newNotifier.lean` and `Spec/notifier__*.lean`. Lean-first (no Rocq counterpart).

A `notifier` is a channel `ch` under a `sync.RWMutex`: `notify` (write lock) installs a fresh
channel and closes the previous one, `wait` (read lock) reads the current channel and blocks
until it is closed or its context is done. So `ch` is a sequence of close-to-broadcast
channels (Perennial's `ownBroadcastChan` idiom).

**The notification counter.** A monotone counter `γ.count` (`monoNat`) counts the `notify`
calls. The channel installed when the count is `k` broadcasts `notifierLb γ (k + 1)` (the
count is at least `k + 1`) when it is closed, which the next `notify` does after
incrementing the count. `wait` reads the channel at count `k ≥ k0` (the caller's lower
bound) and, if it returns `nil`, has received `notifierLb γ (k + 1)`: a `notify` happened
after the read.

**The lock invariant** `notifierLockInv n γ q` is the `RWMutex`'s fractional `P q`
(Perennial's guarded `ownRWMutex rw P`): a `q`-fraction of `n.ch`, of the counter, of a ghost
variable `γ.cur` naming the current channel and its broadcast ghost names
(`NotifierCur`), and `q/2` of the broadcast channel's "pending" token (the other `1/2` of a
pending broadcast channel is in its invariant; `notify` reassembles it under the write lock to
close the channel). `RWMutex` admits a bounded number of readers, so `RLock` and `Lock` need a
token (`notifierHandle`, an `ownRWMutex`), as the store's readers do; `newNotifier` returns
`actualMaxReaders` of them.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

/-- The ghost names of a `notifier`: the notification counter and the current channel. -/
structure NotifierNames where
  count : GName
  cur : GName

/-- The current channel of a `notifier`: the channel, its channel names and broadcast names,
and the notification count at which it was installed. -/
structure NotifierCur where
  ch : Loc
  γch : ChanNames
  γi : BroadcastInternalNames
  k : Nat

/-- The encoding of a `NotifierCur` (for `Pos.Countable`). -/
def NotifierCur.enc (c : NotifierCur) :
    Loc × (GName × GName × GName × GName × GName × w64) × GName × Nat :=
  (c.ch, (c.γch.stateName, c.γch.offerLockName, c.γch.offerParkedPropName,
    c.γch.offerParkedPredName, c.γch.offerContinuationName, c.γch.chanCap), c.γi.doneGn, c.k)

theorem NotifierCur.enc_inj : Function.Injective NotifierCur.enc := by
  rintro ⟨a, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c⟩, d⟩ ⟨a', ⟨b1', b2', b3', b4', b5', b6'⟩, ⟨c'⟩, d'⟩ h
  simp only [NotifierCur.enc, Prod.mk.injEq] at h
  obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ := h
  rfl

instance NotifierCur.countable : Pos.Countable NotifierCur :=
  .ofInjective (fun c => Pos.Countable.encode c.enc)
    (fun _ _ h => NotifierCur.enc_inj (Pos.encode_inj h))

theorem qp_half_add' (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `n.mu`. -/
abbrev notifierMuAddr (n : Loc) : Loc := structFieldRef notifier go!"mu" n

/-- The address of `n.ch`. -/
abbrev notifierChAddr (n : Loc) : Loc := structFieldRef notifier go!"ch" n

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- At least `k` notifications happened (persistent). -/
def notifierLb (γ : NotifierNames) (k : Nat) : IProp GF := monoNatLbOwn γ.count k

instance notifierLb_persistent (γ : NotifierNames) (k : Nat) :
    Persistent (notifierLb (GF := GF) γ k) := by
  unfold notifierLb; infer_instance

/-- The lock invariant `P q` of `n.mu` (see the module docstring). -/
def notifierLockInv (n : Loc) (γ : NotifierNames) (q : Qp) : IProp GF :=
  iprop(∃ c : NotifierCur,
    "Hcur" ∷ ghostVar γ.cur q c ∗
    "Hch" ∷ notifierChAddr n ↦{DFrac.own q} c.ch ∗
    "Hauth" ∷ monoNatAuthOwn γ.count q c.k ∗
    "#Hbc" ∷ isBroadcastChanInternal c.ch c.γch c.γi (notifierLb γ (c.k + 1)) ∗
    "Hpend" ∷ dghostVar c.γi.doneGn (.own q.half) false)

instance notifierLockInv_fractional (n : Loc) (γ : NotifierNames) :
    Fractional (notifierLockInv (GF := GF) n γ) where
  fractional q1 q2 := by
    have hch : ∀ l : Loc, (notifierChAddr n ↦{DFrac.own (q1 + q2)} l : IProp GF) ⊣⊢
        notifierChAddr n ↦{DFrac.own q1} l ∗ notifierChAddr n ↦{DFrac.own q2} l :=
      fun l => (typedPointsto_dfractional (GF := GF) _ l).dfractional (DFrac.own q1) (DFrac.own q2)
    have hcur := fun (c : NotifierCur) =>
      (ghostVar_fractional (GF := GF) γ.cur c).fractional q1 q2
    have hmono := fun (k : Nat) => (monoNatAuthOwn_fractional (GF := GF) γ.count k).fractional q1 q2
    have hpend := fun (g : GName) =>
      (dghostVar_fractional (GF := GF) g false).fractional q1.half q2.half
    refine ⟨?_, ?_⟩
    · iintro H
      unfold notifierLockInv
      iNamed H
      rw [qp_half_add'] at *
      icases (hcur c).1 $$ Hcur with ⟨Hc1, Hc2⟩
      icases (hch _).1 $$ Hch with ⟨Hl1, Hl2⟩
      icases (hmono _).1 $$ Hauth with ⟨Ha1, Ha2⟩
      icases (hpend _).1 $$ Hpend with ⟨Hp1, Hp2⟩
      isplitl [Hc1 Hl1 Ha1 Hp1]
      · iexists c; simp only [named]; iframe; iframe #
      · iexists c; simp only [named]; iframe; iframe #
    · iintro ⟨H1, H2⟩
      unfold notifierLockInv
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hcur1 Hcur2 gives % ⟨_, Heq⟩
      subst Heq
      iexists c
      simp only [named]
      isplitl [Hcur1 Hcur2]
      · iapply (hcur c).2; iframe
      isplitl [Hch1 Hch2]
      · iapply (hch _).2; iframe
      isplitl [Hauth1 Hauth2]
      · iapply (hmono _).2; iframe
      isplitr
      · iexact Hbc1
      rw [qp_half_add']
      iapply (hpend _).2; iframe

/-- A handle on the `notifier` `n` with ghost names `γ`: a token of `n.mu` (one of the
`RWMutex`'s bounded reader slots), which `wait` (`RLock`) and `notify` (`Lock`) need. There
is no separate persistent `isNotifier`: Perennial's guarded `RWMutex` spec keeps the mutex's
invariant in the token, and the notifier has nothing else that is fixed. -/
def notifierHandle (n : Loc) (γ : NotifierNames) : IProp GF :=
  sync.ownRWMutex (notifierMuAddr n) (notifierLockInv (hG := hG) n γ)

/-- What `wait(ctx)` returns: `nil` once a `notify` happened after it read the channel, so the
count is above the caller's lower bound `k0`; or a non-nil error once the context `s` is done
(`ContextClosed`, with its `PDone`). -/
def notifierWaitResult (γ : NotifierNames) (k0 : Nat) (s : context.ContextDesc (IProp GF))
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ notifierLb γ (k0 + 1)) ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn))

end defs

end EtcdGrove
end Perennial
