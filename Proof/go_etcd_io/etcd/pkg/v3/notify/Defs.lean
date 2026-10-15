/-
etcd's `pkg/notify.Notifier` (`notify.go`): the shared vocabulary of
`Spec/go_etcd_io/etcd/pkg/v3/notify/Notifier__*.lean`. Lean-first (no Rocq counterpart).

A `Notifier` is a channel `n.channel` under a `sync.RWMutex`: `Notify` (write lock) installs a
fresh channel and, after unlocking, closes the previous one; `Receive` (read lock) returns the
current channel. So `n.channel` is a sequence of close-to-broadcast channels (Perennial's
`ownBroadcastChan` idiom), as the cache's `notifier` (`cache/v3/InvNotifier.lean`), whose
broadcast here carries nothing (`True`: no caller in the proofs waits on it).

**The lock invariant** `notifyLockInv n γ q` is the `RWMutex`'s fractional `P q`: a
`q`-fraction of `n.channel`, of a ghost variable `γ` naming the current channel and its
broadcast ghost names (`NotifyCur`), and `q/2` of the current broadcast channel's "pending"
token (the other `1/2` of a pending broadcast channel is in its invariant); `Notify` takes the
whole token out under the write lock, installs the new channel, and closes the old one after
unlocking with it. `isNotifier n` (persistent) is the mutex's writer guard
(`isRWMutexGuard`): any number of `Notify` callers, with no reader slot.

**A reader** (`notifyReader n`, 2026-10-13, the request path's unit 4b): `Receive` read-locks the
mutex, so each caller holds a reader slot (`sync.ownRWMutex`; Perennial's `RWMutex` admits a
bounded number of readers); `NewNotifier` returns them with the writer guard. `Receive` returns
the current channel, a broadcast channel with no content (`notifyChan`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.notify
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

/-- The current channel of a `Notifier`: the channel, its channel names and broadcast names. -/
structure NotifyCur where
  ch : Loc
  γch : ChanNames
  γi : BroadcastInternalNames

/-- The encoding of a `NotifyCur` (for `Pos.Countable`). -/
def NotifyCur.enc (c : NotifyCur) :
    Loc × (GName × GName × GName × GName × GName × w64) × GName :=
  (c.ch, (c.γch.stateName, c.γch.offerLockName, c.γch.offerParkedPropName,
    c.γch.offerParkedPredName, c.γch.offerContinuationName, c.γch.chanCap), c.γi.doneGn)

theorem NotifyCur.enc_inj : Function.Injective NotifyCur.enc := by
  rintro ⟨a, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c⟩⟩ ⟨a', ⟨b1', b2', b3', b4', b5', b6'⟩, ⟨c'⟩⟩ h
  simp only [NotifyCur.enc, Prod.mk.injEq] at h
  obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := h
  rfl

instance NotifyCur.countable : Pos.Countable NotifyCur :=
  .ofInjective (fun c => Pos.Countable.encode c.enc)
    (fun _ _ h => NotifyCur.enc_inj (Pos.encode_inj h))

theorem notify_qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `n.mu`. -/
abbrev notifyMuAddr (n : Loc) : Loc := structFieldRef notify.Notifier go!"mu" n

/-- The address of `n.channel`. -/
abbrev notifyChAddr (n : Loc) : Loc := structFieldRef notify.Notifier go!"channel" n

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The lock invariant `P q` of `n.mu` (see the module docstring). -/
def notifyLockInv (n : Loc) (γ : GName) (q : Qp) : IProp GF :=
  iprop(∃ c : NotifyCur,
    "Hcur" ∷ ghostVar γ q c ∗
    "Hch" ∷ notifyChAddr n ↦{DFrac.own q} c.ch ∗
    "#Hbc" ∷ isBroadcastChanInternal c.ch c.γch c.γi iprop(True) ∗
    "Hpend" ∷ dghostVar c.γi.doneGn (.own q.half) false)

instance notifyLockInv_fractional (n : Loc) (γ : GName) :
    Fractional (notifyLockInv (GF := GF) n γ) where
  fractional q1 q2 := by
    have hch : ∀ l : Loc, (notifyChAddr n ↦{DFrac.own (q1 + q2)} l : IProp GF) ⊣⊢
        notifyChAddr n ↦{DFrac.own q1} l ∗ notifyChAddr n ↦{DFrac.own q2} l :=
      fun l => (typedPointsto_dfractional (GF := GF) _ l).dfractional (DFrac.own q1) (DFrac.own q2)
    have hcur := fun (c : NotifyCur) =>
      (ghostVar_fractional (GF := GF) γ c).fractional q1 q2
    have hpend := fun (g : GName) =>
      (dghostVar_fractional (GF := GF) g false).fractional q1.half q2.half
    refine ⟨?_, ?_⟩
    · iintro H
      unfold notifyLockInv
      iNamed H
      rw [notify_qp_half_add] at *
      icases (hcur c).1 $$ Hcur with ⟨Hc1, Hc2⟩
      icases (hch _).1 $$ Hch with ⟨Hl1, Hl2⟩
      icases (hpend _).1 $$ Hpend with ⟨Hp1, Hp2⟩
      isplitl [Hc1 Hl1 Hp1]
      · iexists c; simp only [named]; iframe; iframe #
      · iexists c; simp only [named]; iframe; iframe #
    · iintro ⟨H1, H2⟩
      unfold notifyLockInv
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
      isplitr
      · iexact Hbc1
      rw [notify_qp_half_add]
      iapply (hpend _).2; iframe

/-- `n` is a `Notifier` (persistent): its mutex's writer guard, with the lock invariant. -/
def isNotifier (n : Loc) : IProp GF :=
  iprop(∃ γ : GName, sync.isRWMutexGuard (notifyMuAddr n) (notifyLockInv (hG := hG) n γ))

instance isNotifier_persistent (n : Loc) : Persistent (isNotifier (GF := GF) n) := by
  unfold isNotifier; infer_instance

/-- **A reader slot of `n.mu`** (not persistent; `Receive`'s). -/
def notifyReader (n : Loc) : IProp GF :=
  iprop(∃ γ : GName, sync.ownRWMutex (notifyMuAddr n) (notifyLockInv (hG := hG) n γ))

/-- **A channel `Receive` returned** (persistent): closed (by a later `Notify`), never sent on, with
no content (Perennial's broadcast idiom, a receiver's view). -/
def notifyChan (ch : Loc) : IProp GF :=
  iprop(∃ γ : ChanNames, ownBroadcastChan ch γ iprop(True) .Unknown)

instance notifyChan_persistent (ch : Loc) : Persistent (notifyChan (GF := GF) ch) := by
  unfold notifyChan; infer_instance

end defs

end EtcdGrove
end Perennial
