/-
`pkg/wait`'s `WaitTime` (`wait_time.go`: the applied index's waiters, the server's `applyWait`):
the contract `isWaitTime` and the `*timeList`'s invariant `isTimeList`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).

**The contract** (`isWaitTime wt P`, persistent), for a predicate `P` of deadlines (the server's:
`appliedAtLeast γr`):
* `Wait(d)` returns a channel that is closed, never sent on, whose close tells some `Q` from which
  `P d` follows (`□ (Q -∗ P d)`): `Wait` returns the package-wide `closec` (closed in `init`, with
  nothing: `Q = True`) when `d` is already triggered, then `P d` holds already; or a channel of the
  deadline `d`, closed with `P d` by a later `Trigger`;
* `Trigger(d)` takes `□ P d` and closes the channels of every deadline at most `d`.

**The package's `closec`** (`waitClosecInit`): the global `closec` holds a channel closed by the
package's `init`, never sent on, an invariant keeping it `Closed []` (as Perennial's
`context.isClosedchanInit`). Since D19r (D), 2026-10-18, the package's fact (`closecClosed`),
proved by its initializer (`init` closes `closec`, Go never writes it afterwards); until then a
broadcast channel, which needs later credits the package facts' instances do not have, so a
premise of `NewTimeList`.

**The `*timeList`** (`isTimeList tl P`): the mutex `tl.l` over `tl.lastTriggerDeadline` and the map
`tl.m` (the field written once, by `NewTimeList`), with `□ P` of the last trigger's deadline and, per
deadline `d` in the map, a pending broadcast channel with content `P d`; `P` is monotone downward
(`□ (∀ d d', ⌜d' ≤ d⌝ -∗ P d -∗ P d')`), so `□ P last` gives `P d` for every `d ≤ last`.

**A trigger's deadline may go down** (`Trigger` sets `lastTriggerDeadline = d` even if `d` is
smaller than the last): then a `Wait(d')` with `d < d' ≤` the old deadline returns a fresh channel
(released by a later `Trigger` at `d'` or more), although `d'` was triggered. No premise is needed
for the contract (the lock invariant only keeps `□ P last`, which `Trigger(d)`'s `□ P d` gives), and
the API's documentation (a channel "will be triggered when Trigger is called with a deadline that is
later than or equal to the one it is waiting for") does not promise more; the server's
`ep.appliedi` only grows.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.wait
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `tl.l`. -/
abbrev tlLockAddr (tl : Loc) : Loc := structFieldRef wait.timeList go!"l" tl
/-- The address of `tl.lastTriggerDeadline`. -/
abbrev tlLastAddr (tl : Loc) : Loc := structFieldRef wait.timeList go!"lastTriggerDeadline" tl
/-- The address of `tl.m`. -/
abbrev tlMapAddr (tl : Loc) : Loc := structFieldRef wait.timeList go!"m" tl

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A channel closed (never sent on) whose close tells `Q`** (persistent; a receiver's view):
Perennial's broadcast idiom (the read loop's `bcastChan`), or (D19r (D), 2026-10-18) a channel an
invariant keeps closed with `□ Q` already known (the package's `closec`; as Perennial's
`context.isContextDone`'s second case). -/
def waitBcast (ch : Loc) (Q : IProp GF) : IProp GF :=
  iprop((∃ γ : ChanNames, ownBroadcastChan ch γ Q .Unknown) ∨
    (∃ γ : ChanNames, isChan ch γ Unit ∗
      inv _root_.Perennial.context.closedchanN (ownChan γ Unit (.Closed [])) ∗ □ Q))

instance waitBcast_persistent (ch : Loc) (Q : IProp GF) : Persistent (waitBcast ch Q) := by
  unfold waitBcast; infer_instance

/-- **`closec` is closed** (persistent; see the file header): the package's fact (D19r (D),
2026-10-18; until then a broadcast channel, kept out of the fact, a premise of `NewTimeList`). -/
def waitClosecInit : IProp GF :=
  iprop(∃ (ch : Loc) (γ : ChanNames), globalAddr wait.closec ↦□ ch ∗ isChan ch γ Unit ∗
    inv _root_.Perennial.context.closedchanN (ownChan γ Unit (.Closed [])))

instance waitClosecInit_persistent : Persistent (waitClosecInit (GF := GF)) := by
  unfold waitClosecInit; infer_instance

/-- `closec` is closed, from the package's fact. -/
theorem waitClosecInit_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ⊢ waitClosecInit := by
  iintro #Hp
  ihave Hf : (go_etcd_io.etcd.pkg.v3.wait.closecClosed : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  iunfold go_etcd_io.etcd.pkg.v3.wait.closecClosed at Hf
  iunfold waitClosecInit
  iexact Hf

/-- **`P` is monotone downward** (persistent). -/
def waitMono (P : w64 → IProp GF) : IProp GF :=
  iprop(□ (∀ (d d' : w64), ⌜uint.Z d' ≤ uint.Z d⌝ -∗ P d -∗ P d'))

instance waitMono_persistent (P : w64 → IProp GF) : Persistent (waitMono P) := by
  unfold waitMono; infer_instance

/-- **The lock invariant of `tl.l`**, with the map `mref` (see the file header): the last
trigger's deadline, with `□ P` of it, and the map's channels, each pending with content `P d`. -/
def timeListR (tl mref : Loc) (P : w64 → IProp GF) : IProp GF :=
  iprop(∃ (last : w64) (M : GMap w64 Loc),
    tlLastAddr tl ↦ last ∗ ownMap mref (DFrac.own 1) M ∗ □ P last ∗
    [∗map] d ↦ ch ∈ M, ∃ γ : ChanNames, ownBroadcastChan ch γ (P d) .Pending)

/-- **The `*timeList` `tl`** (persistent; `NewTimeList`'s result): its map field (read-only), its
mutex with the lock invariant, `P` monotone downward, `closec` closed. -/
def isTimeList (tl : Loc) (P : w64 → IProp GF) : IProp GF :=
  iprop(∃ mref : Loc, tlMapAddr tl ↦□ mref ∗ sync.isMutex (tlLockAddr tl) (timeListR tl mref P) ∗
    waitMono P ∗ waitClosecInit)

instance isTimeList_persistent (tl : Loc) (P : w64 → IProp GF) :
    Persistent (isTimeList tl P) := by
  unfold isTimeList; infer_instance

/-- **The `WaitTime` interface value `wt`** (persistent; see the file header). -/
def isWaitTime (wt : GoInterface) (P : w64 → IProp GF) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜wt = GoInterface.ok wi⌝ ∗
    □ (∀ d : w64, {{ True }} (App (Val #(methods wi.ty go!"Wait" wi.v)) (Val #d))
      {{ (ch : Loc), RET #ch; ∃ Q : IProp GF, waitBcast ch Q ∗ □ (Q -∗ P d) }}) ∗
    □ (∀ d : w64, {{ □ P d }} (App (Val #(methods wi.ty go!"Trigger" wi.v)) (Val #d))
      {{ RET #(); True }}))

instance isWaitTime_persistent (wt : GoInterface) (P : w64 → IProp GF) :
    Persistent (isWaitTime wt P) := by
  unfold isWaitTime; infer_instance

end defs

end EtcdGrove
end Perennial
