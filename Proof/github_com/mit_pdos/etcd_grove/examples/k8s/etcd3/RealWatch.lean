/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B5: the driver's watch check implies `ValidateWatch` (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B5. A watch the driver's check accepts (`watchOkL`, at the
configuration `h` of its linearization point) is accepted by upstream's `WatchValidator`
(`validateWatchL`) on the events `realCheck` gives it (`realEventsL`, D7g-2/3), against a replay
`R` that agrees with `h` from the seeded revision `s0` on (`ReplayAt`, B3b).

The received events are the store's `watch.Event`s (`REv`); the driver's own check reads them as
`toWEvent` maps them (`toWEvL`), encoded in the output and decoded (`decWEventsL`). The premises
beyond `watchOkL`:

- the history's facts (`HistWf`, `HistSorted`, its length the revision, `1 ≤ s0 ≤` its revision);
- **`WatchFromL s0 x all`**: the events after the initial ones (a watch-list's from its first
  bookmark; any other watch's all of them) mark revisions after `s0`: the replay knows the changes
  from `s0` on only. The store's watch starts at or after the revision it had when the watch was
  made, after the seeds (scope R3; read off `kStreamOk`'s start in step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealReplay
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## The driver's glue (`watch.go`, `realcheck.go`) -/

/-- **`toWEvent(ev)`** (`watch.go`): the four object event types with a `*Obj` its record and type
(`WAdded` 0, `WModified` 1, `WDeleted` 2, `WBookmark` 3), an Error with a `*metav1.Status` of status
`Failure` a `WError` (4), anything else `WBad` (5); the zero object but for the first. -/
def toWEvL (e : REv) : WEv :=
  if e.ty = evAdded ∨ e.ty = evModified ∨ e.ty = evDeleted ∨ e.ty = evBookmark then
    match e.o with
    | .obj o =>
      ⟨if e.ty = evModified then 1 else if e.ty = evDeleted then 2
        else if e.ty = evBookmark then 3 else 0, o⟩
    | _ => ⟨5, zObj⟩
  else if e.ty = evError then
    match e.o with
    | .status s => if s = go!"Failure" then ⟨4, zObj⟩ else ⟨5, zObj⟩
    | _ => ⟨5, zObj⟩
  else ⟨5, zObj⟩

/-- **`realEvents(in, evs)`** (`realcheck.go`): cut after the first Error event (D7g-2); for a
watch-list, nothing if no bookmark is left (D7g-3). -/
def realEventsL (x : Input) (evs : List REv) : List REv :=
  let cut := match evs.findIdx? (fun e => decide (e.ty = evError)) with
    | some i => evs.take (i + 1)
    | none => evs
  if x.SendInit' = W64 2 then
    (if cut.any (fun e => decide (e.ty = evBookmark)) then cut else [])
  else cut

/-! ## The premise on where a watch starts -/

/-- **The events after the initial ones mark revisions after `s0`** (`evLo`: an event's own
revision, a bookmark's plus one): for a watch-list, the non-error events from the first bookmark
on; for any other watch, all its non-error events. -/
def WatchFromL (s0 : w64) (x : Input) (all : List WEv) : Prop :=
  ∀ e ∈ (if x.SendInit' = W64 2 then (nonErr all).dropWhile (fun e => e.t ≠ 3) else nonErr all),
    uint.nat s0 < evLo e

/-! ## B5 -/

/-- **B5.** A watch of `x` that ran (not skipped, its `Watch` call did not fail), whose output's
events decode to the driver's view of the received events `raw` and which the driver's check
accepts at the configuration `h`, is accepted by `ValidateWatch` on `realEvents(in, raw)`, against
a replay that agrees with `h` from the seeded revision `s0` on. -/
theorem validateWatchL_of_watchOkL (s0 : w64) (R : RReplay) (h : HSt) (x : Input) (y : Output)
    (raw : List REv)
    (hlen : h.hist.length = uint.nat h.st.rv) (hwf : HistWf x h.hist) (hsort : HistSorted h.hist)
    (hs0 : 1 ≤ uint.nat s0) (hs0h : uint.nat s0 ≤ uint.nat h.st.rv)
    (hR : ReplayAt s0 R h)
    (hskip : x.Skip' = false) (hfail : y.WFailed' = false)
    (hdec : decWEventsL y.WEvents' = some (raw.map toWEvL))
    (hfrom : WatchFromL s0 x (raw.map toWEvL))
    (hok : watchOkL x y h = true) :
    validateWatchL R x (realEventsL x raw) = true := by
  sorry

end go

end k8s_correctness
end EtcdGrove
end Perennial
