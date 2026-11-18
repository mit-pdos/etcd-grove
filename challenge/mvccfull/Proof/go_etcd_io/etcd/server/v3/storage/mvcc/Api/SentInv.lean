/-
**`wsRecvOk` from what each response records at its send** (the pure core of the stream's
channel invariant, stage 1 of the mvcc API proof; formerly probe M1,
`notes/mvcc-api-probes/WsRecvOkProbe.lean`, 2026-11-04, moved here unchanged but for the
namespace: `notes/mvcc-api-risk.md`). The channel invariant keeps `SentInv` (its sent list's
facts), and `wsRecv_ok.law` is `wsRecvOk_of_sent` at the received prefix (`SentInv.take`).
Lean-first (no Rocq counterpart).

The probe's account, as written then: `notes/mvcc-api-invariants.md` §2 (`wsRecv`) says the consumer's view
holds, for each received response, pure facts and persistent ghost elements only. This file asks
whether the frozen pure guarantee `wsRecvOk` follows from such facts, with every other premise
one an invariant keeps under monotone ghost state (the notified log and the compaction revision
only grow; the registry only gains entries, never changes one; the cancelled set only grows; a
registration's stamp is the sent count at its atomic step).

- `SentFact`: what a response records at its send (pure data); `SentFact.holds pre f`: what is
  true of it at the send, `pre` the responses sent before it.
- `SentInv σ S D F`: the premises (the chain of facts, the lower bounds, registry agreement, the
  cancelled set's monotonicity, the progress stamps).
- `wsRecvOk_of_sent`: `SentInv σ S D F → wsRecvOk σ S (F.map (·.r))` (and the unbundled form).
- `sentFacts_snoc`: a send keeps `SentInv`; `SentInv.take`: the received prefix keeps it; the
  other steps (`register`, `cancel`, `close`, the store's `notify`/`commit`/`compact`/`Restore`)
  keep it.

**Result (no `sorry`, no axiom beyond Lean's): every conjunct of `wsRecvOk` follows from pure facts
recorded at the sends.** What the facts had to be, against §2's wording:
- The cumulative delivery is `∃ hi ≤ |L|` (its watcher's kept events of `[lo, hi)`), not "up to the
  response's revision": a batched response (`eb.moreRev ≠ 0`, `watchable_store.go:397-401`) carries
  the events below `moreRev` at `Revision: curRev`. Only a progress response's (no events, no
  compaction) `hi` is its revision `+ 1`, a separate fact.
- "The events sent so far" is `recvEvs` of the **sent** prefix before the response (`pre`), with
  the response's own (`sentChain`); the received list is a prefix of the sent (`SentInv.take`).
- The `-1` response records its covered watchers with their registry info (`CovEntry`), the
  cancelled ones as ids (`dead`, each in the cancelled set `D`).
- Two premises beyond the four asked: `S.ws !! -1 = none` (in `registryAgree`; else conjunct 3's
  `r.id = id` case at `id = -1` asks a `-1` response for a watcher `-1`'s events), and `deadIn`
  (the recorded cancelled ids are in `D`).
- The steps' premises: a registration's stamp at least the **sent** count at its atomic step
  (`SentInv.register`'s `F.length ≤ w.k`, `F` the sent list: `wsSentLb`'s `k ≤ sent` is the other
  half); a `-1` send covers every watcher registered by then (`stampsAt S F.length`); `commit_mono`
  needs `MvccReachable σ` (no pending `[]`); `Restore` needs `σ.pending = none` (`restore_mono`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api
namespace sent

open go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## What a response records at its send -/

/-- A watcher a stream-wide (`-1`) progress response covers: its id and its registry info. -/
structure CovEntry where
  id : w64
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat

/-- **What a response records when it is sent** (§2): the response; its watcher's registry info
(the `ι.reg` element: range, filters, first revision; meaningless for a `-1` response); the
notified-log lower bound `L` and the compaction lower bound `c0` (the `γ.crevLb` fragment) at the
send; for a `-1` response, the watchers it covers (each with its registry element) and those
cancelled when it was sent (`ι.dead` elements). -/
structure SentFact where
  r : WResp
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat
  L : Log
  c0 : Int
  cov : List CovEntry
  dead : List w64

/-- The response's own shape against the bounds it was sent with (`wsRecvOk`'s first conjunct,
with `L` for the notified log and `c0` for the compaction revision). -/
def respShape (r : WResp) (L : Log) (c0 : Int) : Prop :=
  (∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev) ∧
  (r.compactRev = W64 0 → sint.nat r.rev < L.length) ∧
  (r.compactRev ≠ W64 0 → r.evs = [] ∧ r.id ≠ W64 (-1) ∧ r.rev = W64 0 ∧
    0 < sint.Z r.compactRev ∧ sint.Z r.compactRev ≤ c0) ∧
  (r.id = W64 (-1) → r.evs = [] ∧ r.compactRev = W64 0 ∧ 1 ≤ sint.Z r.rev) ∧
  (∀ ev ∈ r.evs, 0 < sint.Z ev.kv.modRev ∧
    (ev.del = false → 0 < sint.Z ev.kv.createRev ∧ 0 < sint.Z ev.kv.version))

/-- **What is true of a response at its send**, `pre` the responses sent before it: its shape;
the cumulative delivery of its watcher (while `onceUpTo L lo c0`, the watcher's events sent so
far, this response's included, are its kept events of `[lo, hi)` of `L`, some `hi`); a progress
response's (no events, no compaction) `hi` its revision `+ 1`; a `-1` response's coverage (each
covered watcher's events so far its kept events up to the response's revision); a progress
response's revision at least its watcher's (or each covered watcher's) first revision less one, and
at least every event-less response's sent before it (`wsRecvOk`'s conjuncts 4-5, F-W1,
2026-11-06). -/
def SentFact.holds (pre : List WResp) (f : SentFact) : Prop :=
  respShape f.r f.L f.c0 ∧
  (f.r.id ≠ W64 (-1) → onceUpTo f.L f.lo f.c0 →
    ∃ hi, hi ≤ f.L.length ∧
      recvEvs (pre ++ [f.r]) f.r.id = filtered f.fs (watchEvents f.L f.rg f.lo hi)) ∧
  (f.r.id ≠ W64 (-1) → f.r.evs = [] → f.r.compactRev = W64 0 → onceUpTo f.L f.lo f.c0 →
    recvEvs (pre ++ [f.r]) f.r.id =
      filtered f.fs (watchEvents f.L f.rg f.lo (sint.nat f.r.rev + 1))) ∧
  (f.r.id = W64 (-1) → ∀ c ∈ f.cov, onceUpTo f.L c.lo f.c0 →
    recvEvs (pre ++ [f.r]) c.id = filtered c.fs (watchEvents f.L c.rg c.lo (sint.nat f.r.rev + 1))) ∧
  (f.r.evs = [] → f.r.compactRev = W64 0 →
    (f.r.id ≠ W64 (-1) → (f.lo : Int) ≤ sint.Z f.r.rev + 1) ∧
    (f.r.id = W64 (-1) → ∀ c ∈ f.cov, (c.lo : Int) ≤ sint.Z f.r.rev + 1) ∧
    ∀ y ∈ pre, y.evs = [] → sint.Z y.rev ≤ sint.Z f.r.rev)

/-! ## The premises -/

/-- The stream's state has the watcher `id` with this registry info (an `ι.reg` element). -/
def regAgree (S : StreamState) (id : w64) (rg : WatchRange) (fs : List (EvM → Bool)) (lo : Nat) :
    Prop :=
  ∃ w, S.ws !! id = some w ∧ w.rg = rg ∧ w.fs = fs ∧ w.lo = lo

/-- A fact's registry info agrees with the stream's state. -/
def factAgree (S : StreamState) (f : SentFact) : Prop :=
  (f.r.id ≠ W64 (-1) → regAgree S f.r.id f.rg f.fs f.lo) ∧
  (f.r.id = W64 (-1) → ∀ c ∈ f.cov, regAgree S c.id c.rg c.fs c.lo)

/-- A `-1` response at `j` (stamp: the sent count) covers each watcher registered at a stamp at
most `j` (that is, registered before it was sent), or recorded it cancelled. -/
def stampsAt (S : StreamState) (j : Nat) (f : SentFact) : Prop :=
  f.r.id = W64 (-1) → ∀ id w, S.ws !! id = some w → w.k ≤ j →
    (∃ c ∈ f.cov, c.id = id) ∨ id ∈ f.dead

/-! ## Pure lemmas -/

/-! ## The main result -/

/-! ## The steps keep the premises -/

end sent
end api
end mvcc
end EtcdGrove
end Perennial
