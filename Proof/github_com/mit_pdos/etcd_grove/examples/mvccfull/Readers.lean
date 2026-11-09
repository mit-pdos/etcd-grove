/-
mvccfull's readers (`notes/mvccfull-proof-plan.md`, "Draft (F1): the invariants in full", R, and
"Draft revision: readers per epoch"). Lean-first (no Rocq counterpart).

**What a read learns** (`readQ`): a reader's read is a call of mvcc's API whose atomic update
commits the store's state `σ` unchanged (`reader_au`, mvccrand's pattern per incarnation). It opens
the incarnation's invariant (`memberInv`, `Members.lean`), which it may since it holds a share of
the incarnation's retirement token (`ghostVar ι.ret q ()`: the retired invariant holds the whole
token, so a live share rules that case out, `memberInv_live`), and records then: lower bounds of
the monotone revision and compaction revision at `σ`'s, a lower bound of the history covering `σ`'s
notified log (`histOkM`), and `σ`'s reachability. The floors loaded before the read (`revLo`,
`cmpLo`) are below `σ`'s values (`revLo_acc`, `cmpLo_acc`: a load gives a monotone lower bound above
the value loaded); the ceilings loaded after (`revHi`, `cmpHi`) are above them (`revHi_acc`,
`cmpHi_acc`: an upper bound of the current value, which is above any value it had before).

**An epoch's readers** (`startReaders` to `stopReaders`, between two restarts): each reader
goroutine holds, for each member, the member's current incarnation's handles, one reader token of
its store, a share `q` of the incarnation's retirement token and of the member's `kv` field
(`Members.lean`'s `incRd`; `incRdL` its abbreviation), and one reader slot of the history
(`histRd`): `rdOwn`. A reader may read both members (in F2, the corruption checker's hashes), so it holds both members' parts. The writer lends
the `n` readers' parts (`rdStock`) at `startReaders` and gets them back, whole, from the readers'
wait group (Perennial's thread-token join, `sync.tokJoin`, no lending) at `stopReaders`; then no
reader of the epoch is left, and the writer may retire an incarnation (`memberInv`'s retirement).
The stop flag `readStop` and the reads counter `reads` are atomics in invariants of any value
(`ctrInv`; their values carry nothing the proof needs), allocated by `Run`.

**The runner's fields the readers read**, persistent from `Run`'s setup on (`Run` writes `cfg`,
`keys`, `h` and `ms` before the first `startReaders` and never after): `runnerKeys` (the keys,
sorted, not empty), `runnerH` (the history), `runnerCfg` (the configuration and its read weights),
`runnerMs` (the members).

**F1's scope** (`readMixOk`): the read mix gives the corruption checker's hashes (alternative `5`)
no positive weight, gives some other alternative a positive weight, and its positive weights' sum
does not wrap (`pick.specW`, `Spec/.../mvccfull/pickW.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Members
public import Perennial.Proof.sync.WaitGroupTokJoin

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/-! ## The pure part -/

section model
variable [GooseExts]

/-- **F1's scope premise on the read mix** `w` (`Config.Mix.Read`, as integers): the hashes
(alternative `5`) have no positive weight, another of the six alternatives has one, and the
positive weights of the six sum below `2 ^ 63` (`pick`'s `total` does not wrap). With it,
`pick(w, 6)` never returns `5` (`pick.specW`, `readMixOk_ne5`). -/
def readMixOk (w : List Int) : Prop :=
  w.getD 5 0 ≤ 0 ∧ (∃ i, i < 6 ∧ 0 < w.getD i 0) ∧ ((w.take 6).map (fun x => max 0 x)).sum < 2 ^ 63

/-- An alternative of positive weight under `readMixOk` is not the hashes'. -/
theorem readMixOk_ne5 {w : List Int} (h : readMixOk w) {i : Nat} (hi : 0 < w.getD i 0) : i ≠ 5 := by
  rintro rfl; exact absurd h.1 (by omega)

/-- **A reachable state's revisions** (as `txn.reach_crev`, with the log's length): at least two
revisions, the compaction revision in `[-1, rev]`. -/
theorem reach_bounds (σ : MvccState) (h : MvccReachable σ) :
    2 ≤ σ.log.length ∧ -1 ≤ σ.crev ∧ σ.crev ≤ (σ.rev : Int) := by
  induction h with
  | start => simp [mvccStart, MvccState.rev]
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    have hl : σ.log.length ≤ σ.commitPending.log.length := by
      unfold MvccState.commitPending mvcc.commitLog
      split <;> simp
    have : σ.rev ≤ σ.commitPending.rev := by
      unfold MvccState.rev; omega
    have h2 : σ.commitPending.crev = σ.crev := rfl
    refine ⟨by omega, ih.2.1, ?_⟩
    rw [h2]; omega
  | compact σ r _ _ h1 h2 h3 ih =>
    exact ⟨ih.1, by simp [MvccState.compactTo]; omega, by
      simpa [MvccState.compactTo, MvccState.rev] using h3⟩

/-- **The history's states match the read log** (mvccrand's `hist_match`, over the keys `ks`): a
lower bound `Hl` covering the notified log, and any extension `Hs` of it, have the store's state at
each committed revision. -/
theorem hist_match (ks : List GoString) (σ : MvccState) (Hl Hs : List HRev)
    (hok : histOkM ks σ Hl) (hpre : Hl <+: Hs) (r : Nat) (hr : r < σ.log.length) :
    ∃ M, (Hs.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt σ.log r) := by
  have hle : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  obtain ⟨e, he, hrev⟩ := hok.2 r (by omega)
  refine ⟨e.1, ?_, ?_⟩
  · rw [List.getElem?_map, Perennial.prefix_getElem? hpre he]; rfl
  · have h1 := hrev.1
    have : stateAt σ.notifiedLog r = stateAt σ.log r := by
      unfold MvccState.notifiedLog; split
      · rfl
      · exact stateAt_append_lt _ _ hr
    rw [this] at h1; exact h1

end model

/-! ## The runner's fields, the counters, the wait group -/

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of the runner. -/
abbrev rF (f : GoString) (x : Loc) : Loc := structFieldRef runner f x

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The readers' namespace (their wait group's join, the counters' invariants). -/
def readersN : Namespace := (nroot .@ "mvccfull") .@ "readers"

/-- The readers' wait group's join namespace (`sync.tokJoin`'s, no lending). -/
def rdWgN : Namespace := readersN .@ "wg"

/-- **An atomic counter or flag whose value carries nothing** (persistent): the atomic in an
invariant, at any value (`readStop`, `reads`; any thread `Load`s, `Store`s or `Add`s it). -/
def ctrInv (N : Namespace) (l : Loc) : IProp GF :=
  iprop(inv N (∃ v : w64, sync.atomic.ownInt64 l (DFrac.own 1) v))

/-- **The readers' shared atomics** (persistent): the stop flag and the reads counter. -/
def rdShared (x : Loc) : IProp GF :=
  iprop(ctrInv (readersN .@ "stop") (rF go!"readStop" x) ∗
    ctrInv (readersN .@ "reads") (rF go!"reads" x))

/-- **The run's keys** (persistent): `x.keys` holds `ks`, sorted (`keysOf_sorted`), not empty
(`keysOf_ne`: `normalize` makes `Depth ≥ 1`; `genKey` indexes them). -/
def runnerKeys (x : Loc) (ks : List GoString) : IProp GF :=
  iprop(∃ keys : GoSlice, rF go!"keys" x ↦□ keys ∗ keys ↦*□ ks ∗
    ⌜ks.Pairwise go.GoStringLt ∧ ks ≠ []⌝)

/-- **The run's history** (persistent): `x.h` holds `h`. -/
def runnerH (x h : Loc) : IProp GF := iprop(rF go!"h" x ↦□ h)

/-- **The run's configuration and its range-revision weights** (persistent): what `genRange`
reads. -/
def runnerRangeMix (x : Loc) (cfg : Config) : IProp GF :=
  iprop(rF go!"cfg" x ↦□ cfg ∗ ∃ wrr : List w64, cfg.Mix'.RangeRev' ↦*□ wrr)

/-- **The run's configuration and its read weights `wr`** (persistent): what a reader reads. -/
def runnerCfg (x : Loc) (cfg : Config) (wr : List w64) : IProp GF :=
  iprop(runnerRangeMix x cfg ∗ cfg.Mix'.Read' ↦*□ wr)

/-- **The run's members** (persistent): `x.ms` holds the leader's and the follower's pointers. -/
def runnerMs (x mp0 mp1 : Loc) : IProp GF :=
  iprop(∃ msl : GoSlice, rF go!"ms" x ↦□ msl ∗ msl ↦*□ [mp0, mp1])

/-- A member's ghost names by its index (`0` the leader, `1` the follower). -/
def FullNames.mem (γ : FullNames) : Nat → MemberNames
  | 0 => γ.m0
  | _ => γ.m1

/-- **An incarnation, live** (exclusive, fractional in `q`): its handles and a share of its
retirement token (which rules out the retired case of its invariant, `memberInv_live`). What a
thread needs to open the incarnation's invariant (`checkStoreRange`'s ceilings; a stream
goroutine's). -/
def incLive (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) : IProp GF :=
  iprop(isInc ks γh i mp m ι kv ∗ ghostVar ι.ret q ())

/-- **A reader's part of a member's incarnation**: `Members.lean`'s `incRd` (handles, one reader
token, a share `q` of the retirement token and of the member's `kv` field). -/
abbrev incRdL (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) : IProp GF :=
  incRd ks γh i mp m ι kv q

/-- **A reader goroutine's part of an epoch** (exclusive): a reader slot of the history, and both
members' current incarnations' parts (`e0` the leader's incarnation and store handle, `e1` the
follower's). -/
def rdOwn (ks : List GoString) (h : Loc) (γ : FullNames) (mp0 mp1 : Loc)
    (e0 e1 : IncNames × GoInterface) (q : Qp) : IProp GF :=
  iprop(histRd h γ.h ∗ incRdL ks γ.h 0 mp0 γ.m0 e0.1 e0.2 q ∗ incRdL ks γ.h 1 mp1 γ.m1 e1.1 e1.2 q)

/-- `n` reader slots of the history. -/
def histRds (h : Loc) (γh : HistNames) (n : Nat) : IProp GF :=
  iprop([∗list] _u ∈ List.replicate n (), histRd h γh)

/-- What the writer lends `n` readers of a member's incarnation: `n` reader tokens, the share `q`
of the retirement token and of the `kv` field. -/
def rdLent (mp : Loc) (ι : IncNames) (kv : GoInterface) (n : Nat) (q : Qp) : IProp GF :=
  iprop(mvccReaders ι.kv n ∗ ghostVar ι.ret q () ∗ mF go!"kv" mp ↦{DFrac.own q} kv)

/-- **What the writer lends an epoch's `n` readers** (exclusive): `n` history slots and both
members' lent parts. `startReaders` takes it and `stopReaders` gives it back, whole (the readers'
`Done`s give their `rdOwn`s, without the persistent handles; `n = 0` keeps it in the join's
`ownAdder`). -/
def rdStock (h : Loc) (γ : FullNames) (mp0 mp1 : Loc) (e0 e1 : IncNames × GoInterface) (n : Nat)
    (q : Qp) : IProp GF :=
  iprop(histRds h γ.h n ∗ rdLent mp0 e0.1 e0.2 n q ∗ rdLent mp1 e1.1 e1.2 n q)

/-- **What a read learns of the state `σ` it reads** (persistent): lower bounds of the member's
monotone revision and compaction revision at `σ`'s, a lower bound `Hl` of the history covering
`σ`'s notified log, and `σ` reachable (so `2 ≤ |σ.log|` and `-1 ≤ σ.crev ≤ σ.rev`,
`reach_bounds`) with its log's bound. -/
def readQ (ks : List GoString) (γh : HistNames) (m : MemberNames) (σ : MvccState) : IProp GF :=
  iprop(∃ Hl : List HRev, monoListLbOwn γh.l Hl ∗ monoNatLbOwn m.rev σ.rev ∗
    monoNatLbOwn m.crev (Int.toNat (σ.crev + 1)) ∗
    ⌜histOkM ks σ Hl ∧ MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝)

instance readQ_persistent (ks : List GoString) (γh : HistNames) (m : MemberNames) (σ : MvccState) :
    Persistent (readQ (GF := GF) ks γh m σ) := by
  unfold readQ; infer_instance

end defs

/-! ## The laws (Iris statements; proofs to come: `sorry`, marked) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The members' invariants are outside mvcc's namespace. (Proof to come: `sorry`.) -/
theorem memberN_mask (i : Nat) : (↑(memberN i) : CoPset) ⊆ ⊤ \ ↑mvccN := by
  sorry

/-- **A live share rules out retirement**: with a share of the retirement token, the incarnation's
invariant holds its contents. (Proof to come: `sorry`; `ghostVar_valid_2`.) -/
theorem memberInv_live (ks : List GoString) (γh : HistNames) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (q : Qp) :
    ghostVar (GF := GF) ι.ret q () ∗ memberInv ks γh mp m ι ⊢
      ghostVar ι.ret q () ∗ memberState ks γh mp m ι.kv := by
  sorry

/-- **The revision's floor**: `revLo`'s load gives a lower bound `n` of the member's monotone
revision with the value loaded at most `n`. In the shape of `Int64.Load`'s premise. (Proof to
come: `sorry`; `memberInv_live`, `monoNatLbOwn_get`.) -/
theorem revLo_acc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) :
    incLive (GF := GF) ks γh i mp m ι kv q ⊢
      |={⊤,∅}=> ∃ v : w64, sync.atomic.ownInt64 (mF go!"revLo" mp) (DFrac.own 1) v ∗
        (sync.atomic.ownInt64 (mF go!"revLo" mp) (DFrac.own 1) v ={∅,⊤}=∗
          incLive ks γh i mp m ι kv q ∗ ∃ n : Nat, monoNatLbOwn m.rev n ∗ ⌜sint.Z v ≤ n⌝) := by
  sorry

/-- **The compaction revision's floor**: `cmpLo`'s load gives a lower bound `c` of the member's
monotone compaction revision plus one, with the value loaded plus one at most `c`. (Proof to come:
`sorry`.) -/
theorem cmpLo_acc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) :
    incLive (GF := GF) ks γh i mp m ι kv q ⊢
      |={⊤,∅}=> ∃ v : w64, sync.atomic.ownInt64 (mF go!"cmpLo" mp) (DFrac.own 1) v ∗
        (sync.atomic.ownInt64 (mF go!"cmpLo" mp) (DFrac.own 1) v ={∅,⊤}=∗
          incLive ks γh i mp m ι kv q ∗ ∃ c : Nat, monoNatLbOwn m.crev c ∗ ⌜sint.Z v + 1 ≤ c⌝) := by
  sorry

/-- **The revision's ceiling**: `revHi` holds at least any lower bound `n` of the monotone
revision (the revision now, at most `revHi`, is at least the one seen). In the shape of
`Int64.Load`'s premise (and `inBounds`'). (Proof to come: `sorry`.) -/
theorem revHi_acc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) (n : Nat) :
    incLive (GF := GF) ks γh i mp m ι kv q ∗ monoNatLbOwn m.rev n ⊢
      |={⊤,∅}=> ∃ v : w64, sync.atomic.ownInt64 (mF go!"revHi" mp) (DFrac.own 1) v ∗
        ⌜(n : Int) ≤ sint.Z v⌝ ∗
        (sync.atomic.ownInt64 (mF go!"revHi" mp) (DFrac.own 1) v ={∅,⊤}=∗
          incLive ks γh i mp m ι kv q) := by
  sorry

/-- **The compaction revision's ceiling**: `cmpHi` plus one holds at least any lower bound `c` of
the monotone compaction revision plus one. (Proof to come: `sorry`.) -/
theorem cmpHi_acc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) (c : Nat) :
    incLive (GF := GF) ks γh i mp m ι kv q ∗ monoNatLbOwn m.crev c ⊢
      |={⊤,∅}=> ∃ v : w64, sync.atomic.ownInt64 (mF go!"cmpHi" mp) (DFrac.own 1) v ∗
        ⌜(c : Int) ≤ sint.Z v + 1⌝ ∗
        (sync.atomic.ownInt64 (mF go!"cmpHi" mp) (DFrac.own 1) v ={∅,⊤}=∗
          incLive ks γh i mp m ι kv q) := by
  sorry

/-- **A reader's read update at the incarnation's invariant** (mvccrand's `reader_au`, per
incarnation and with the compaction revision): the state committed unchanged, with what the read
learns (`readQ`) and the floors `n` (revision) and `c` (compaction revision plus one) loaded before
below it; the live share back. The update of `KV.Rev`, `KV.FirstRev`, `KV.Read` and `KV.Range`
(`Q := fun σ => ghostVar ι.ret q () ∗ readQ … σ ∗ ⌜…⌝`). (Proof to come: `sorry`; mvccrand's,
with `memberInv_live`, `monoNatLbOwn_valid`/`_get`, `hreach`.) -/
theorem reader_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames)
    (kv : GoInterface) (q : Qp) (n c : Nat) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ monoNatLbOwn m.rev n ∗ monoNatLbOwn m.crev c ⊢
      ghostVar ι.ret q () -∗
      AU <{ ∃∃ σ, mvccState ι.kv σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState ι.kv σ, COMM ghostVar ι.ret q () ∗ readQ ks γh m σ ∗
          ⌜n ≤ σ.rev ∧ c ≤ Int.toNat (σ.crev + 1)⌝ }> := by
  sorry

/-- **A read the compaction revision `c` did not reach is one `clo ≤ c` did not reach**: the
outcome at `c`'s live case is the outcome at `clo` (`checkStoreRange` checks the store's `Range` at
the floor `clo` loaded before it). -/
theorem rangeOutcomeC_lower (r : Loc) (err : GoInterface) (L : Log) (rev : w64) (c clo : Int)
    (endNil : Bool) (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (hc : clo ≤ c)
    (h : sint.Z ro.Rev' ≤ sint.Z rev → c ≤ sint.Z (rangeRev rev ro.Rev')) :
    rangeOutcome (GF := GF) r err L rev endNil k e ro ⊢
      rangeOutcomeC r err L rev clo endNil k e ro := by
  iintro H
  iunfold rangeOutcomeC
  iright
  isplitr
  · ipureintro; intro h'; have := h h'; omega
  · iexact H

/-- **The lent parts split among `n` readers** (and join back): `n` readers' parts, each at the
share `q / n`, are the stock with the persistent handles. (Proof to come: `sorry`.) -/
theorem rdStock_split (ks : List GoString) (h : Loc) (γ : FullNames) (mp0 mp1 : Loc)
    (e0 e1 : IncNames × GoInterface) (n : Nat) (q : Qp) (hn : 0 < n) :
    isInc (GF := GF) ks γ.h 0 mp0 γ.m0 e0.1 e0.2 ∗ isInc ks γ.h 1 mp1 γ.m1 e1.1 e1.2 ⊢
      (rdStock h γ mp0 mp1 e0 e1 n q ∗-∗
        [∗list] _u ∈ List.replicate n (), rdOwn ks h γ mp0 mp1 e0 e1 (q / sync.posToQpZ (n : Int))) := by
  sorry

end laws

end mvccfull
end EtcdGrove
end Perennial
