/-
The consistent-index protocol of etcd's apply thread (`server/etcdserver/server.go`): the
shared vocabulary of the apply thread's specs (`Spec/EtcdServer__*.lean`). Lean-first (no
Rocq counterpart).

**What the consistent index is for.** The backend persists, in one bbolt transaction, the
effects of applied raft entries *and* the consistent index `ci`: after a crash, etcd
replays the raft log from `ci + 1`, applying to the backend only the entries above `ci`
(`apply`: `shouldApplyV3 = e.Index > ci`). So every commit must persist a `ci` that matches
the effects it persists: an entry with effects in the backend and an index above the saved
`ci` is applied twice after a crash (double apply); an entry at or below the saved `ci` whose
effects are not in the backend is never applied (lost update, etcd's #13766).

**The model.** The batch transaction's buffer is not modelled as data but by two indices
(ghost, the apply thread's): `eff`, the index of the last entry with writes in the buffer,
and `p`, the index through which every entry has been processed (its writes, if any, are in
the buffer). The invariant `consInv`, whenever no entry's writes are in flight, has
`eff ≤ ci ≤ p` (`ci` read as the stored index while the consistent index is 0, unloaded:
`cik`). A commit holds the batch transaction's lock and saves `ci` as the stored meta index
(`OnPreCommitUnsafe` → `UnsafeSave`), so what it persists satisfies `eff ≤ meta ≤ p`: exactly
the two properties above.

**Who moves what.** The apply thread is the only writer of `ci`, `p` and `eff`; it holds half
of a ghost variable with all four of `(k, p, eff, pending)` (`applyThread`), the invariant the
other half. The steps (the lemmas below):
- loading `ci` (it is 0 after `NewConsistentIndex`/`SetBackend`) from the stored index: `cik`
  unchanged (`ci_load_au`, for `ConsistentIndex`/`UnsafeConsistentIndex`);
- the post-lock hook, under the batch transaction's lock, before an entry's writes:
  `ci := i` for the entry `i = p + 1` being applied, with its writes now in flight
  (`pending`; the lock's token `pend` is deposited in the invariant: `hook_set_au`);
- the entry's writes, still under the lock: `p, eff := i` (`writes_done`, which takes `pend`
  back);
- an entry processed with no writes (the applier's contract says so of its outcome without
  the lock; or the code applies nothing, as for an entry without data): `p := i`
  (`skip_done`); then `ci := i` outside the lock (`ci_advance_au`, the deferred update in
  `applyEntryNormal`).
A commit, holding `pend`, finds the invariant out of the in-flight state, reads `ci` and saves
it (`commit_save_au`).

**The backend's meta keys.** The batch lock's invariant `batchLockInv` holds the batch
transaction's meta keys `TM mm` (the backend's resource: `metaWriter`'s view), half of a ghost
mirror of them, and `pend`. The read view (what `ReadTx` reads) is only ever read while `ci`
is 0, and then the stored meta keys have not been written since the backend was opened: they
are `γ.m0`, the meta keys the backend was opened with (`readView`: a read returns `m0` while
`written` is false). Once a commit stores a non-zero index, `written` is true for good.
-/
import EtcdGrove.Server.InvCindex
import Perennial.Ghost.Token

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex


/-- The protocol invariant's namespace. -/
abbrev applyN : Namespace := nroot.@"apply"

/-- The apply thread's state: the consistent index `k`, processed-through `p`, the last entry
with writes in the buffer `eff`, and whether an entry's writes are in flight. -/
structure ApplyState where
  k : w64
  p : w64
  eff : w64
  pending : Bool
deriving DecidableEq

instance ApplyState.countable : Pos.Countable ApplyState :=
  .ofInjective (fun s => Pos.Countable.encode (s.k, s.p, s.eff, s.pending))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The ghost names (and the backend's initial meta keys) of the protocol. -/
structure ApplyNames where
  /-- the consistent index's -/
  ci : CINames
  /-- `ghostVar ApplyState`: half the invariant's, half the apply thread's -/
  st : GName
  /-- `ghostVar w64`: the batch transaction's stored meta index, half the invariant's, half
  the batch lock's -/
  mt : GName
  /-- `ghostVar Bool`: a commit has stored meta keys since the backend was opened -/
  wr : GName
  /-- `token`: the batch lock's; the invariant's while an entry's writes are in flight -/
  pend : GName
  /-- the meta keys the backend was opened with -/
  m0 : MetaCI

/-- The consistent index as an index of the backend: while `ci` is 0 (unloaded) the stored
meta index, which then is still the one the backend was opened with; else `ci`. -/
def ciEff (γ : ApplyNames) (k : w64) : w64 := if k = W64 0 then γ.m0.1 else k

/-- The protocol's relation, out of the in-flight state: no entry above `ci` has writes in
the buffer, and every entry at or below it has been processed. -/
def stOk (γ : ApplyNames) (s : ApplyState) : Prop :=
  uint.Z s.eff ≤ uint.Z (ciEff γ s.k) ∧ uint.Z (ciEff γ s.k) ≤ uint.Z s.p

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]

/-- The invariant's part that depends on whether an entry's writes are in flight: if so,
the batch lock's token is here, `ci` is the entry `p + 1` and nothing above `p` has writes in
the buffer; if not, `stOk`. -/
def flightInv (γ : ApplyNames) (s : ApplyState) : IProp GF :=
  match s.pending with
  | true => iprop(token γ.pend ∗ ⌜s.k = s.p + 1⌝ ∗ ⌜uint.Z s.eff ≤ uint.Z s.p⌝ ∗
      ⌜uint.Z s.p < uint.Z s.k⌝)
  | false => iprop(⌜stOk γ s⌝)

instance flightInv_timeless (γ : ApplyNames) (s : ApplyState) :
    Timeless (flightInv (GF := GF) γ s) := by
  unfold flightInv; split <;> infer_instance

/-- The protocol invariant: the consistent index (the client's half of its mirror), the
protocol's state, the stored meta index `mi` and whether it has been written since the
backend was opened: a non-zero `ci` is not below the stored index, and while `ci` is 0 the
stored keys are the initial ones. -/
def consInv (γ : ApplyNames) : IProp GF :=
  iprop(∃ (s : ApplyState) (mi : w64) (w : Bool),
    ciIdx γ.ci s.k ∗ ghostVar γ.st (1 : Qp).half s ∗ ghostVar γ.mt (1 : Qp).half mi ∗
    ghostVar γ.wr 1 w ∗
    ⌜s.k ≠ W64 0 → uint.Z mi ≤ uint.Z s.k⌝ ∗
    ⌜s.k = W64 0 → w = false⌝ ∗ ⌜w = false → mi = γ.m0.1⌝ ∗ flightInv γ s)

instance consInv_timeless (γ : ApplyNames) : Timeless (consInv (GF := GF) γ) := by
  unfold consInv; infer_instance

/-- The apply thread's half: the protocol's state is `s`. -/
def applyThread (γ : ApplyNames) (s : ApplyState) : IProp GF :=
  ghostVar γ.st (1 : Qp).half s

/-- The batch transaction lock's invariant, for the backend's meta-keys resource `TM`: the
keys, the lock's half of the stored index's mirror, and the token `pend`. -/
def batchLockInv (γ : ApplyNames) (TM : MetaCI → IProp GF) : IProp GF :=
  iprop(∃ mm : MetaCI, ghostVar γ.mt (1 : Qp).half mm.1 ∗ TM mm ∗ token γ.pend)

/-- The read view of the meta keys, as the backend's `ReadTx` contract (`metaReadTx`) sees
it: while no commit has stored meta keys, they read as `γ.m0`. `γ.wr` is the invariant's;
a reader's linearization point borrows it. -/
def readView (γ : ApplyNames) (m : MetaCI) : IProp GF :=
  iprop(ghostVar γ.wr 1 false ∗ ⌜m = γ.m0⌝)

/-! ## The protocol's steps -/

/-- The post-lock hook's store `ci := i`, for the entry `i = p + 1` being applied, under the
batch lock (whose token `pend` it deposits in the invariant): the entry's writes are now in
flight. The update `SetConsistentIndex` takes. -/
theorem hook_set_au (γ : ApplyNames) (s : ApplyState) (i : w64) (Φ : IProp GF)
    (hpend : s.pending = false) (hi : i = s.p + 1) (hlt : uint.Z s.p < uint.Z i) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ token γ.pend -∗
      (applyThread γ { s with k := i, pending := true } -∗ Φ) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k0 : w64, ciIdx γ.ci k0 ∗ (ciIdx γ.ci i ={∅, ⊤ \ ↑ciN}=∗ Φ) := by
  iintro #Hinv Hst Htok HΦ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iunfold flightInv at Hrel
  rw [hpend]
  icases Hrel with %Hok
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod ghostVar_update_halves { s with k := i, pending := true } $$ Hst Hs with ⟨Hst, Hs⟩
  imod Hclose $$ [Hk Hs Hm Hw Htok] with -
  · inext
    iunfold consInv
    iexists { s with k := i, pending := true }, mi, w
    iframe Hk Hs Hm Hw
    iunfold flightInv
    dsimp only
    iframe Htok
    unfold stOk ciEff at Hok
    ipureintro
    refine ⟨fun _ => ?_, fun h => ?_, Hw0, hi, ?_, hlt⟩
    · by_cases hk : s.k = W64 0
      · have := Hw0 (Hk0 hk); subst this; simp only [hk, ↓reduceIte] at Hok; omega
      · have := Hmk hk; simp only [hk, ↓reduceIte] at Hok; omega
    · exfalso; subst hi; rw [h] at hlt; simp at hlt
    · split at Hok <;> omega
  imodintro
  iapply HΦ
  iunfold applyThread
  iexact Hst

/-- Reading `ci` (the fast path of `ConsistentIndex`/`UnsafeConsistentIndex`): it is the
apply thread's `k`. -/
theorem ci_read_au (γ : ApplyNames) (s : ApplyState) (Ψ : w64 → IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ (applyThread γ s -∗ Ψ s.k) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ.ci k ∗ (ciIdx γ.ci k ={∅, ⊤ \ ↑ciN}=∗ Ψ k) := by
  iintro #Hinv Hst HΨ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod Hclose $$ [Hk Hs Hm Hw Hrel] with -
  · inext
    iunfold consInv
    iexists s, mi, w
    iframe
    ipureintro
    exact ⟨Hmk, Hk0, Hw0⟩
  imodintro
  iapply HΨ
  iunfold applyThread
  iexact Hst

/-- What `UnsafeReadConsistentIndex` returns for stored meta keys `m`. -/
def loadedMeta (m : MetaCI) : MetaCI := if m.1 = W64 0 then (W64 0, W64 0) else m

theorem loadedMeta_fst (m : MetaCI) : (loadedMeta m).1 = m.1 := by
  unfold loadedMeta; split <;> simp_all

/-- One read of the read view while `ci` is 0: it reads `γ.m0`. -/
theorem read_view_au (γ : ApplyNames) (s : ApplyState) (hk : s.k = W64 0) (Ψ : MetaCI → IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ (applyThread γ s -∗ Ψ γ.m0) -∗
      readAU (⊤ \ ↑applyN) (readView γ) Ψ := by
  iintro #Hinv Hst HΨ
  unfold readAU
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  have hw : w = false := Hk0 hk
  subst hw
  imodintro
  iexists γ.m0
  iunfold readView
  iframe Hw
  isplitr
  · ipureintro; rfl
  iintro ⟨Hw, -⟩
  imod Hclose $$ [Hk Hs Hm Hw Hrel] with -
  · inext
    iunfold consInv
    iexists s, mi, false
    iframe
    ipureintro
    exact ⟨Hmk, Hk0, Hw0⟩
  imodintro
  iapply HΨ
  iunfold applyThread
  iexact Hst

/-- The two reads of `UnsafeReadConsistentIndex` while `ci` is 0 (the slow path of
`ConsistentIndex`/`UnsafeConsistentIndex`): they return `loadedMeta γ.m0`. -/
theorem read_ci_au (γ : ApplyNames) (s : ApplyState) (hk : s.k = W64 0)
    (Ψ : MetaCI → IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ (applyThread γ s -∗ Ψ (loadedMeta γ.m0)) -∗
      readCIAU (⊤ \ ↑applyN) (readView γ) Ψ := by
  iintro #Hinv Hst HΨ
  unfold readCIAU
  iapply read_view_au γ s hk $$ Hinv Hst
  iintro Hst
  unfold loadedMeta
  by_cases h0 : γ.m0.1 = W64 0
  · simp only [h0, ↓reduceIte]
    iapply HΨ $$ Hst
  · simp only [h0, ↓reduceIte]
    iapply read_view_au γ s hk $$ Hinv Hst
    iintro Hst
    iapply HΨ $$ Hst

/-- The store that ends the slow path of `ConsistentIndex`/`UnsafeConsistentIndex`: `ci`
becomes the stored index `γ.m0.1` (still 0 if absent): `ciEff` unchanged. -/
theorem ci_load_store_au (γ : ApplyNames) (s : ApplyState) (hk : s.k = W64 0)
    (hp : s.pending = false) (Φ : IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗
      (applyThread γ { s with k := γ.m0.1 } -∗ Φ) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k0 : w64, ciIdx γ.ci k0 ∗ (ciIdx γ.ci γ.m0.1 ={∅, ⊤ \ ↑ciN}=∗ Φ) := by
  iintro #Hinv Hst HΦ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  have hw : w = false := Hk0 hk
  subst hw
  have hmi : mi = γ.m0.1 := Hw0 rfl
  subst hmi
  iunfold flightInv at Hrel
  rw [hp]
  icases Hrel with %Hok
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod ghostVar_update_halves { s with k := γ.m0.1 } $$ Hst Hs with ⟨Hst, Hs⟩
  imod Hclose $$ [Hk Hs Hm Hw] with -
  · inext
    iunfold consInv
    iexists { s with k := γ.m0.1 }, γ.m0.1, false
    iframe
    iunfold flightInv
    dsimp only
    (try rw [hp])
    ipureintro
    unfold stOk ciEff at Hok ⊢
    simp only [hk, ↓reduceIte] at Hok
    refine ⟨fun _ => Int.le_refl _, fun _ => rfl, fun _ => rfl, ?_⟩
    split <;> simp_all
  imodintro
  iapply HΦ
  iunfold applyThread
  (try rw [hp])
  iexact Hst

/-- An entry's writes, under the batch lock, after the post-lock hook: the entry `k` is
processed and is the last with writes in the buffer; the lock's token comes back. -/
theorem writes_done (γ : ApplyNames) (s : ApplyState) (hp : s.pending = true) :
    inv applyN (consInv γ) ⊢ applyThread γ s ={⊤}=∗
      applyThread γ { k := s.k, p := s.k, eff := s.k, pending := false } ∗ token γ.pend := by
  iintro #Hinv Hst
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iunfold flightInv at Hrel
  rw [hp]
  icases Hrel with ⟨Htok, %Hkp, %Hep, %Hlt⟩
  imod ghostVar_update_halves { k := s.k, p := s.k, eff := s.k, pending := false } $$ Hst Hs
    with ⟨Hst, Hs⟩
  imod Hclose $$ [Hk Hs Hm Hw] with -
  · inext
    iunfold consInv
    iexists { k := s.k, p := s.k, eff := s.k, pending := false }, mi, w
    iframe
    iunfold flightInv
    dsimp only
    (try rw [hp])
    ipureintro
    have hk0 : s.k ≠ W64 0 := by intro h; rw [h] at Hlt; simp at Hlt
    refine ⟨Hmk, Hk0, Hw0, ?_⟩
    unfold stOk ciEff
    simp only [hk0, ↓reduceIte]
    omega
  imodintro
  iframe Htok
  iunfold applyThread
  (try rw [hp])
  iexact Hst

/-- The next entry to process, processed with no writes (the applier's outcome without the
batch lock, or code that applies nothing): it is processed. Sound only where no write has
happened, which is what the callers' contracts and code establish. -/
theorem skip_done (γ : ApplyNames) (s : ApplyState) (i : w64) (hp : s.pending = false)
    (_hi : i = s.p + 1) (hlt : uint.Z s.p < uint.Z i) :
    inv applyN (consInv γ) ⊢ applyThread γ s ={⊤}=∗ applyThread γ { s with p := i } := by
  iintro #Hinv Hst
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iunfold flightInv at Hrel
  rw [hp]
  icases Hrel with %Hok
  imod ghostVar_update_halves { s with p := i } $$ Hst Hs with ⟨Hst, Hs⟩
  imod Hclose $$ [Hk Hs Hm Hw] with -
  · inext
    iunfold consInv
    iexists { s with p := i }, mi, w
    iframe
    iunfold flightInv
    dsimp only
    (try rw [hp])
    ipureintro
    refine ⟨Hmk, Hk0, Hw0, ?_⟩
    unfold stOk at Hok ⊢
    dsimp only
    omega
  imodintro
  iunfold applyThread
  (try rw [hp])
  iexact Hst

/-- `ci := i` outside the batch lock, for a processed entry `i` above `ci` (the deferred
update of `applyEntryNormal`, after an entry with no writes). -/
theorem ci_advance_au (γ : ApplyNames) (s : ApplyState) (i : w64) (hp : s.pending = false)
    (hle : uint.Z i ≤ uint.Z s.p) (hlt : uint.Z (ciEff γ s.k) < uint.Z i) (Φ : IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ (applyThread γ { s with k := i } -∗ Φ) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k0 : w64, ciIdx γ.ci k0 ∗ (ciIdx γ.ci i ={∅, ⊤ \ ↑ciN}=∗ Φ) := by
  iintro #Hinv Hst HΦ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s0, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  iunfold applyThread at Hst
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iunfold flightInv at Hrel
  rw [hp]
  icases Hrel with %Hok
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod ghostVar_update_halves { s with k := i } $$ Hst Hs with ⟨Hst, Hs⟩
  have hmi : uint.Z mi ≤ uint.Z (ciEff γ s.k) := by
    unfold ciEff
    by_cases hk : s.k = W64 0
    · have := Hw0 (Hk0 hk); subst this; simp [hk]
    · have := Hmk hk; simp only [hk, ↓reduceIte]; exact this
  have hi0 : i ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
  imod Hclose $$ [Hk Hs Hm Hw] with -
  · inext
    iunfold consInv
    iexists { s with k := i }, mi, w
    iframe
    iunfold flightInv
    dsimp only
    (try rw [hp])
    ipureintro
    refine ⟨fun _ => by omega, fun h => absurd h hi0, Hw0, ?_⟩
    unfold stOk at Hok ⊢
    unfold ciEff
    simp only [hi0, ↓reduceIte]
    omega
  imodintro
  iapply HΦ
  iunfold applyThread
  (try rw [hp])
  iexact Hst

/-- What a commit persists is consistent: no entry above the saved index `m` has writes in
the buffer, and every entry at or below it has been processed. -/
def commitOk (s : ApplyState) (m : w64) : Prop :=
  uint.Z s.eff ≤ uint.Z m ∧ uint.Z m ≤ uint.Z s.p

/-- A commit's `UnsafeSave`, holding the batch lock (its token and its half of the stored
index's mirror `mm.1`): it reads `ci = k`, which is not below the stored index, and stores
`k` if it is not 0; the mirror follows, and what the commit persists is consistent. -/
theorem commit_save_au (γ : ApplyNames) (mm : MetaCI) (Ψ : w64 → IProp GF) :
    inv applyN (consInv γ) ⊢ ghostVar γ.mt (1 : Qp).half mm.1 -∗ token γ.pend -∗
      (∀ (k : w64) (s : ApplyState),
        ⌜k ≠ W64 0 → uint.Z mm.1 ≤ uint.Z k⌝ -∗
        ⌜commitOk s (if k = W64 0 then mm.1 else k)⌝ -∗
        ghostVar γ.mt (1 : Qp).half (if k = W64 0 then mm.1 else k) -∗ token γ.pend -∗ Ψ k) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ.ci k ∗ (ciIdx γ.ci k ={∅, ⊤ \ ↑ciN}=∗ Ψ k) := by
  iintro #Hinv Hml Htok HΨ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%s, %mi, %w, Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel⟩
  icombine Hml Hm gives %Heq
  obtain ⟨_, hmi⟩ := Heq
  subst hmi
  -- the commit holds `pend`, so no entry's writes are in flight
  iunfold flightInv at Hrel
  cases hps : s.pending
  case true =>
    icases Hrel with ⟨Htok', -⟩
    iexfalso
    iapply token_exclusive $$ Htok Htok'
  icases Hrel with %Hok
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod ghostVar_update_halves (if s.k = W64 0 then mm.1 else s.k) $$ Hml Hm with ⟨Hml, Hm⟩
  imod ghostVar_update (w || decide (s.k ≠ W64 0)) $$ Hw with Hw
  have hsave : commitOk s (if s.k = W64 0 then mm.1 else s.k) := by
    unfold commitOk
    unfold stOk ciEff at Hok
    by_cases hk : s.k = W64 0
    · have := Hw0 (Hk0 hk); simp only [hk, ↓reduceIte] at Hok ⊢; rw [this]; exact Hok
    · simp only [hk, ↓reduceIte] at Hok ⊢; exact Hok
  imod Hclose $$ [Hk Hs Hm Hw] with -
  · inext
    iunfold consInv
    iexists s, (if s.k = W64 0 then mm.1 else s.k), (w || decide (s.k ≠ W64 0))
    iframe
    iunfold flightInv
    rw [hps]
    ipureintro
    refine ⟨fun hk => ?_, fun hk => ?_, fun hw => ?_, Hok⟩
    · rw [ite_eq_right (fun h => absurd h hk)]; exact Int.le_refl _
    · have hd : decide (s.k ≠ W64 0) = false := decide_eq_false (fun h => h hk)
      rw [hd, Hk0 hk]
    · by_cases hk : s.k = W64 0
      · have hd : decide (s.k ≠ W64 0) = false := decide_eq_false (fun h => h hk)
        rw [hd, Bool.or_false] at hw
        rw [ite_eq_left hk]; exact Hw0 hw
      · have hd : decide (s.k ≠ W64 0) = true := decide_eq_true hk
        rw [hd, Bool.or_true] at hw
        cases hw
  imodintro
  iapply HΨ $$ %s.k %s %Hmk %hsave Hml Htok

end defs

end EtcdGrove
end Perennial
