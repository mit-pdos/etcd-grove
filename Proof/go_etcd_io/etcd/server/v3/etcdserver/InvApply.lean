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

**One protocol, several backends** (D22 receiver epochs, S7f, 2026-10-23; `notes/decisions.md`,
"D22 receiver epochs, S7f carried out"). The names split: the logical ones (`ci`, `st`, `fz`, and
`cur`, `reg`) are the server's for good, the physical ones (`ApplyPhys`: `mt`, `wr`, `pend`, `m0`)
a backend's. The invariant reads only the logical names (`consInv (γ.withPh π) = consInv γ`); the
current backend's physical names are a ghost variable `cur`, half the invariant's, half the apply
thread's (`curOwn`, in `applyThread` and `freezeY`), so every step of the apply thread is at the
current backend's names, and the registry `reg` (a monotone list) holds every backend's names the
protocol has had, the current last. `applySnapshot`'s swap (`ci_swap_au`, at `ci.SetBackend`'s
store of 0) retires the current names: their mirror's invariant half joins `retiredInv`, bounded by
`ciEff`, which never decreases; the old backend's batch lock keeps its registration (`applyRegd`, in
`batchLockInv`), so the commit of its `Close`, which runs the server's hooks (one hooks object for
every backend), still goes through `commit_save_au` (its retired case). The protocol's allocation
for the boot backend: `consInv_alloc`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Perennial.Ghost.Token

@[expose] public section

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

/-- **The protocol's physical names** (D22 receiver epochs, S7f, 2026-10-23): those of one
backend, which `applySnapshot`'s swap replaces: the stored index's mirror `mt`, the read view's
`wr`, the batch lock's token `pend`, and the meta keys the backend was opened with `m0`. -/
structure ApplyPhys where
  /-- `ghostVar w64`: the batch transaction's stored meta index, half the batch lock's, half the
  invariant's (the current backend's in `consInvAt`, a retired one's in `retiredInv`) -/
  mt : GName
  /-- `ghostVar Bool`: a commit has stored meta keys since the backend was opened -/
  wr : GName
  /-- `token`: the batch lock's; the invariant's while an entry's writes are in flight -/
  pend : GName
  /-- the meta keys the backend was opened with -/
  m0 : MetaCI

instance ApplyPhys.countable : Pos.Countable ApplyPhys :=
  .ofInjective (fun π => Pos.Countable.encode (π.mt, π.wr, π.pend, π.m0))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The ghost names of the protocol: the logical ones (`ci`, `st`, `fz`, `cur`, `reg`), fixed for
the server's life, and the current backend's physical ones (`ph`; D22 receiver epochs, S7f,
2026-10-23: until then all of them fixed, so the protocol was of one backend). -/
structure ApplyNames where
  /-- the consistent index's -/
  ci : CINames
  /-- `ghostVar ApplyState`: half the invariant's, half the apply thread's -/
  st : GName
  /-- `token`: the invariant's out of the stored-index window, the window's holder's in it
  (`consFrozen`; D22 the stored-index window, 2026-10-23) -/
  fz : GName
  /-- `ghostVar ApplyPhys` (S7f): the current backend's physical names, half the invariant's, half
  the apply thread's (`curOwn`, in `applyThread` or `freezeY`) -/
  cur : GName
  /-- `monoList ApplyPhys` (S7f): every backend's physical names the protocol has had, the
  current one last (the invariant's authority); a batch lock holds the index of its own
  (`applyRegd`), so its commits find their mirror whether its backend is current or retired -/
  reg : GName
  /-- the physical names these names are at (the current backend's for the apply thread) -/
  ph : ApplyPhys

/-- The stored index's mirror of the names' backend. -/
abbrev ApplyNames.mt (γ : ApplyNames) : GName := γ.ph.mt
/-- The read view's `written` flag of the names' backend. -/
abbrev ApplyNames.wr (γ : ApplyNames) : GName := γ.ph.wr
/-- The batch lock's token of the names' backend. -/
abbrev ApplyNames.pend (γ : ApplyNames) : GName := γ.ph.pend
/-- The meta keys the names' backend was opened with. -/
abbrev ApplyNames.m0 (γ : ApplyNames) : MetaCI := γ.ph.m0

/-- **The names `γ` at the physical names `π`** (S7f): `γ`'s logical names. -/
abbrev ApplyNames.withPh (γ : ApplyNames) (π : ApplyPhys) : ApplyNames :=
  ⟨γ.ci, γ.st, γ.fz, γ.cur, γ.reg, π⟩

theorem ApplyNames.withPh_ph (γ : ApplyNames) : γ.withPh γ.ph = γ := rfl

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

/-- The protocol invariant's state out of the stored-index window: the consistent index (the
client's half of its mirror), the protocol's state, the stored meta index `mi` and whether it has
been written since the backend was opened: a non-zero `ci` is not below the stored index, and
while `ci` is 0 the stored keys are the initial ones; the window's token. -/
def consInvAt (γ : ApplyNames) (s : ApplyState) (mi : w64) (w : Bool) : IProp GF :=
  iprop(ciIdx γ.ci s.k ∗ ghostVar γ.st (1 : Qp).half s ∗ ghostVar γ.mt (1 : Qp).half mi ∗
    ghostVar γ.wr 1 w ∗
    ⌜s.k ≠ W64 0 → uint.Z mi ≤ uint.Z s.k⌝ ∗
    ⌜s.k = W64 0 → w = false⌝ ∗ ⌜w = false → mi = γ.m0.1⌝ ∗ flightInv γ s ∗ token γ.fz)

/-- **The protocol frozen in the stored-index window** (D22 the stored-index window, 2026-10-23;
`notes/decisions.md`, "D22 the stored-index window carried out"): a commit stored the apply
thread's consistent index `s.k` (not 0, nothing in flight: `commit_freeze_au`), the apply thread
deposited a quarter of the protocol's state here and holds the other quarter, a quarter of the
stored index's mirror and the token `γ.fz` (`freezeY`). While frozen no step of the apply thread can
run (it holds no half of the state), so `ci` stays `s.k`, which every commit stores again. -/
def consFrozen (γ : ApplyNames) (s : ApplyState) (mi : w64) (w : Bool) : IProp GF :=
  iprop(ciIdx γ.ci s.k ∗ ghostVar γ.st (1 : Qp).half s ∗ ghostVar γ.st (1 : Qp).half.half s ∗
    ghostVar γ.mt (1 : Qp).half.half mi ∗ ghostVar γ.wr 1 w ∗
    ⌜s.k = mi ∧ s.k ≠ W64 0 ∧ s.pending = false ∧ w = true ∧ stOk γ s⌝)

/-- **The retired backends' mirrors** (D22 receiver epochs, S7f, 2026-10-23): for every backend
`applySnapshot` replaced, the invariant's half of its stored index's mirror, at most `c` (the
current consistent index as an index, `ciEff`): an old backend's batch lock (its `Close` commits
through the server's hooks, one hooks object for every backend) stores whatever `ci` holds, which,
when not 0, is not below its stored index (`commit_save_au`'s retired case). -/
def retiredInv (l : List ApplyPhys) (c : w64) : IProp GF :=
  iprop([∗list] π ∈ l, ∃ mr : w64, ghostVar π.mt (1 : Qp).half mr ∗ ⌜uint.Z mr ≤ uint.Z c⌝)

instance retiredInv_timeless (l : List ApplyPhys) (c : w64) :
    Timeless (retiredInv (GF := GF) l c) := by
  unfold retiredInv; infer_instance

/-- The retired mirrors' bound only grows. -/
theorem retiredInv_mono (l : List ApplyPhys) (c c' : w64) (h : uint.Z c ≤ uint.Z c') :
    retiredInv (GF := GF) l c ⊢ retiredInv l c' := by
  unfold retiredInv
  apply BigSepL.bigSepL_mono_of_forall
  intro _ π
  iintro ⟨%mr, Hm, %Hr⟩
  iexists mr
  iframe Hm
  ipureintro; omega

/-- **The protocol's registry and retired backends** at the names `γ` (S7f): the authority of the
registry (the retired backends' physical names `l`, then the current `γ.ph`) and the retired
mirrors (`retiredInv`, at most `c`). -/
def consRest (γ : ApplyNames) (l : List ApplyPhys) (c : w64) : IProp GF :=
  iprop(monoListAuthOwn γ.reg 1 (l ++ [γ.ph]) ∗ retiredInv l c)

instance consRest_timeless (γ : ApplyNames) (l : List ApplyPhys) (c : w64) :
    Timeless (consRest (GF := GF) γ l c) := by
  unfold consRest; infer_instance

/-- The protocol invariant: the current backend's physical names `π` (half of `γ.cur`), the
protocol at them out of the stored-index window (`consInvAt`) or frozen in it (`consFrozen`), the
registry and the retired backends' mirrors (`consRest`; D22 receiver epochs, S7f, 2026-10-23:
until then of one backend, all names fixed). Only `γ`'s logical names are read: `consInv
(γ.withPh π) = consInv γ`. -/
def consInv (γ : ApplyNames) : IProp GF :=
  iprop(∃ (π : ApplyPhys) (l : List ApplyPhys) (s : ApplyState) (mi : w64) (w : Bool),
    ghostVar γ.cur (1 : Qp).half π ∗
    (consInvAt (γ.withPh π) s mi w ∨ consFrozen (γ.withPh π) s mi w) ∗
    consRest (γ.withPh π) l (ciEff (γ.withPh π) s.k))

instance consInv_timeless (γ : ApplyNames) : Timeless (consInv (GF := GF) γ) := by
  unfold consInv consInvAt consFrozen; infer_instance

theorem consInv_withPh (γ : ApplyNames) (π : ApplyPhys) :
    consInv (GF := GF) (γ.withPh π) = consInv γ := rfl

/-- The apply thread's (or the window's holder's) half of the current physical names: `γ.ph`
(S7f). -/
def curOwn (γ : ApplyNames) : IProp GF :=
  ghostVar γ.cur (1 : Qp).half γ.ph

instance curOwn_timeless (γ : ApplyNames) : Timeless (curOwn (GF := GF) γ) := by
  unfold curOwn; infer_instance

/-- The apply thread's half: the protocol's state is `s`, at the current backend's physical names
`γ.ph` (`curOwn`, S7f). -/
def applyThread (γ : ApplyNames) (s : ApplyState) : IProp GF :=
  iprop(ghostVar γ.st (1 : Qp).half s ∗ curOwn γ)

/-- **A batch lock's registration** (persistent; S7f): the physical names `γ.ph` are in the
protocol's registry. -/
def applyRegd (γ : ApplyNames) : IProp GF :=
  iprop(∃ i : Nat, monoListIdxOwn γ.reg i γ.ph)

instance applyRegd_persistent (γ : ApplyNames) : Persistent (applyRegd (GF := GF) γ) := by
  unfold applyRegd; infer_instance

instance applyRegd_timeless (γ : ApplyNames) : Timeless (applyRegd (GF := GF) γ) := by
  unfold applyRegd monoListIdxOwn monoListLbOwn; infer_instance

/-- The protocol's parts at `γ.withPh γ.ph` are at `γ`. -/
theorem consParts_ph (γ : ApplyNames) (l : List ApplyPhys) (s : ApplyState) (mi : w64) (w : Bool) :
    ((consInvAt (GF := GF) (γ.withPh γ.ph) s mi w ∨ consFrozen (γ.withPh γ.ph) s mi w) ∗
      consRest (γ.withPh γ.ph) l (ciEff (γ.withPh γ.ph) s.k)) ⊢
      (consInvAt γ s mi w ∨ consFrozen γ s mi w) ∗ consRest γ l (ciEff γ s.k) := .rfl

/-- The protocol's parts at `γ` are at `γ.withPh γ.ph`. -/
theorem consParts_ph' (γ : ApplyNames) (l : List ApplyPhys) (s : ApplyState) (mi : w64)
    (w : Bool) :
    ((consInvAt (GF := GF) γ s mi w ∨ consFrozen γ s mi w) ∗ consRest γ l (ciEff γ s.k)) ⊢
      (consInvAt (γ.withPh γ.ph) s mi w ∨ consFrozen (γ.withPh γ.ph) s mi w) ∗
        consRest (γ.withPh γ.ph) l (ciEff (γ.withPh γ.ph) s.k) := .rfl

/-- **Opening the invariant with the apply thread's part of the current names** (S7f): the
current names are `γ.ph`; the invariant's half of them comes out with the protocol at `γ`. -/
theorem consInv_open (γ : ApplyNames) :
    consInv (GF := GF) γ ∗ curOwn γ ⊢ curOwn γ ∗ curOwn γ ∗
      ∃ (l : List ApplyPhys) (s : ApplyState) (mi : w64) (w : Bool),
        (consInvAt γ s mi w ∨ consFrozen γ s mi w) ∗ consRest γ l (ciEff γ s.k) := by
  iintro ⟨Hi, Hc⟩
  iunfold consInv at Hi
  icases Hi with ⟨%π, %l, %s, %mi, %w, Hc', Hi, Hr⟩
  iunfold curOwn at Hc
  icombine Hc Hc' gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  icases consParts_ph γ l s mi w $$ [$Hi $Hr] with ⟨Hi, Hr⟩
  iunfold curOwn
  iframe Hc Hc'
  iexists l, s, mi, w
  iframe Hi Hr

/-- **Closing the invariant** at the current names `γ.ph` (S7f), the protocol from `s` to `s'`,
whose consistent index as an index (`ciEff`) has not decreased (the retired mirrors' bound). -/
theorem consInv_close (γ : ApplyNames) (l : List ApplyPhys) (s s' : ApplyState) (mi : w64)
    (w : Bool) (hle : uint.Z (ciEff γ s.k) ≤ uint.Z (ciEff γ s'.k)) :
    curOwn (GF := GF) γ ∗ consRest γ l (ciEff γ s.k) ∗
      (consInvAt γ s' mi w ∨ consFrozen γ s' mi w) ⊢ consInv γ := by
  iintro ⟨Hc, Hr, Hi⟩
  iunfold consRest at Hr
  icases Hr with ⟨Ha, Hr⟩
  ihave Hr := retiredInv_mono l _ _ hle $$ Hr
  icases consParts_ph' γ l s' mi w $$ [$Hi Ha Hr] with ⟨Hi, Hr⟩
  · iunfold consRest
    iframe Ha Hr
  iunfold consInv
  iexists γ.ph, l, s', mi, w
  iunfold curOwn at Hc
  iframe Hc Hi Hr

/-- The frozen invariant holds three quarters of the protocol's state: the apply thread,
holding its half, is not frozen. -/
theorem frozen_thread_false (γ : ApplyNames) (s s' : ApplyState) (mi : w64) (w : Bool) :
    consFrozen (GF := GF) γ s mi w ∗ ghostVar γ.st (1 : Qp).half s' ⊢ False := by
  unfold consFrozen
  iintro ⟨⟨-, Hs, Hq, -⟩, Hst⟩
  icombine Hs Hst gives %Hv
  obtain ⟨-, rfl⟩ := Hv
  ihave Hfull := (ghostVar_split_half γ.st 1 s).2 $$ [Hs Hst]
  · iframe
  icombine Hfull Hq gives %Hv
  exfalso
  exact Qp_one_add_not_le _ Hv.1

/-- The batch transaction lock's invariant, for the backend's meta-keys resource `TM`: the
keys, the lock's half of the stored index's mirror, the token `pend`, and (S7f) the registration
of the backend's physical names (`applyRegd`), so that its commits find their mirror once the
backend is retired. -/
def batchLockInv (γ : ApplyNames) (TM : MetaCI → IProp GF) : IProp GF :=
  iprop(∃ mm : MetaCI, ghostVar γ.mt (1 : Qp).half mm.1 ∗ TM mm ∗ token γ.pend ∗ applyRegd γ)

/-- The read view of the meta keys, as the backend's `ReadTx` contract (`metaReadTx`) sees
it: while no commit has stored meta keys, they read as `γ.m0`. `γ.wr` is the invariant's;
a reader's linearization point borrows it. -/
def readView (γ : ApplyNames) (m : MetaCI) : IProp GF :=
  iprop(ghostVar γ.wr 1 false ∗ ⌜m = γ.m0⌝)

/-- The protocol's state out of the window: `ci` and the stored index, as an index (`ciEff`), at
least the stored index. -/
theorem consInvAt_mi (γ : ApplyNames) (s : ApplyState) (mi : w64) (w : Bool)
    (Hmk : s.k ≠ W64 0 → uint.Z mi ≤ uint.Z s.k) (Hk0 : s.k = W64 0 → w = false)
    (Hw0 : w = false → mi = γ.m0.1) : uint.Z mi ≤ uint.Z (ciEff γ s.k) := by
  unfold ciEff
  by_cases hk : s.k = W64 0
  · have := Hw0 (Hk0 hk); subst this; simp [hk]
  · simp only [hk, ↓reduceIte]; exact Hmk hk
/-- A registry index of the authority, the authority kept. -/
theorem reg_lookup (γr : GName) (l : List ApplyPhys) (i : Nat) (π : ApplyPhys) :
    monoListAuthOwn (GF := GF) γr 1 l ∗ monoListIdxOwn γr i π ⊢
      ⌜l[i]? = some π⌝ ∗ (monoListAuthOwn γr 1 l ∗ monoListIdxOwn γr i π) :=
  persistent_entails_right (by
    iintro ⟨Ha, Hi⟩
    iapply mono_list_auth_idx_lookup γr 1 l i π $$ Ha Hi)

/-- The consistent index out of the protocol (in or out of the window), and back. -/
theorem consCore_ci (γ : ApplyNames) (s : ApplyState) (mi : w64) (w : Bool) :
    (consInvAt (GF := GF) γ s mi w ∨ consFrozen γ s mi w) ⊢
      ciIdx γ.ci s.k ∗ (ciIdx γ.ci s.k -∗ (consInvAt γ s mi w ∨ consFrozen γ s mi w)) := by
  iintro (Hi | Hi)
  · iunfold consInvAt at Hi
    icases Hi with ⟨Hk, Hrest⟩
    iframe Hk
    iintro Hk
    ileft
    iunfold consInvAt
    iframe
  · iunfold consFrozen at Hi
    icases Hi with ⟨Hk, Hrest⟩
    iframe Hk
    iintro Hk
    iright
    iunfold consFrozen
    iframe

/-- `ciEff` past a larger index `i`: `i` itself (not 0). -/
theorem ciEff_le_of_lt (γ : ApplyNames) (k i : w64) (h : uint.Z (ciEff γ k) < uint.Z i) :
    uint.Z (ciEff γ k) ≤ uint.Z (ciEff γ i) := by
  have hi0 : i ≠ W64 0 := by
    intro h0; rw [h0] at h; have : (0 : Int) ≤ uint.Z (ciEff γ k) := by word
    simp at h
  unfold ciEff at h ⊢
  rw [if_neg hi0]
  omega

/-- Loading `ci` (0) as the stored index `γ.m0.1` leaves `ciEff`. -/
theorem ciEff_load_le (γ : ApplyNames) (k : w64) (hk : k = W64 0) :
    uint.Z (ciEff γ k) ≤ uint.Z (ciEff γ γ.m0.1) := by
  unfold ciEff
  rw [if_pos hk]
  split <;> exact Int.le_refl _

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
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
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
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Htok Hfzt] with -
  · inext
    iapply consInv_close γ l s ({ s with k := i, pending := true }) mi w (ciEff_le_of_lt γ s.k i (by have := Hok.2; omega))
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
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
  iframe Hcu
  iexact Hst

/-- Reading `ci` (the fast path of `ConsistentIndex`/`UnsafeConsistentIndex`): it is the
apply thread's `k`. -/
theorem ci_read_au (γ : ApplyNames) (s : ApplyState) (Ψ : w64 → IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ (applyThread γ s -∗ Ψ s.k) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ.ci k ∗ (ciIdx γ.ci k ={∅, ⊤ \ ↑ciN}=∗ Ψ k) := by
  iintro #Hinv Hst HΨ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hrel Hfzt] with -
  · inext
    iapply consInv_close γ l s (s) mi w (Int.le_refl _)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
    iframe
    ipureintro
    exact ⟨Hmk, Hk0, Hw0⟩
  imodintro
  iapply HΨ
  iunfold applyThread
  iframe Hcu
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
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
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
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hrel Hfzt] with -
  · inext
    iapply consInv_close γ l s (s) mi false (Int.le_refl _)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
    iframe
    ipureintro
    exact ⟨Hmk, Hk0, Hw0⟩
  imodintro
  iapply HΨ
  iunfold applyThread
  iframe Hcu
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
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
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
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hfzt] with -
  · inext
    iapply consInv_close γ l s ({ s with k := γ.m0.1 }) γ.m0.1 false (ciEff_load_le γ s.k hk)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
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
  iframe Hcu
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
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iunfold flightInv at Hrel
  rw [hp]
  icases Hrel with ⟨Htok, %Hkp, %Hep, %Hlt⟩
  imod ghostVar_update_halves { k := s.k, p := s.k, eff := s.k, pending := false } $$ Hst Hs
    with ⟨Hst, Hs⟩
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hfzt] with -
  · inext
    iapply consInv_close γ l s ({ k := s.k, p := s.k, eff := s.k, pending := false }) mi w (Int.le_refl _)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
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
  iframe Hcu
  (try rw [hp])
  iexact Hst

/-- The next entry to process, processed with no writes (the applier's outcome without the
batch lock, or code that applies nothing): it is processed. Sound only where no write has
happened, which is what the callers' contracts and code establish. -/
theorem skip_done (γ : ApplyNames) (s : ApplyState) (i : w64) (hp : s.pending = false)
    (_hi : i = s.p + 1) (hlt : uint.Z s.p < uint.Z i) :
    inv applyN (consInv (GF := GF) γ) ⊢ applyThread γ s ={⊤}=∗ applyThread γ { s with p := i } := by
  iintro #Hinv Hst
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  iunfold flightInv at Hrel
  rw [hp]
  icases Hrel with %Hok
  imod ghostVar_update_halves { s with p := i } $$ Hst Hs with ⟨Hst, Hs⟩
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hfzt] with -
  · inext
    iapply consInv_close γ l s ({ s with p := i }) mi w (Int.le_refl _)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
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
  iframe Hcu
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
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
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
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hfzt] with -
  · inext
    iapply consInv_close γ l s ({ s with k := i }) mi w (ciEff_le_of_lt γ s.k i hlt)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
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
  iframe Hcu
  (try rw [hp])
  iexact Hst

/-- What a commit persists is consistent: no entry above the saved index `m` has writes in
the buffer, and every entry at or below it has been processed. -/
def commitOk (s : ApplyState) (m : w64) : Prop :=
  uint.Z s.eff ≤ uint.Z m ∧ uint.Z m ≤ uint.Z s.p

/-- A commit's `UnsafeSave`, holding the batch lock of the backend of the names `γ` (its token, its
half of the stored index's mirror `mm.1`, its registration `applyRegd`): it reads `ci = k`, which
is not below the stored index, and stores `k` if it is not 0; the mirror follows. If `γ`'s backend
is the current one, what the commit persists is consistent (`commitOk` of the protocol's state);
if it is a retired one (D22 receiver epochs, S7f, 2026-10-23: an old backend's `Close`, which
commits through the server's hooks, one hooks object for every backend), its mirror's other half is
the invariant's `retiredInv`, at most `ciEff`, and the protocol's state is not its concern
(`commitOk` of a state made of the stored index). -/
theorem commit_save_au (γ : ApplyNames) (mm : MetaCI) (Ψ : w64 → IProp GF) :
    inv applyN (consInv γ) ⊢ ghostVar γ.mt (1 : Qp).half mm.1 -∗ token γ.pend -∗ applyRegd γ -∗
      (∀ (k : w64) (s : ApplyState),
        ⌜k ≠ W64 0 → uint.Z mm.1 ≤ uint.Z k⌝ -∗
        ⌜commitOk s (if k = W64 0 then mm.1 else k)⌝ -∗
        ghostVar γ.mt (1 : Qp).half (if k = W64 0 then mm.1 else k) -∗ token γ.pend -∗ Ψ k) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ.ci k ∗ (ciIdx γ.ci k ={∅, ⊤ \ ↑ciN}=∗ Ψ k) := by
  iintro #Hinv Hml Htok #Hreg HΨ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold consInv at Hi
  icases Hi with ⟨%π, %l, %s, %mi, %w, Hci, Hi, Hr⟩
  by_cases hπ : π = γ.ph
  rotate_left
  · -- retired (S7f): the mirror's other half is the registry's entry of `γ.ph`
    iunfold consRest at Hr
    icases Hr with ⟨Ha, Hret⟩
    iunfold applyRegd at Hreg
    icases Hreg with ⟨%i, #Hidx⟩
    icases reg_lookup γ.reg (l ++ [π]) i γ.ph $$ [$Ha $Hidx] with ⟨%Hli, Ha, -⟩
    have hmem : γ.ph ∈ l := by
      have h1 := List.mem_of_getElem? Hli
      rw [List.mem_append, List.mem_singleton] at h1
      exact h1.resolve_right (fun h => hπ h.symm)
    iunfold retiredInv at Hret
    icases (BigSepL.bigSepL_mem_acc hmem) $$ Hret with ⟨⟨%mr, Hmr, %Hmr⟩, Hret⟩
    icombine Hml Hmr gives %Heq
    obtain ⟨_, hmr⟩ := Heq
    subst hmr
    icases consCore_ci (γ.withPh π) s mi w $$ Hi with ⟨Hk, Hi⟩
    iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
    iintro Hmask
    iexists s.k
    iframe Hk
    iintro Hk
    imod Hmask with -
    imod ghostVar_update_halves (if s.k = W64 0 then mm.1 else s.k) $$ Hml Hmr with ⟨Hml, Hmr⟩
    ihave Hi := Hi $$ Hk
    have hbound : uint.Z (if s.k = W64 0 then mm.1 else s.k) ≤
        uint.Z (ciEff (γ.withPh π) s.k) := by
      by_cases hk : s.k = W64 0
      · rw [if_pos hk]; exact Hmr
      · rw [if_neg hk]; unfold ciEff; rw [if_neg hk]; exact Int.le_refl _
    imod Hclose $$ [Hci Hi Ha Hret Hmr] with -
    · inext
      iunfold consInv
      iexists π, l, s, mi, w
      iframe Hci Hi
      iunfold consRest
      iframe Ha
      iunfold retiredInv
      iapply Hret
      iexists (if s.k = W64 0 then mm.1 else s.k)
      iframe Hmr
      ipureintro; exact hbound
    imodintro
    have hmono : s.k ≠ W64 0 → uint.Z mm.1 ≤ uint.Z s.k := fun hk => by
      unfold ciEff at Hmr; rw [if_neg hk] at Hmr; exact Hmr
    have hsave : commitOk ⟨W64 0, (if s.k = W64 0 then mm.1 else s.k),
        (if s.k = W64 0 then mm.1 else s.k), false⟩ (if s.k = W64 0 then mm.1 else s.k) :=
      ⟨Int.le_refl _, Int.le_refl _⟩
    iapply HΨ $$ %s.k %_ %hmono %hsave Hml Htok
  subst hπ
  icases consParts_ph γ l s mi w $$ [$Hi $Hr] with ⟨Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · -- frozen (the stored-index window): `ci` is the stored index, which the commit stores again
    iunfold consFrozen at Hfz
    icases Hfz with ⟨Hk, Hs, Hsq, Hm, Hw, %Hf⟩
    obtain ⟨hmi, hk0, hps, hw, Hok⟩ := Hf
    icombine Hml Hm gives %Heq
    obtain ⟨_, hmm⟩ := Heq
    iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
    iintro Hmask
    iexists s.k
    iframe Hk
    iintro Hk
    imod Hmask with -
    imod Hclose $$ [Hci Hr Hk Hs Hsq Hm Hw] with -
    · inext
      iapply consInv_close γ l s s mi w (Int.le_refl _)
      iunfold curOwn
      iframe Hci Hr
      iright
      iunfold consFrozen
      iframe Hk Hm Hw
      isplitl [Hs]
      · iexact Hs
      isplitl [Hsq]
      · iexact Hsq
      ipureintro
      exact ⟨hmi, hk0, hps, hw, Hok⟩
    imodintro
    have hsave : commitOk s (if s.k = W64 0 then mm.1 else s.k) := by
      unfold commitOk
      unfold stOk ciEff at Hok
      simp only [hk0, ↓reduceIte] at Hok ⊢
      exact Hok
    have hmono : s.k ≠ W64 0 → uint.Z mm.1 ≤ uint.Z s.k := fun _ => by
      rw [hmm, hmi] <;> exact Int.le_refl _
    ihave Hml : ghostVar γ.mt (1 : Qp).half (if s.k = W64 0 then mm.1 else s.k) $$ [Hml]
    · rw [if_neg hk0, hmi, ← hmm]
      iexact Hml
    iapply HΨ $$ %s.k %s %hmono %hsave Hml Htok
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
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
  imod Hclose $$ [Hci Hr Hk Hs Hm Hw Hfzt] with -
  · inext
    iapply consInv_close γ l s s (if s.k = W64 0 then mm.1 else s.k) (w || decide (s.k ≠ W64 0))
      (Int.le_refl _)
    iunfold curOwn
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe Hfzt
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

/-- What the apply thread holds in the stored-index window opened at its state `s` (D22 the
stored-index window, 2026-10-23): a quarter of its state, a quarter of the stored index's mirror
(at `s.k`) and the window's token. -/
def freezeY (γ : ApplyNames) (s : ApplyState) : IProp GF :=
  iprop(ghostVar γ.st (1 : Qp).half.half s ∗ ghostVar γ.mt (1 : Qp).half.half s.k ∗ token γ.fz ∗
    curOwn γ)

/-- **The stored-index window opened** (D22 the stored-index window, 2026-10-23; `notes/decisions.md`,
"D22 the stored-index window carried out"): a commit's `UnsafeSave` as in `commit_save_au`, at the
request of the apply thread at `s` (`ci = s.k`, not 0; nothing in flight), which gives its state:
the commit stores `s.k` and the protocol is frozen (`consFrozen`); the apply thread gets
`freezeY γ s`. -/
theorem commit_freeze_au (γ : ApplyNames) (mm : MetaCI) (s : ApplyState) (Ψ : w64 → IProp GF)
    (hk0 : s.k ≠ W64 0) (hps : s.pending = false) :
    inv applyN (consInv γ) ⊢ ghostVar γ.mt (1 : Qp).half mm.1 -∗ token γ.pend -∗
      applyThread γ s -∗
      (∀ (k : w64) (s' : ApplyState),
        ⌜k ≠ W64 0 → uint.Z mm.1 ≤ uint.Z k⌝ -∗
        ⌜commitOk s' (if k = W64 0 then mm.1 else k)⌝ -∗
        ghostVar γ.mt (1 : Qp).half (if k = W64 0 then mm.1 else k) -∗ token γ.pend -∗
        freezeY γ s -∗ Ψ k) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ.ci k ∗ (ciIdx γ.ci k ={∅, ⊤ \ ↑ciN}=∗ Ψ k) := by
  iintro #Hinv Hml Htok Hst HΨ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, Hw, %Hmk, %Hk0, %Hw0, Hrel, Hfzt⟩
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  icombine Hml Hm gives %Heq
  obtain ⟨_, hmi⟩ := Heq
  subst hmi
  iunfold flightInv at Hrel
  rw [hps]
  icases Hrel with %Hok
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod ghostVar_update_halves s.k $$ Hml Hm with ⟨Hml, Hm⟩
  imod ghostVar_update true $$ Hw with Hw
  icases (ghostVar_split_half γ.mt (1 : Qp).half s.k).1 $$ Hm with ⟨Hm, Hmq⟩
  icases (ghostVar_split_half γ.st (1 : Qp).half s).1 $$ Hst with ⟨Hsq, Hsq'⟩
  imod Hclose $$ [Hci Hr Hk Hs Hsq Hm Hw] with -
  · inext
    iapply consInv_close γ l s s s.k true (Int.le_refl _)
    iframe Hci Hr
    iright
    iunfold consFrozen
    iframe Hk Hm Hw
    isplitl [Hs]
    · iexact Hs
    isplitl [Hsq]
    · iexact Hsq
    ipureintro
    exact ⟨rfl, hk0, hps, rfl, Hok⟩
  imodintro
  have hsave : commitOk s (if s.k = W64 0 then mm.1 else s.k) := by
    unfold commitOk
    unfold stOk ciEff at Hok
    simp only [hk0, ↓reduceIte] at Hok ⊢
    exact Hok
  ihave Hml : ghostVar γ.mt (1 : Qp).half (if s.k = W64 0 then mm.1 else s.k) $$ [Hml]
  · rw [if_neg hk0]
    iexact Hml
  iapply HΨ $$ %s.k %s %(Hmk) %hsave Hml Htok [Hsq' Hmq Hfzt Hcu]
  unfold freezeY
  iframe

/-- **The stored-index window closed** (D22 the stored-index window, 2026-10-23): the holder's
`freezeY γ s` gives the apply thread its state `s` back, the protocol out of the window. -/
theorem unfreeze (γ : ApplyNames) (s : ApplyState) :
    inv applyN (consInv (GF := GF) γ) ⊢ freezeY γ s ={⊤}=∗ applyThread γ s := by
  iintro #Hinv HY
  iunfold freezeY at HY
  icases HY with ⟨Hsq, Hmq, Htok, Hcu⟩
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  · iunfold consInvAt at Hi
    icases Hi with ⟨-, -, -, -, -, -, -, -, Hfzt⟩
    iexfalso
    iapply token_exclusive $$ Htok Hfzt
  iunfold consFrozen at Hfz
  icases Hfz with ⟨Hk, Hs, Hsq0, Hm, Hw, %Hf⟩
  obtain ⟨hmi, hk0, hps, hw, Hok⟩ := Hf
  icombine Hsq Hsq0 gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  subst hmi
  ihave Hst := (ghostVar_split_half γ.st (1 : Qp).half s).2 $$ [$Hsq $Hsq0]
  ihave Hmh := (ghostVar_split_half γ.mt (1 : Qp).half s.k).2 $$ [$Hmq $Hm]
  imod Hclose $$ [Hci Hr Hk Hs Hmh Hw Htok] with -
  · inext
    iapply consInv_close γ l s s s.k w (Int.le_refl _)
    iframe Hci Hr
    ileft
    iunfold consInvAt
    iframe
    iunfold flightInv
    rw [hps]
    ipureintro
    refine ⟨fun _ => Int.le_refl _, fun h => absurd h hk0, ?_, Hok⟩
    intro h
    rw [hw] at h
    cases h
  imodintro
  iunfold applyThread
  iframe Hcu
  iexact Hst

/-! ## The backend's swap (D22 receiver epochs, S7f) -/

/-- **The backend's swap** (D22 receiver epochs, S7f, 2026-10-23; `notes/decisions.md`, "D22
receiver epochs, S7f carried out"), at the linearization point of `ci.SetBackend(newbe)` in
`applySnapshot` (its store of `ci = 0`: `consistentIndex.SetBackend.spec`'s update): the apply
thread, at `s` out of the window, moves the protocol to the new backend's physical names `π'` (its
mirror `π'.mt`, whole, at the meta keys it was opened with `π'.m0`, its read view's `π'.wr`, whole,
unwritten), at the state `s'` (`ci = 0`, nothing in flight, `stOk`); the old backend's names are
retired: their mirror's invariant half joins `retiredInv`, at most the new `ciEff` (`π'.m0.1`,
which must not be below the old one: `hle`), so the old backend's commits (its `Close`) still go
through `commit_save_au`. The apply thread gets its state at the new names, the new batch lock's
half of the mirror and the new names' registration (`applyRegd`), for the new backend's
`batchLockInv`. -/
theorem ci_swap_au (γ : ApplyNames) (s s' : ApplyState) (π' : ApplyPhys) (Φ : IProp GF)
    (hk' : s'.k = W64 0) (hps' : s'.pending = false) (hok : stOk (γ.withPh π') s')
    (hle : uint.Z (ciEff γ s.k) ≤ uint.Z π'.m0.1) :
    inv applyN (consInv γ) ⊢ applyThread γ s -∗ ghostVar π'.mt 1 π'.m0.1 -∗
      ghostVar π'.wr 1 false -∗
      (applyThread (γ.withPh π') s' -∗ ghostVar π'.mt (1 : Qp).half π'.m0.1 -∗
        applyRegd (γ.withPh π') -∗ Φ) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k0 : w64, ciIdx γ.ci k0 ∗ (ciIdx γ.ci (W64 0) ={∅, ⊤ \ ↑ciN}=∗ Φ) := by
  iintro #Hinv Hst Hmt' Hwr' HΦ
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  iunfold applyThread at Hst
  icases Hst with ⟨Hst, Hcu⟩
  icases consInv_open γ $$ [$Hi $Hcu] with ⟨Hcu, Hci, %l, %s0, %mi, %w, Hi, Hr⟩
  icases Hi with (Hi | Hfz)
  rotate_left
  · iexfalso; iapply frozen_thread_false $$ [$Hfz $Hst]
  iunfold consInvAt at Hi
  icases Hi with ⟨Hk, Hs, Hm, -, %Hmk, %Hk0, %Hw0, -, Hfzt⟩
  icombine Hst Hs gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  have hmi : uint.Z mi ≤ uint.Z (ciEff γ s.k) := consInvAt_mi γ s mi w Hmk Hk0 Hw0
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists s.k
  iframe Hk
  iintro Hk
  imod Hmask with -
  imod ghostVar_update_halves s' $$ Hst Hs with ⟨Hst, Hs⟩
  iunfold curOwn at Hcu Hci
  imod ghostVar_update_halves π' $$ Hcu Hci with ⟨Hcu, Hci⟩
  iunfold consRest at Hr
  icases Hr with ⟨Ha, Hret⟩
  imod monoListAuthOwn_update_app [π'] $$ Ha with ⟨Ha, #Hlb⟩
  ihave #Hidx := monoListIdxOwn_get (l ++ [γ.ph]).length π' (by simp) $$ Hlb
  icases (ghostVar_split_half π'.mt 1 π'.m0.1).1 $$ Hmt' with ⟨Hm1, Hm2⟩
  ihave Hret := retiredInv_mono l _ π'.m0.1 hle $$ Hret
  imod Hclose $$ [Hci Hk Hs Hm1 Hwr' Hfzt Ha Hret Hm] with -
  · inext
    iunfold consInv
    iexists π', l ++ [γ.ph], s', π'.m0.1, false
    iframe Hci
    isplitl [Hk Hs Hm1 Hwr' Hfzt]
    · ileft
      iunfold consInvAt
      rw [hk']
      iframe Hk Hs Hm1 Hwr' Hfzt
      iunfold flightInv
      rw [hps']
      ipureintro
      exact ⟨fun h => absurd rfl h, fun _ => rfl, fun _ => rfl, hok⟩
    iunfold consRest
    iframe Ha
    iunfold retiredInv
    iapply BigSepL.bigSepL_snoc.2
    rw [hk']
    have hc : ciEff (γ.withPh π') (W64 0) = π'.m0.1 := by unfold ciEff; rw [if_pos rfl]
    rw [hc]
    iunfold retiredInv at Hret
    iframe Hret
    iexists mi
    iframe Hm
    ipureintro; omega
  imodintro
  iapply HΦ $$ [Hst Hcu] Hm2
  · iunfold applyThread
    iunfold curOwn
    iframe Hst Hcu
  iunfold applyRegd
  iexists (l ++ [γ.ph]).length
  iexact Hidx

/-! ## The protocol's allocation -/

/-- **The protocol's allocation** (D22 receiver epochs, S7f, 2026-10-23; for whoever discharges
`bootstrap`'s contract, `InvBoot.lean`'s `bootOk`: its `inv applyN (consInv γA)`,
`applyThread γA ⟨0, 0, 0, false⟩` and the batch lock's `batchLockInv γA`, whose names exist before
the backend does): over a consistent index holding 0 (`NewConsistentIndex`'s), for a backend opened
at the meta keys `m0`, fresh names with the registry holding them alone; the apply thread at
`ci = 0`, processed through the stored index; the batch lock's half of the mirror, its token and
its registration. -/
theorem consInv_alloc (γci : CINames) (m0 : MetaCI) (Ms : CoPset) :
    ciIdx (GF := GF) γci (W64 0) ⊢ |={Ms}=> ∃ γ : ApplyNames, ⌜γ.ci = γci ∧ γ.m0 = m0⌝ ∗
      inv applyN (consInv γ) ∗ applyThread γ ⟨W64 0, m0.1, W64 0, false⟩ ∗
      ghostVar γ.mt (1 : Qp).half m0.1 ∗ token γ.pend ∗ applyRegd γ := by
  iintro Hk
  imod (ghostVar_alloc (GF := GF) (⟨W64 0, m0.1, W64 0, false⟩ : ApplyState)) with ⟨%γst, Hst⟩
  imod (ghostVar_alloc (GF := GF) m0.1) with ⟨%γmt, Hmt⟩
  imod (ghostVar_alloc (GF := GF) false) with ⟨%γwr, Hwr⟩
  imod token_alloc with ⟨%γpend, Hpend⟩
  imod token_alloc with ⟨%γfz, Hfz⟩
  imod (ghostVar_alloc (GF := GF) (⟨γmt, γwr, γpend, m0⟩ : ApplyPhys)) with ⟨%γcur, Hcur⟩
  imod (mono_list_own_alloc (GF := GF) [(⟨γmt, γwr, γpend, m0⟩ : ApplyPhys)])
    with ⟨%γreg, Ha, #Hlb⟩
  ihave #Hidx := monoListIdxOwn_get (γ := γreg) 0 (⟨γmt, γwr, γpend, m0⟩ : ApplyPhys) rfl $$ Hlb
  icases (ghostVar_split_half γst 1 (⟨W64 0, m0.1, W64 0, false⟩ : ApplyState)).1 $$ Hst
    with ⟨Hst1, Hst2⟩
  icases (ghostVar_split_half γmt 1 m0.1).1 $$ Hmt with ⟨Hmt1, Hmt2⟩
  icases (ghostVar_split_half γcur 1 (⟨γmt, γwr, γpend, m0⟩ : ApplyPhys)).1 $$ Hcur
    with ⟨Hcur1, Hcur2⟩
  iexists (⟨γci, γst, γfz, γcur, γreg, ⟨γmt, γwr, γpend, m0⟩⟩ : ApplyNames)
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hk Hst1 Hmt1 Hwr Hfz Hcur1 Ha]
  · iapply inv_alloc applyN Ms
    inext
    iunfold consInv
    iexists (⟨γmt, γwr, γpend, m0⟩ : ApplyPhys), ([] : List ApplyPhys),
      (⟨W64 0, m0.1, W64 0, false⟩ : ApplyState), m0.1, false
    iframe Hcur1
    isplitl [Hk Hst1 Hmt1 Hwr Hfz]
    · ileft
      iunfold consInvAt
      iframe Hk Hst1 Hmt1 Hwr Hfz
      iunfold flightInv
      ipureintro
      refine ⟨fun h => absurd rfl h, fun _ => rfl, fun _ => rfl, ?_⟩
      unfold stOk ciEff
      simp only [↓reduceIte]
      refine ⟨by word, Int.le_refl _⟩
    iunfold consRest
    rw [List.nil_append]
    iframe Ha
    iunfold retiredInv
    iapply BigSepL.bigSepL_nil.2
    itrivial
  imodintro
  iunfold applyThread
  iunfold curOwn
  iframe Hst2 Hcur2 Hmt2 Hpend
  iunfold applyRegd
  iexists 0
  iexact Hidx

end defs

end EtcdGrove
end Perennial
