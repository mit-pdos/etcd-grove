/-
The etcd server as its apply thread uses it: the shared vocabulary of the specs of
`applyEntryNormal`, `apply`, `applyEntries` and the applier's contract. Lean-first (no Rocq
counterpart); the protocol is `InvApply.lean`, the hook `InvServer.lean`.

**The applier.** `apply.Apply` (the `UberApplier`'s dispatch, through mvcc, the lessor, auth,
...) and `applyConfChange` (the cluster's membership) write the backend's batch transaction.
What the protocol needs of them is their contract (`Spec/.../apply/Apply.lean`,
`Spec/.../EtcdServer__applyConfChange.lean`): an entry's writes happen in one critical section
of the batch lock, which runs the post-lock hook first, or not at all. Since the apply package's
unit 3 (2026-10-12) the applier is the apply package's (`apply.applierFor ua E`, a definition,
`apply/InvUber.lean`; `apply.Apply` proved): its environment `E` (the store, its ghost names,
the batch lock's invariant `E.P` and hook `E.f`) is a parameter of `isServer`, whose fields pin
`E.P = batchLockInv γ TM` and `E.f` the server's hook. The apply thread owns the applier's KV
state (`srvApplyKV s E x`: the uber-applier's current chain and the KV's committed log, at the
server's `uberApply`).

**What a batch does to the KV** (pure): one normal entry by `entryStep` (no data: nothing;
else its request decoded, `apply.applyStep`), a batch by `entriesStep c` (each normal entry
applied with `v3` iff it is above the consistent index `c` the batch starts at; a conf change
leaves the KV), under the entries' shapes (`logShape`), each normal entry `entryOk` at the state
it meets (`entryOk_of_shape`, at the apply thread's small log, `srvApplyKV_small`; until D19c's
move, 2026-10-18, `entriesOk c`: `entryOk` at every state a run of the batch reaches it in).

**The server** (`isServer s γ ci TM E`, persistent): the fields the apply thread reads, their
values and contracts. `uberApply` is replaced by `applySnapshot` (not translated), on the
apply thread; here it is read-only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Wait
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCfgView
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Perennial.Proof.errors
public import Proof.go_etcd_io.etcd.pkg.v3.notify.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.etcdserver

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvLgAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"lg" s
abbrev srvWAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"w" s
abbrev srvUberApplyAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"uberApply" s
abbrev srvBemuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"bemu" s
abbrev srvBeAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"be" s
abbrev srvLessorAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"lessor" s
abbrev srvFirstCommitAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"firstCommitInTerm" s
abbrev srvAlarmStoreAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"alarmStore" s
abbrev srvClusterAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"cluster" s
abbrev srvCfgAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"Cfg" s
abbrev srvQuotaAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"QuotaBackendBytes" (srvCfgAddr s)
abbrev srvTermAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"term" s
abbrev srvLgMuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"lgMu" s
abbrev srvMemberIDAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"memberID" s
abbrev srvLeadAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"lead" s
abbrev cfgElectionTicksAddr (c : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"ElectionTicks" c
abbrev cfgTickMsAddr (c : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"TickMs" c

abbrev epConfStateAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"confState" ep
abbrev epAppliedTAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"appliedt" ep
abbrev epAppliedIAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"appliedi" ep

abbrev taEntriesAddr (ta : Loc) : Loc := structFieldRef toApply go!"entries" ta
abbrev taRaftAdvancedCAddr (ta : Loc) : Loc := structFieldRef toApply go!"raftAdvancedC" ta

end addrs

/-- A batch of committed entries as raft hands them to the apply thread: consecutive indices
from `f0` (not 0), with no overflow past the last; each a normal entry or a (v1) conf change
(etcd proposes no others: `apply` panics on any other type). -/
def entriesFrom [FfiSyntax] (f0 : w64) (ms : List EntryModel) : Prop :=
  0 < uint.Z f0 ∧ uint.Z f0 + ms.length < 2 ^ 64 ∧
  ∀ (n : Nat) (m : EntryModel), ms[n]? = some m →
    uint.Z m.index = uint.Z f0 + n ∧
      (m.typ = W32 0 ∨ (m.typ = W32 1 ∧ isConfChangeEncoding m.data))

/-- The apply thread's relation between the protocol's state `st` and the applied index `a`
(`ep.appliedi`): out of flight, and processed through the larger of `ci` and `a`. It holds
when the server starts (the applied index is the snapshot's, at most the stored consistent
index, through which the backend holds everything) and `applyEntries` keeps it. -/
def loopOk (γ : ApplyNames) (st : ApplyState) (a : w64) : Prop :=
  st.pending = false ∧ uint.Z st.p = max (uint.Z (ciEff γ st.k)) (uint.Z a)

/-! ## What a batch of entries does to the KV (pure) -/

/-- **The premise on a normal entry** at the KV state `x` it meets: no data (`applyEntryNormal`
skips it), or its data decode (`irrDecode`: the proposer marshalled an `InternalRaftRequest`) to
a request with an id or a header (`irrId`: else `apply.Apply` panics; pre-3.0 entries), neither a
compaction nor empty (`dispatchOk`), and satisfying the txn package's premises at `x.log`
(`rqOk`: `apply.Apply.spec`'s). -/
def entryOk (x : apply.ApplyKV) (m : EntryModel) : Prop :=
  m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧ (∃ id, apply.irrId rq = some id) ∧
    apply.rqOk x.log rq ∧ apply.dispatchOk x.chain.authOn rq

/-- **An entry's premise at a small log, from its shape** (D19c's move, 2026-10-18): the KV
invariant keeps every committed entry's shape (`entryShape`), and the apply thread's log is
small (`srvApplyKV_small`), so the size clauses hold there (`rqSmall_of_small`). -/
theorem entryOk_of_shape [FfiSyntax] (x : apply.ApplyKV) (m : EntryModel) (hs : entryShape m)
    (ht : m.typ = W32 0) (hl : x.log.length ≤ mvcc.logCh x.log + 2)
    (hc : mvcc.logCh x.log < 2 ^ 48) : entryOk x m := by
  rcases hs.1 ht with hd | ⟨rq, hdec, hid, hsh⟩
  · exact Or.inl hd
  · exact Or.inr ⟨rq, hdec, hid, hsh.2 x.log (rqSmall_of_small x.log rq hl hc), hsh.1 _⟩

/-- **What `applyEntryNormal` does to the KV** with the normal entry `m` (`v3`: above `ci`): no
data, nothing (`skipped`); else its decoded request through `apply.Apply` (`applyStep`). -/
def entryStep (m : EntryModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) :
    Prop :=
  if m.data = [] then x' = x ∧ out = .skipped
  else ∃ rq id, apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧
    apply.applyStep rq v3 x x' out

/-- The backend's outcome extends the log (2026-10-14, unit C2a). -/
theorem backendStep_prefix (rq : apply.IRRModel) (log : mvcc.Log) (o : apply.Outcome)
    (h : apply.backendStep rq log o) : log <+: o.logAfter log := by
  have hc : ∀ pend, log <+: mvcc.commitLog log pend := by
    intro pend; unfold mvcc.commitLog; split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  unfold apply.backendStep at h
  split at h
  · obtain ⟨op, -, h⟩ := h
    rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact List.prefix_refl _
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  · obtain ⟨op, -, rfl⟩ := h
    exact hc _
  · subst h; exact List.prefix_refl _
  · obtain ⟨t, -, h⟩ := h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact List.prefix_refl _
    · exact hc _
  · obtain ⟨pend, -, rfl⟩ := h
    exact hc _
  · exact h.elim
  · exact h.elim
  · rcases h with rfl | rfl <;> exact List.prefix_refl _

/-- Through any chain, the outcome extends the log (2026-10-14, unit C2a). -/
theorem chainStep_prefix (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log)
    (o : apply.Outcome) (h : apply.chainStep apply.backendStep c rq log o) :
    log <+: o.logAfter log := by
  induction c generalizing o with
  | backend => exact backendStep_prefix rq log o h
  | corrupt c ih =>
    unfold apply.chainStep at h
    split at h
    · subst h; exact List.prefix_refl _
    · exact ih o h
  | capped c ih =>
    unfold apply.chainStep at h
    split at h
    · subst h; exact List.prefix_refl _
    · split at h
      · rcases h with rfl | h
        · exact List.prefix_refl _
        · exact ih o h
      · exact ih o h
  | auth _ c ih =>
    unfold apply.chainStep at h
    split at h
    · rcases h with ⟨-, rfl⟩ | h
      · exact List.prefix_refl _
      · exact ih o h
    · exact ih o h
  | quota c ih =>
    unfold apply.chainStep at h
    exact ih o h

/-- `apply.Apply`'s step extends the KV's log (2026-10-14, unit C2a). -/
theorem applyStep_prefix (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (h : apply.applyStep rq v3 x x' out) : x.log <+: x'.log := by
  cases out with
  | skipped => obtain ⟨-, rfl⟩ := h; exact List.prefix_refl _
  | rejected => obtain ⟨-, rfl⟩ := h; exact List.prefix_refl _
  | dispatched o skip =>
    obtain ⟨-, hd, hl, -⟩ := h
    rw [hl]
    unfold apply.dispatchStep at hd
    split at hd
    · subst hd; exact List.prefix_refl _
    · split at hd
      · exact chainStep_prefix _ rq x.log o hd
      · rw [hd]; exact List.prefix_refl _

/-- **What `apply` does to the KV with one entry** of a batch that starts at the consistent
index `c`: a normal entry by `entryStep`, with `v3` iff it is above `c` (an entry at or below is
replayed, `ApplyV2storeOnly`); a conf change leaves the KV. -/
def batchStep (c : w64) (m : EntryModel) (x x' : apply.ApplyKV) : Prop :=
  if m.typ = W32 0 then ∃ out, entryStep m (decide (uint.Z c < uint.Z m.index)) x x' out
  else x' = x

/-- **What a batch does to the KV** from the consistent index `c`: the entries' `batchStep`s in
order (a relation: `applyStep` is). -/
def entriesStep (c : w64) : List EntryModel → apply.ApplyKV → apply.ApplyKV → Prop
  | [], x, x' => x' = x
  | m :: ms, x, x' => ∃ x1, batchStep c m x x1 ∧ entriesStep c ms x1 x'

/-- The entries of a batch above the applied index `ai` (those `applyEntries` hands to
`apply`). -/
def unapplied (ai : w64) (ms : List EntryModel) : List EntryModel :=
  ms.filter (fun m => decide (uint.Z ai < uint.Z m.index))

theorem entriesStep_append (c : w64) (l : List EntryModel) (m : EntryModel)
    (x x1 x2 : apply.ApplyKV) (h1 : entriesStep c l x x1) (h2 : batchStep c m x1 x2) :
    entriesStep c (l ++ [m]) x x2 := by
  induction l generalizing x with
  | nil => simp only [entriesStep] at h1; subst h1; exact ⟨x2, h2, rfl⟩
  | cons m' l ih =>
    obtain ⟨y, hy, hl⟩ := h1
    exact ⟨y, hy, ih y hl⟩

theorem entriesStep_take_succ (c : w64) (ms : List EntryModel) (j : Nat) (m : EntryModel)
    (x xj x1 : apply.ApplyKV) (hm : ms[j]? = some m) (h1 : entriesStep c (ms.take j) x xj)
    (h2 : batchStep c m xj x1) : entriesStep c (ms.take (j + 1)) x x1 := by
  rw [List.take_add_one, hm, Option.toList_some]
  exact entriesStep_append c _ m x xj x1 h1 h2

/-- The entries above `ai` of a batch whose indices count up from `b`: those from the offset
`ai + 1 - b` on. -/
theorem unapplied_eq_drop (ai : w64) (ms : List EntryModel) (b : Int)
    (h : ∀ (n : Nat) (m : EntryModel), ms[n]? = some m → uint.Z m.index = b + n) :
    unapplied ai ms = ms.drop (uint.Z ai + 1 - b).toNat := by
  induction ms generalizing b with
  | nil => simp [unapplied]
  | cons m ms ih =>
    have hm : uint.Z m.index = b := by simpa using h 0 m rfl
    have ht : ∀ (n : Nat) (m' : EntryModel), ms[n]? = some m' → uint.Z m'.index = (b + 1) + n := by
      intro n m' hn
      have := h (n + 1) m' (by simpa using hn)
      push_cast at this; omega
    have ih' := ih (b + 1) ht
    unfold unapplied at ih' ⊢
    by_cases hb : uint.Z ai < b
    · rw [List.filter_cons_of_pos (by simp [hm, hb]), ih']
      rw [show (uint.Z ai + 1 - b).toNat = 0 by omega, show (uint.Z ai + 1 - (b + 1)).toNat = 0 by omega]
      rfl
    · rw [List.filter_cons_of_neg (by simp [hm, hb]), ih']
      rw [show (uint.Z ai + 1 - b).toNat = (uint.Z ai + 1 - (b + 1)).toNat + 1 by omega]
      rfl

/-- **The trace of a batch**: the states a run of `entriesStep` passes through. -/
theorem entriesStep_trace (c : w64) (ms : List EntryModel) (x x' : apply.ApplyKV)
    (h : entriesStep c ms x x') :
    ∃ xs : List apply.ApplyKV, xs.length = ms.length + 1 ∧ xs[0]? = some x ∧
      xs[ms.length]? = some x' ∧
      ∀ (n : Nat) (m : EntryModel) (y y' : apply.ApplyKV), ms[n]? = some m →
        xs[n]? = some y → xs[n + 1]? = some y' → batchStep c m y y' := by
  induction ms generalizing x with
  | nil => simp only [entriesStep] at h; subst h; exact ⟨[x'], rfl, rfl, rfl, by simp⟩
  | cons m ms ih =>
    obtain ⟨x1, h1, hr⟩ := h
    obtain ⟨xs, hl, h0, hL, hs⟩ := ih x1 hr
    refine ⟨x :: xs, by simp [hl], rfl, by simpa using hL, ?_⟩
    intro n m' y y' hm hy hy'
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm hy
      simp only [Nat.zero_add, List.getElem?_cons_succ, h0, Option.some.injEq] at hy'
      subst hm hy hy'; exact h1
    | succ n =>
      simp only [List.getElem?_cons_succ] at hm hy hy'
      exact hs n m' y y' hm hy hy'

-- The server's atomics' invariants' namespace `srvN`: `InvRequest.lean` (2026-10-13).

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

-- The server's wait: `waitInv` (`InvRequest.lean`, the registry's contract, in `srvFieldsAt`);
-- the apply thread's reader of it, `waitOk` (`apply/Wait.lean`, in `srvApplyKV`).

/-- The server's atomic `s.lead` (the leader's id, which raft's goroutine stores; the apply
thread loads it in `isLeader`). -/
def srvLeadInv (s : Loc) : IProp GF :=
  iprop(inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvLeadAddr s) (DFrac.own 1) v))

instance srvLeadInv_persistent (s : Loc) : Persistent (srvLeadInv (GF := GF) s) := by
  unfold srvLeadInv; infer_instance

/-- A reader slot of the server's logger lock `s.lgMu` (a `*sync.RWMutex` that is only ever
read-locked, around reading `s.lg`, which never changes: its invariant is `True`): Perennial's
`RWMutex` admits a bounded number of readers, so `RLock` needs a token, which the apply thread
holds (`Logger`). Not persistent. -/
def srvLgReader (s : Loc) : IProp GF :=
  iprop(∃ mu : Loc, srvLgMuAddr s ↦□ mu ∗ sync.ownRWMutex mu (fun _ => iprop(True)))

/-- The values of the server's fields the apply thread reads, and the post-lock hook. -/
structure SrvFields where
  lg : Loc
  w : GoInterface
  lessor : GoInterface
  hook : val
  firstCommit : Loc
  alarmStore : Loc
  cluster : Loc
  quota : w64
  lgMu : Loc
  memberID : w64
  electionTicks : w64
  tickMs : w64

/-- The server's KV invariants (persistent; 2026-10-14, unit T1): the KV invariant, the
certificates', raft's committed log's; the store's certificates at the KV's names. -/
def srvKVInvs (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(kvInv γr.raft γr.kv ∗ kvCertInv γr.raft γr.kv ∗ srvRaftLogInv γr.raft ∗
    ⌜E.γ.cok = γr.kv.cok⌝)

instance srvKVInvs_persistent (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvKVInvs (GF := GF) E γr) := by
  unfold srvKVInvs; infer_instance

/-- The server's two atomics the apply thread stores (read by other goroutines): the applied
index, in its invariant with the ghost applied index and the applied logs (`srvAppliedInv`, the
request path's unit 4b; any value until then), and the term. -/
def srvAtomics (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvAppliedInv s E γr ∗
    inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) v) ∗
    srvKVInvs E γr)

instance srvAtomics_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAtomics (GF := GF) s E γr) := by
  unfold srvAtomics; infer_instance

/-- The entries `ents` are modelled by `ms` (persistent). -/
def entriesAt (ents : List Loc) (ms : List EntryModel) : IProp GF :=
  iprop(⌜ents.length = ms.length⌝ ∗
    □ (∀ (n : Nat) (e : Loc) (m : EntryModel), ⌜ents[n]? = some e⌝ -∗ ⌜ms[n]? = some m⌝ -∗
      entryAt e m))

instance entriesAt_persistent (ents : List Loc) (ms : List EntryModel) :
    Persistent (entriesAt (GF := GF) ents ms) := by
  unfold entriesAt; infer_instance

/-- (D22 S-h, 2026-10-20; S-0's amendment) **The applied term after a batch** `es` applied from the
term `at0`: unchanged if no entry was applied, else the last applied entry's (`applyEntries`
sets `ep.appliedt` only for a non-empty batch). -/
def termAfter (at0 : w64) (es : List EntryModel) (at' : w64) : Prop :=
  (es = [] ∧ at' = at0) ∨ es.getLast?.map EntryModel.term = some at'

/-- (D22 S-h) **`at'` is the last term of the applied log `A`**, if any (`applyRes`'s). -/
def lastTermIs (A : List EntryModel) (at' : w64) : Prop :=
  A = [] ∨ A.getLast?.map EntryModel.term = some at'

theorem lastTermIs_append {A es : List EntryModel} {t t' : w64} (h1 : lastTermIs A t)
    (h2 : termAfter t es t') : lastTermIs (A ++ es) t' := by
  unfold lastTermIs termAfter at *
  rcases h2 with ⟨rfl, rfl⟩ | h2
  · simpa using h1
  · right
    rw [List.getLast?_append]
    cases hl : es.getLast? with
    | none => rw [hl] at h2; simp at h2
    | some e => rw [hl] at h2; simpa using h2

-- `resultOk ar` (the server's, until the apply package's unit 3): `apply.resultErrOk`
-- (`apply/InvUber.lean`), the same definition, which `apply.Apply`'s spec returns.

/-- (D19i part 1) `ep.confState`: `nil`, or a `*pb.ConfState` read-only for good (raft's
`ApplyConfChange` answer, or the start snapshot's), as `CreateSnapshot` reads it (persistent). -/
def epCsOk (cs : Loc) : IProp GF :=
  iprop(⌜cs = null⌝ ∨ ∃ c : ConfStateM, csPts cs DFrac.discard c false)

instance epCsOk_persistent (cs : Loc) : Persistent (epCsOk (GF := GF) cs) := by
  unfold epCsOk; infer_instance

/-- A snapshot's conf state, read-only (`csOptA` at `□`), is a valid `ep.confState`. -/
theorem epCsOk_of_csOptA (p : Loc) (c : ConfStateM) :
    ⊢ csOptA (GF := GF) p DFrac.discard c -∗ epCsOk p := by
  iintro H
  iunfold csOptA at H
  iunfold epCsOk
  icases H with (⟨%Hn, -⟩ | #H | #H)
  · ileft; ipureintro; exact Hn
  · iright; iexists c; iexact H
  · iright; iexists c
    iunfold csPts at H
    icases H with ⟨%sv, %sl, %so, %sn, %pa, H⟩
    iNamed H
    iunfold csPts
    iexists sv, sl, so, sn, pa
    simp only [named]
    iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
    ipureintro; exact ⟨Hnn, fun h => by cases h⟩

/-- (D19i part 1) `ep.confState`, the apply thread's: the field, and its value `epCsOk`. -/
def epConfState (ep cs : Loc) : IProp GF :=
  iprop(epConfStateAddr ep ↦ cs ∗ epCsOk cs)

end defs

section defs_lc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! At `HeapGS HasLC.hasLC GF` (later credits), as the notifier `s.firstCommitInTerm`'s
predicate is (Perennial's channel specs are), and the apply package's. -/

/-- **The server's grant guard** (D19n, 2026-10-18; D19q: the workload's): the predicate on lease
ids the server gives its lessor (`lease.NewLessor`'s `GA`): only a lease that meets it can be
granted, and the lessor's `expiredC` carries only such leases. The workload's `grant`
(`SrvWorkload.grant`): `False` for the leases-off `putgetWorkload`, whose `plainReq` admits no
`LeaseGrant`, so `run`'s receive from `expiredC` is dead. -/
def srvGrantGuard (W : SrvWorkload) : w64 → IProp GF := fun id => iprop(⌜W.grant id⌝)

/-- `l` is a `lease.Lessor` whose `Promote` returns (in memory: no backend writes); and
(2026-10-13, the request path's unit 4c: the server's `run`) whose `Demote` returns and whose
`ExpiredLeasesC` returns a channel of slices of expired leases, each carrying a lease of the
lessor's grant guard, the workload `W`'s `srvGrantGuard` (D19n, D19q; until D19n a bag with no
logical content, which `run` passed to the names-only `revokeExpiredLeases`). And (D19q, until the
lease path is proved: `revokeExpiredLeases` with a true spec) the workload grants no lease
(`W.noGrant`), so nothing is sent on that channel. A trust-boundary contract (the lessor is
names-only). -/
def lessorOk (W : SrvWorkload) (l : GoInterface) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜l = GoInterface.ok li⌝ ∗
    □ (∀ d : w64,
      {{ True }} (App (Val #(methods li.ty go!"Promote" li.v)) (Val #d)) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods li.ty go!"Demote" li.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods li.ty go!"ExpiredLeasesC" li.v)) (Val #()))
      {{ (c : GoChan), RET #c; ∃ γc : ChanNames,
        isChanBag γc c (V := GoSlice) (fun _ => iprop(∃ id : w64, srvGrantGuard W id)) }}) ∗
    ⌜W.noGrant⌝)

instance lessorOk_persistent (W : SrvWorkload) (l : GoInterface) :
    Persistent (lessorOk (GF := GF) W l) := by
  unfold lessorOk; infer_instance

/-- **The apply thread's right to `s.forceDiskSnapshot`** (D14i, 2026-10-17): what the applier's
`ForceSnapshot` takes (`apply.isSnapshotServer`, the environment's `E.FS`). -/
def srvFS (s : Loc) : IProp GF :=
  iprop(∃ f : Bool, structFieldRef EtcdServer go!"forceDiskSnapshot" s ↦ f)

/-- **The resources the consistent index reads under** (D14i): the apply protocol's state, not
pending, with the backend's owner share (`applyBackend`), as `wp_ci_get` takes them; the
environment's `E.ciC`. -/
def srvCiC (γ : ApplyNames) (ci : Loc) (C : IProp GF) : Prop :=
  ∃ (st : ApplyState) (b : GoInterface),
    C = iprop(applyThread γ st ∗ applyBackend γ ci b) ∧ st.pending = false

/-- The apply environment's threaded resources are the server's (D14i); (D22, 2026-10-23) its rest
buckets' resource the backend's tracked buckets with the cluster `cl`'s in-memory members, its
write right the tracked buckets' half (`srvRestOwn`, `srvRestRW`); (D22 receiver epochs, S7c,
2026-10-23) both with the server's objects' backend parts `H` (`srvRestOwnH`, `srvRestRWH`): the
alarm store's, the auth store's, the lessor's and (S7e) the cluster's, on the store's backend
(`srvObjsOn`). -/
def srvEnvOk (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (cl : Loc) : Prop :=
  E.FS = srvFS s ∧ E.ciC = srvCiC γ ci ∧
    ∃ (γB : backend.BNames) (H : IProp GF), E.RO = srvRestOwnH γB cl H ∧ E.RW = srvRestRWH γB H ∧
      ∃ (d : mvcc.KBReal) (al st lp : Loc), E.γ.kb = some d ∧ d.γB = γB ∧
        H = srvObjsOn al st lp cl d.be

/-- The server `s`'s fields hold `v`, with their contracts; the apply environment `E`'s batch
lock has the protocol's invariant `batchLockInv γ TM` and runs the post-lock hook `v.hook`; its
rest buckets' resource is the backend's tracked buckets and `s.cluster`'s in-memory members
(`srvRestOwn`, D22, 2026-10-23). (D22 receiver epochs, S7a, 2026-10-23: `s.uberApply`, which
`applySnapshot` rebuilds, is no longer here, read-only for good: it is the apply thread's,
`srvApplyKV`.) -/
def srvFieldsAt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      srvWAddr s ↦□ v.w ∗ waitInv v.w ρ E ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗ ⌜srvEnvOk s γ ci E v.cluster⌝ ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk ρ.kv.wl v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ membership.isRaftCluster v.cluster ∗
      srvQuotaAddr s ↦□ v.quota ∗
      srvLgMuAddr s ↦□ v.lgMu ∗ srvMemberIDAddr s ↦□ v.memberID ∗ srvLeadInv s ∗
      cfgElectionTicksAddr (srvCfgAddr s) ↦□ v.electionTicks ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ v.tickMs ∗
      isNotifier v.firstCommit ∗ isAlarmStore v.alarmStore)

instance srvFieldsAt_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) :
    Persistent (srvFieldsAt s γ ci TM E ρ v) := by
  unfold srvFieldsAt; infer_instance

/-- **The server's id generator** (persistent; the vertical slice's unit V2): the apply thread
reads, from a committed entry's claim, the floor its proposer recorded (`idClaim_fact` at the
server's `srvFloorFact`). -/
def srvGenAt (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(∃ g : Loc, srvReqIDGenAddr s ↦□ g ∗ idGen ρ.ids g (srvFloorFact E))

instance srvGenAt_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (srvGenAt (GF := GF) s E ρ) := by
  unfold srvGenAt; infer_instance

/-- The apply thread's view of the server `s` (persistent): `s.consistIndex` (with the
protocol, `isServerCI`), the fields `applyEntryNormal` and `apply` read (the applier's in the
environment `E`), and the atomics (the applied index's at the read names `γr`: unit 4b); the
request path's read names are `γr` (`ρ.rd`, 2026-10-14, unit C2a: the results the apply thread
hands the wait carry a witness at them, `resultIsW`); the server's raft node (`srvRaftNode`, whose
`ApplyConfChange` `applyConfChange` calls; audit phase B3, 2026-10-18). -/
def isServer (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) : IProp GF :=
  iprop(⌜ρ.rd = γr⌝ ∗ isServerCI s γ ci ∗ (∃ v : SrvFields, srvFieldsAt s γ ci TM E ρ v) ∗
    srvAtomics s E γr ∗ srvGenAt s E ρ ∗ srvRaftNode s ρ.raft)

instance isServer_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    Persistent (isServer s γ ci TM E ρ γr) := by
  unfold isServer; infer_instance

/-- The real backend `be` as the server's `s.be` holds it. -/
abbrev srvBeIface (be : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be

/-- **What a reader of `s.be` knows of the backend `d`** (persistent; D22 receiver epochs, S7b,
2026-10-23): its contract at the store's late-bound writer resource and some hooks' resource
(`backend.isBackend`), what the storage-version monitor writes it through. True of every backend
the server ever holds, so it is kept in `s.bemu`'s lock invariant with the field (`bemuP`). -/
def srvBeRO (d : mvcc.KBReal) : IProp GF :=
  iprop(∃ Pk : IProp GF, backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be)

instance srvBeRO_persistent (d : mvcc.KBReal) : Persistent (srvBeRO (GF := GF) d) := by
  unfold srvBeRO; infer_instance

/-- **The apply thread's part of the server's backend** (D22 receiver epochs, S7b, 2026-10-23;
until then `NewServer` kept half of `s.be` read-only for good): half of `s.be` (the other half is
`s.bemu`'s lock invariant's, `bemuP`), at the real backend `d` of the store's names `E.γ`, and a
quarter of the ghost variable `E.γbe` of the current backend (half `bemuP`'s, split among the
readers of `s.bemu`; a quarter the write budget's, `srvWTPool`). `applySnapshot`, the only writer
of `s.be` (`server.go`'s `s.be = newbe`, under `bemu`'s write side), gathers all of both. -/
def srvBeOwn (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d)

/-- **The apply thread's applier state** at `x` (not persistent): the server's `uberApply`, owned
(D22 receiver epochs, S7a, 2026-10-23: the apply thread is its only reader and writer,
`applySnapshot` rebuilds it; until then `↦□` in `srvFieldsAt`), the apply package's uber-applier
in the environment `E` (`apply.applierFor`) and its state (`apply.applyKV`: its current chain
`x.chain`, the KV's resources at the committed log `x.log`), the apply thread's part of `s.be`
(`srvBeOwn`, S7b), and the authority of the revisions' tokens at `x.log` (`revAuth`: the apply
thread mints a revision's token when the log grows to it; the vertical slice's unit V1), and the
apply thread's auth resource (`srvAuthApplyRes`, the auth plan's E2m, 2026-10-26: with auth on,
the admin side's authority with its fuel, its write resource and the provider's admin share,
which an admin request's application takes; `True` with auth off). -/
def srvApplyKV (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) : IProp GF :=
  iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
    apply.applyKV E ua x ∗ srvBeOwn s E ∗ revAuth E x.log ∗ srvAuthApplyRes s E ∗
    ∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗
      waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) ∗ RD)

/-- **What the caller of `applyEntryNormal` knows of the entry's registration** (persistent; the
request path's unit 4d): for an entry whose data decode to a request with an id, `ot`'s
knowledge of the id (`waitRegdOpt`: nothing for `none`, the registration with the consumer token
`t` for `some t`); and (linkv-txn stage B1, 2026-10-20) nothing known only of another prefix's id
than the member's `p` (the member's own requests were registered before they were proposed:
`idRegd`, `entryWaitOk`). -/
def entryRegd (γw : GName) (p : w64) (m : EntryModel) (ot : Option GName) : IProp GF :=
  iprop(□ ∀ (rq : apply.IRRModel) (id : w64),
    ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ →
      waitRegdOpt γw id ot ∗ ⌜ot = none → m.data ≠ [] → idPfx id ≠ p⌝)

instance entryRegd_persistent (γw : GName) (p : w64) (m : EntryModel) (ot : Option GName) :
    Persistent (entryRegd (GF := GF) γw p m ot) := by
  unfold entryRegd; infer_instance

/-- **What the apply thread knows of a committed entry's registration** (linkv-txn stage B1,
2026-10-20): from the entry's claims (`entryWaitOk`: the id registered in its prefix's member's
registry, `idRegd`) and the member's registry (`idWaitIs`, `waitInv`), the registration with its
consumer token for an id of the member's prefix, nothing for another's. -/
theorem entryRegd_of_wait (ρ : ReqNames) (E : apply.AEnv GF) (m : EntryModel)
    (ht : m.typ = W32 0) :
    entryWaitOk (GF := GF) ρ E m ∗ idWaitIs ρ.ids ρ.ids.pfx ρ.wait ⊢
      ∃ ot : Option GName, entryRegd ρ.wait ρ.ids.pfx m ot := by
  iintro ⟨#Hw, #Hn⟩
  unfold entryWaitOk
  simp only [ht, ↓reduceIte]
  icases Hw with ⟨#Hc, -⟩
  have hnone : (∀ rq id, apply.irrDecode m.data = some rq → apply.irrId rq = some id →
      m.data ≠ [] → idPfx id ≠ ρ.ids.pfx) → ⊢ entryRegd (GF := GF) ρ.wait ρ.ids.pfx m none := by
    intro h
    iunfold entryRegd
    iintro !> %rq %id %hrq
    iunfold waitRegdOpt
    isplitr
    · itrivial
    ipureintro; intro _ hd; exact h rq id hrq.1 hrq.2 hd
  by_cases hd : m.data = []
  · iexists none
    iapply hnone (fun _ _ _ _ h => absurd hd h)
  cases hdec : apply.irrDecode m.data with
  | none =>
    iexists none
    iapply hnone (fun _ _ h => by rw [hdec] at h; cases h)
  | some rq =>
    cases hid : apply.irrId rq with
    | none =>
      iexists none
      iapply hnone (fun rq' _ h h' => by
        rw [hdec] at h; cases h; rw [hid] at h'; cases h')
    | some id =>
      ihave ⟨-, #Hreg⟩ := Hc $$ %rq %id %(⟨hd, rfl, hid⟩)
      by_cases hp : idPfx id = ρ.ids.pfx
      · iunfold idRegd at Hreg
        icases Hreg with ⟨%W, %t, #HW, #Hr⟩
        rw [hp]
        ihave %HWe := idWaitIs_agree ρ.ids ρ.ids.pfx W ρ.wait $$ HW Hn
        subst HWe
        iexists some t
        iunfold entryRegd
        iintro !> %rq' %id' %h
        have : rq' = rq := by rw [hdec] at h; exact (Option.some.inj h.1).symm
        subst this
        have : id' = id := by rw [hid] at h; exact (Option.some.inj h.2).symm
        subst this
        iunfold waitRegdOpt
        iframe Hr
        ipureintro; intro h; cases h
      · iexists none
        iapply hnone (fun rq' id' h h' _ => by
          rw [hdec] at h; cases h; rw [hid] at h'; cases h'; exact hp)

/-- The member's registry, from the server's view (linkv-txn stage B1). -/
theorem isServer_waitIs (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServer (GF := GF) s γ ci TM E ρ γr ⊢ idWaitIs ρ.ids ρ.ids.pfx ρ.wait := by
  iintro #H
  iunfold isServer at H
  icases H with ⟨-, -, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAt at Hf
  icases Hf with ⟨-, -, -, #Hwi, -⟩
  iunfold waitInv at Hwi
  icases Hwi with ⟨-, #Hn⟩
  iexact Hn

/-- **The entry's delivery** (persistent; the request path's unit 4d): the entry has no data, or
its outcome was not waived for want of a waiter (`ApplyOut.waived`: applied, its ranges run),
or the registration `ot` knew of is gone (`waitGoneOpt`: a `Trigger` took it out). -/
def entryDelivered (γw : GName) (m : EntryModel) (ot : Option GName) (out : apply.ApplyOut) :
    IProp GF :=
  iprop(⌜m.data = [] ∨ out.waived = false⌝ ∨
    ∃ (rq : apply.IRRModel) (id : w64), ⌜apply.irrDecode m.data = some rq ∧
      apply.irrId rq = some id⌝ ∗ waitGoneOpt γw id ot)

instance entryDelivered_persistent (γw : GName) (m : EntryModel) (ot : Option GName)
    (out : apply.ApplyOut) : Persistent (entryDelivered (GF := GF) γw m ot out) := by
  unfold entryDelivered; infer_instance

/-- `wait.New`'s contract gives the apply package's `waitOk` (the `IsRegistered` triple). -/
theorem isWait_waitOk (w : GoInterface) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) (RD : IProp GF) :
    isWait w γi γw R RD ⊢
      waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) := by
  iintro H
  iunfold isWait at H
  icases H with ⟨%wi, %Hw, -, -, #HI⟩
  iunfold waitOk
  iexists wi
  iframe HI
  ipureintro; exact Hw

/-- The apply thread's chain is in the environment's auth mode (2026-10-14, unit T1). -/
theorem applyKV_authOn (E : apply.AEnv GF) (ua : GoInterface) (x : apply.ApplyKV) :
    apply.applyKV E ua x ⊢ apply.applyKV E ua x ∗ ⌜x.chain.authOn = E.authOn⌝ := by
  iintro H
  ihave %Hc : iprop(⌜x.chain.authOn = E.authOn⌝) $$ [H]
  · iunfold apply.applyKV at H
    icases H with ⟨%p, -, Ho, -⟩
    iunfold apply.uberOwn at Ho
    icases Ho with ⟨%a, -, -, %h⟩
    ipureintro; exact h
  iframe H
  ipureintro; exact Hc

/-- The certificate of the KV's log, from the apply thread's applier state. -/
theorem applyKV_idxCert (E : apply.AEnv GF) (ua : GoInterface) (x : apply.ApplyKV) :
    apply.applyKV E ua x ⊢ apply.applyKV E ua x ∗ mvcc.idxCert E.γ.idx x.log := by
  iintro H
  ihave #Hc : iprop(mvcc.idxCert E.γ.idx x.log) $$ [H]
  · iunfold apply.applyKV at H
    icases H with ⟨%p, -, -, Hk⟩
    iunfold apply.kvOwn at Hk
    icases Hk with ⟨-, Hsw, -⟩
    iunfold txn.kvWriter at Hsw
    icases Hsw with ⟨Hsw, -⟩
    iunfold txn.soleWriter at Hsw
    icases Hsw with ⟨#Hc, -, -⟩
    iexact Hc
  iframe H Hc

/-- The certificate of the KV's log, from the apply thread's applier state at the server. -/
theorem srvApplyKV_idxCert (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV s E γw x ⊢ srvApplyKV s E γw x ∗ mvcc.idxCert E.γ.idx x.log := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, Hua, #Hap, Hkv, Hw⟩
  icases applyKV_idxCert E ua x $$ Hkv with ⟨Hkv, #Hc⟩
  iframe Hc
  iunfold srvApplyKV
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  iexact Hw

/-- The apply thread's `s.uberApply` and its applier, lent (D22 receiver epochs, S7a). -/
theorem srvApplyKV_ua (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV s E γw x ⊢ ∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      (srvUberApplyAddr s ↦ ua -∗ srvApplyKV s E γw x) := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, Hua, #Hap, Hkv⟩
  iexists ua
  iframe Hua Hap
  iintro Hua
  iunfold srvApplyKV
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  iexact Hkv

/-- **The apply thread's KV log is small** (D19c's move, 2026-10-18): the sole writer's log has
a revision per change past its first two and fewer than `2 ^ 48` changes (`txn.soleWriter_small`:
the time receipts), so the size clauses of every request's premise hold at it
(`rqSmall_of_small`). -/
theorem srvApplyKV_small' (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV s E γw x ⊢
      ⌜x.log.length ≤ mvcc.logCh x.log + 2 ∧ mvcc.logCh x.log < 2 ^ 48⌝ := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, -, -, Hkv, -⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, -, -, Hk⟩
  iunfold apply.kvOwn at Hk
  icases Hk with ⟨-, Hsw, -⟩
  iunfold txn.kvWriter at Hsw
  icases Hsw with ⟨Hsw, -⟩
  iapply txn.soleWriter_small' $$ Hsw

/-- `srvApplyKV_small'`, keeping the applier state. -/
theorem srvApplyKV_small (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV s E γw x ⊢
      ⌜x.log.length ≤ mvcc.logCh x.log + 2 ∧ mvcc.logCh x.log < 2 ^ 48⌝ ∗ srvApplyKV s E γw x :=
  persistent_entails_right (srvApplyKV_small' s E γw x)

/-- Two claims of one id agree on the data and the ghost name. -/
theorem idClaim_agree' (γi : IdNames) (id : w64) (d1 d2 : List w8) (γ1 γ2 : GName) :
    ⊢ idClaim (GF := GF) γi id d1 γ1 -∗ idClaim γi id d2 γ2 -∗ ⌜d1 = d2 ∧ γ1 = γ2⌝ := by
  iintro H1 H2
  iunfold idClaim at H1 H2
  icombine H1 H2 gives %Hag
  ipureintro
  have := Option.some.inj Hag.2
  exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩

/-! ### The write budget backed by time receipts (D19b) -/

def srvWTN : Namespace := nroot .@ "srvWT"

-- (S7b) for a later over an existential backend in the budget's invariant
deriving instance Inhabited for backend.DBNames
deriving instance Inhabited for backend.BNames
deriving instance Inhabited for mvcc.KBReal

/-- **The apply thread's write budget** (D19b, 2026-10-18; persistent): an invariant holding,
for the `a` write tokens taken so far, `a` time receipts, and `n` write tokens of the store
left, with `receiptBound GF ≤ a + n + 1`. The apply loop takes one token per entry with the
receipt of a Go step of that entry's iteration (`srvWTPool_take`): `a + 1 < receiptBound GF`, so
a token is left. Until D19b the apply thread was handed `txn.storeWTs` per batch by `run`, under
the lifetime premise `srvLifeBound` (D14g: every committed log has at most `N` entries), a
statement over raft's ghost state, refutable as a hypothesis of a closed theorem (D19a).
(2026-10-19, D21 M3) The count of tokens taken, `a`, is also a monotone counter `γp`, whose lower
bounds (`srvWTAt`) the apply thread keeps at its applied index: one token per applied entry, so
the applied index stays below `receiptBound GF` (`srvWTPool_bound`), the bound D21 M0 puts under
`SnapshotCatchUpEntries`.

**Of the current backend** (D22 receiver epochs, S7b, 2026-10-23; until then the stock was of the
store's names' backend for good, `txn.storeWTs E.γ n`): the tokens are write-back tokens of the
server's current backend `d`, of which the invariant holds a quarter of the ghost variable `E.γbe`
(half is `s.bemu`'s lock invariant's, `bemuP`, a quarter the apply thread's, `srvBeOwn`), so that a
taker agrees on `d` with it: the apply thread through `srvBeOwn`, the storage-version monitor through
its share of `bemuP` under `s.bemu`'s read lock. The invariant also holds the monitor's read token
of `d` (`mvcc.bkRTx`, until S7b the monitor's own for good, `srvSVRes`), or, while the monitor has
it checked out for a session, a part of the monitor's share of `E.γbe` in its place.
`applySnapshot`, holding `bemu`'s write side, gathers all of `E.γbe` from `bemuP`, `srvBeOwn` and
this invariant (so no session is open: a checked-out part would make more than the whole), moves
it to the new backend, takes the old backend's tokens (for its `Close`) and puts in the new one's:
the pool is refilled per backend, one invariant over the current backend. -/
def srvWTPool (E : apply.AEnv GF) (γp : GName) : IProp GF :=
  inv srvWTN iprop(∃ (a n : Nat) (d : mvcc.KBReal), ⧗ a ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ∗ ownToks d.γB.wb n ∗
    monoNatAuthOwn γp 1 a ∗ ⌜receiptBound GF ≤ a + n + 1⌝ ∗
    (mvcc.bkRTx d.γB d.P d.be ∨ ∃ q : Qp, dghostVar E.γbe (DFrac.own q) d))

instance srvWTPool_persistent (E : apply.AEnv GF) (γp : GName) :
    Persistent (srvWTPool (GF := GF) E γp) := by
  unfold srvWTPool; infer_instance

/-- **The write budget's stock before `start` makes it** (D22 receiver epochs, S7b): `N` write
tokens of the store's backend `d`, the budget's quarter of the current backend's ghost variable at
`d` and the storage-version monitor's read token of `d` (`NewServer`'s). -/
def srvWTStock (E : apply.AEnv GF) (N : Nat) : IProp GF :=
  iprop(∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ∗ txn.storeWTs E.γ N ∗
    mvcc.bkRTx d.γB d.P d.be)

/-- (2026-10-19, D21 M3) **At least `v` write tokens taken** (persistent): the apply thread's, at
its applied index. -/
def srvWTAt (γp : GName) (v : w64) : IProp GF := monoNatLbOwn γp (uint.nat v)

instance srvWTAt_persistent (γp : GName) (v : w64) : Persistent (srvWTAt (GF := GF) γp v) := by
  unfold srvWTAt; infer_instance

/-- The budget from its stock (`N` write tokens), under `receiptBound GF ≤ N + 1`, its counter at
`0`. -/
theorem srvWTPool_alloc (E : apply.AEnv GF) (N : Nat) (Ms : CoPset)
    (h : receiptBound GF ≤ N + 1) :
    srvWTStock (GF := GF) E N ⊢ |={Ms}=> ∃ γp, srvWTPool E γp ∗ srvWTAt γp (W64 0) := by
  iintro HW
  iunfold srvWTStock at HW
  icases HW with ⟨%d, %Hd, Hg, Hw, Hrt⟩
  have hw : txn.storeWTs (GF := GF) E.γ N = ownToks d.γB.wb N := by
    unfold txn.storeWTs; rw [Hd]
  ihave Hw : ownToks (GF := GF) d.γB.wb N $$ [Hw]
  · rw [← hw]; iexact Hw
  imod receipt_zero (GF := GF) with H0
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γp, Ha, #Hlb⟩
  iexists γp
  isplitl
  · unfold srvWTPool
    iapply inv_alloc srvWTN Ms
    inext
    iexists 0, N, d
    isplitl [H0]
    · iexact H0
    isplitl [Hg]
    · iexact Hg
    isplitl [Hw]
    · iexact Hw
    isplitl [Ha]
    · iexact Ha
    isplitr
    · ipureintro; omega
    ileft; iexact Hrt
  · unfold srvWTAt; imodintro; rw [show uint.nat (W64 0) = 0 from rfl]; iexact Hlb

/-- One write-back token of the backend `d` off a supply. -/
theorem wbToks_split (d : mvcc.KBReal) (n : Nat) :
    ownToks (GF := GF) d.γB.wb (n + 1) ⊢ backend.wbTok d.γB ∗ ownToks d.γB.wb n := by
  unfold backend.wbTok
  rw [Nat.add_comm]
  exact ownToks_add_1 n 1 d.γB.wb

/-- A write-back token of the store's backend is the store's write token. -/
theorem storeWT_of_wbTok (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hd : γ.kb = some d) :
    backend.wbTok (GF := GF) d.γB ⊢ mvcc.storeWT γ := by
  unfold mvcc.storeWT mvcc.kbWT
  rw [hd]

/-- The apply thread's quarter of `E.γbe`, lent from its part of `s.be` (S7b). -/
theorem srvBeOwn_frag (s : Loc) (E : apply.AEnv GF) :
    srvBeOwn (GF := GF) s E ⊢ ∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗
      dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ∗
      (dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d -∗ srvBeOwn s E) := by
  iintro H
  iunfold srvBeOwn at H
  icases H with ⟨%d, %Hd, Hbe, Hg⟩
  iexists d
  isplitr
  · ipureintro; exact Hd
  iframe Hg
  iintro Hg
  iunfold srvBeOwn
  iexists d
  iframe Hbe Hg
  ipureintro; exact Hd

/-- The apply thread's part of `s.be`, lent from its applier state (S7b). -/
theorem srvApplyKV_beOwn (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV (GF := GF) s E γw x ⊢ srvBeOwn s E ∗ (srvBeOwn s E -∗ srvApplyKV s E γw x) := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, Hua, #Hap, Hkv, Hbo, Hrest⟩
  iframe Hbo
  iintro Hbo
  iunfold srvApplyKV
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  isplitl [Hbo]
  · iexact Hbo
  iexact Hrest

/-- **One write-back token of the current backend `d` for the entry at `v + 1`** (S7b): the
taker's part of `E.γbe` at `d` agrees with the budget's; from the lower bound at `v` to one at
`v + 1`. -/
theorem srvWTPool_take_at_d (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) (dq : DFrac)
    (v : w64) (hv : uint.Z v + 1 < 2 ^ 64) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ srvWTAt γp v -∗ dghostVar E.γbe dq d ={⊤}=∗
      backend.wbTok d.γB ∗ srvWTAt γp (v + W64 1) ∗ dghostVar E.γbe dq d := by
  iintro #Hp Hr #Hv Hg
  unfold srvWTPool
  iinv Hp with ⟨%a, %n, %d', >Ha, >Hg', >Hn, >Hc, >%Hb, Hrt⟩ Hclose
  ihave %Hdd := dghostVar_agree E.γbe d dq d' _ $$ Hg Hg'
  subst Hdd
  unfold srvWTAt
  icases monoNatLbOwn_valid γp 1 a (uint.nat v) $$ Hc Hv with %Hva
  replace Hva := Hva.2
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  icases wbToks_split d n' $$ Hn with ⟨Ht, Hn⟩
  imod mono_nat_own_update (a + 1) (by omega) $$ Hc with ⟨Hc, #Hlb⟩
  imod Hclose $$ [Ha Hg' Hn Hc Hrt] with -
  · inext
    iexists a + 1, n', d
    iframe Ha Hg' Hn Hc Hrt
    ipureintro; omega
  imodintro
  iframe Ht Hg
  iapply monoNatLbOwn_le (uint.nat (v + W64 1)) (by
    have h1 := uint_nat_eq (v + W64 1)
    have h2 := uint_nat_eq v
    have : uint.Z (v + W64 1) = uint.Z v + 1 := by word
    omega) $$ Hlb

/-- (2026-10-19, D21 M3) **One write token for the entry at `v + 1`**: as `srvWTPool_take`, from
the apply thread's lower bound at `v` to one at `v + 1`; (S7b) at the apply thread's backend (its
applier state's part of `s.be`, `srvBeOwn`). -/
theorem srvWTPool_take_at (s : Loc) (E : apply.AEnv GF) (γp γw : GName) (x : apply.ApplyKV)
    (v : w64) (hv : uint.Z v + 1 < 2 ^ 64) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ srvWTAt γp v -∗ srvApplyKV s E γw x ={⊤}=∗
      mvcc.storeWT E.γ ∗ srvWTAt γp (v + W64 1) ∗ srvApplyKV s E γw x := by
  iintro #Hp Hr #Hv HKV
  icases srvApplyKV_beOwn s E γw x $$ HKV with ⟨Hbo, HKV⟩
  icases srvBeOwn_frag s E $$ Hbo with ⟨%d, %Hd, Hg, Hbo⟩
  imod srvWTPool_take_at_d E γp d _ v hv $$ Hp Hr Hv Hg with ⟨Ht, #Hlb, Hg⟩
  ihave Hbo := Hbo $$ Hg
  ihave HKV := HKV $$ Hbo
  imodintro
  iframe HKV Hlb
  iapply storeWT_of_wbTok E.γ d Hd $$ Ht

/-- (D22 S-l sender, 2026-10-22) **A write token for a receipt, for no entry** at the current
backend `d` (S7b): the merged snapshot's two write-backs (`KV().Commit()`'s `ForceCommit`,
`be.Snapshot()`'s own commit) are paid from the pool, a Go step's receipt each, as an entry's is
(`srvWTPool_take_at`); the count of tokens taken grows past the applied index, whose lower bound
(`srvWTAt`) stays one. -/
theorem srvWTPool_take_extra_d (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) (dq : DFrac) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ dghostVar E.γbe dq d ={⊤}=∗
      backend.wbTok d.γB ∗ dghostVar E.γbe dq d := by
  iintro #Hp Hr Hg
  unfold srvWTPool
  iinv Hp with ⟨%a, %n, %d', >Ha, >Hg', >Hn, >Hc, >%Hb, Hrt⟩ Hclose
  ihave %Hdd := dghostVar_agree E.γbe d dq d' _ $$ Hg Hg'
  subst Hdd
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  icases wbToks_split d n' $$ Hn with ⟨Ht, Hn⟩
  imod mono_nat_own_update (a + 1) (by omega) $$ Hc with ⟨Hc, -⟩
  imod Hclose $$ [Ha Hg' Hn Hc Hrt] with -
  · inext
    iexists a + 1, n', d
    iframe Ha Hg' Hn Hc Hrt
    ipureintro; omega
  imodintro
  iframe Ht Hg

/-- `srvWTPool_take_extra_d` at the apply thread's backend (`srvBeOwn`). -/
theorem srvWTPool_take_extra (s : Loc) (E : apply.AEnv GF) (γp : GName) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ srvBeOwn s E ={⊤}=∗ mvcc.storeWT E.γ ∗ srvBeOwn s E := by
  iintro #Hp Hr Hbo
  icases srvBeOwn_frag s E $$ Hbo with ⟨%d, %Hd, Hg, Hbo⟩
  imod srvWTPool_take_extra_d E γp d _ $$ Hp Hr Hg with ⟨Ht, Hg⟩
  ihave Hbo := Hbo $$ Hg
  imodintro
  iframe Hbo
  iapply storeWT_of_wbTok E.γ d Hd $$ Ht

/-- (D22 S-l sender) **The merged snapshot's two write tokens**, for two receipts. -/
theorem srvWTPool_take_two (s : Loc) (E : apply.AEnv GF) (γp : GName) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ ⧗ 1 -∗ srvBeOwn s E ={⊤}=∗
      mvcc.storeWT E.γ ∗ mvcc.storeWT E.γ ∗ srvBeOwn s E := by
  iintro #Hp Hr1 Hr2 Hbo
  imod srvWTPool_take_extra s E γp $$ Hp Hr1 Hbo with ⟨Ht1, Hbo⟩
  imod srvWTPool_take_extra s E γp $$ Hp Hr2 Hbo with ⟨Ht2, Hbo⟩
  imodintro
  iframe Ht1 Ht2 Hbo

/-- (2026-10-19, D21 M3) **The applied index is below the receipts' bound**: at most the tokens
taken, each with its receipt. -/
theorem srvWTPool_bound (E : apply.AEnv GF) (γp : GName) (v : w64) :
    ⊢ srvWTPool (GF := GF) E γp -∗ srvWTAt γp v ={⊤}=∗ ⌜uint.Z v < receiptBound GF⌝ := by
  iintro #Hp #Hv
  unfold srvWTPool
  iinv Hp with ⟨%a, %n, %d, >Ha, >Hg, >Hn, >Hc, >%Hb, Hrt⟩ Hclose
  unfold srvWTAt
  icases monoNatLbOwn_valid γp 1 a (uint.nat v) $$ Hc Hv with %Hva
  replace Hva := Hva.2
  ihave %Hlt := receipt_lt a $$ Ha
  imod Hclose $$ [Ha Hg Hn Hc Hrt] with -
  · inext
    iexists a, n, d
    iframe Ha Hg Hn Hc Hrt
    ipureintro; omega
  imodintro
  ipureintro
  have := uint_nat_eq v
  omega

end defs_lc

end EtcdGrove
end Perennial
