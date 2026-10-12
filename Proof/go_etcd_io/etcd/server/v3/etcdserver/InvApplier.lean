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
leaves the KV), under `entriesOk c` (every normal entry `entryOk` at every state a run of the
batch reaches it in).

**The server** (`isServer s γ ci TM E`, persistent): the fields the apply thread reads, their
values and contracts. `uberApply` is replaced by `applySnapshot` (not translated), on the
apply thread; here it is read-only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Wait
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Perennial.Proof.errors
public import Proof.go_etcd_io.etcd.pkg.v3.notify.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Defs

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
abbrev srvLessorAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"lessor" s
abbrev srvFirstCommitAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"firstCommitInTerm" s
abbrev srvAlarmStoreAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"alarmStore" s
abbrev srvClusterAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"cluster" s
abbrev srvCfgAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"Cfg" s
abbrev srvQuotaAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"QuotaBackendBytes" (srvCfgAddr s)
abbrev srvAppliedIndexAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"appliedIndex" s
abbrev srvTermAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"term" s
abbrev srvClusterFieldAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"cluster" s
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
def entriesFrom (f0 : w64) (ms : List EntryModel) : Prop :=
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
    apply.rqOk x.log rq ∧ apply.dispatchOk rq

/-- **What `applyEntryNormal` does to the KV** with the normal entry `m` (`v3`: above `ci`): no
data, nothing (`skipped`); else its decoded request through `apply.Apply` (`applyStep`). -/
def entryStep (m : EntryModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) :
    Prop :=
  if m.data = [] then x' = x ∧ out = .skipped
  else ∃ rq id, apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧
    apply.applyStep rq v3 x x' out

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

/-- **The premise on a batch** from the KV state `x` (consistent index `c`): every normal entry
is `entryOk` at every state a run of the batch's earlier entries (`batchStep`) reaches it in.
Stated over every run, since `applyStep` is a relation (an auth or quota rejection, the alarm
store's answers): the server cannot choose the run. -/
def entriesOk (c : w64) : List EntryModel → apply.ApplyKV → Prop
  | [], _ => True
  | m :: ms, x => (m.typ = W32 0 → entryOk x m) ∧ ∀ x1, batchStep c m x x1 → entriesOk c ms x1

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

theorem entriesOk_drop (c : w64) (ms : List EntryModel) (x : apply.ApplyKV) (j : Nat)
    (m : EntryModel) (h : entriesOk c (ms.drop j) x) (hm : ms[j]? = some m) :
    (m.typ = W32 0 → entryOk x m) ∧
      ∀ x1, batchStep c m x x1 → entriesOk c (ms.drop (j + 1)) x1 := by
  have hj : j < ms.length := by
    rcases Nat.lt_or_ge j ms.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  rw [List.drop_eq_getElem_cons hj] at h
  have hm' : ms[j] = m := by rw [List.getElem?_eq_getElem hj] at hm; exact Option.some.inj hm
  rw [hm'] at h
  exact h

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

/-- The server's atomics' invariant's namespace. -/
abbrev srvN : Namespace := nroot.@"server"

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- The server's wait: `waitInv` (`InvRequest.lean`, the registry's contract, in `srvFieldsAt`);
-- the apply thread's reader of it, `waitOk` (`apply/Wait.lean`, in `srvApplyKV`).

/-- `l` is a `lease.Lessor` whose `Promote` returns (in memory: no backend writes). -/
def lessorOk (l : GoInterface) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜l = GoInterface.ok li⌝ ∗
    □ (∀ d : w64,
      {{ True }} (App (Val #(methods li.ty go!"Promote" li.v)) (Val #d)) {{ RET #(); True }}))

instance lessorOk_persistent (l : GoInterface) : Persistent (lessorOk (GF := GF) l) := by
  unfold lessorOk; infer_instance

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
  ua : GoInterface
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

/-- The server's two atomics the apply thread stores (read by other goroutines). -/
def srvAtomics (s : Loc) : IProp GF :=
  iprop(inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v) ∗
    inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) v))

instance srvAtomics_persistent (s : Loc) : Persistent (srvAtomics (GF := GF) s) := by
  unfold srvAtomics; infer_instance

/-- The entries `ents` are modelled by `ms` (persistent). -/
def entriesAt (ents : List Loc) (ms : List EntryModel) : IProp GF :=
  iprop(⌜ents.length = ms.length⌝ ∗
    □ (∀ (n : Nat) (e : Loc) (m : EntryModel), ⌜ents[n]? = some e⌝ -∗ ⌜ms[n]? = some m⌝ -∗
      entryAt e m))

instance entriesAt_persistent (ents : List Loc) (ms : List EntryModel) :
    Persistent (entriesAt (GF := GF) ents ms) := by
  unfold entriesAt; infer_instance

-- `resultOk ar` (the server's, until the apply package's unit 3): `apply.resultErrOk`
-- (`apply/InvUber.lean`), the same definition, which `apply.Apply`'s spec returns.

end defs

section defs_lc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! At `HeapGS HasLC.hasLC GF` (later credits), as the notifier `s.firstCommitInTerm`'s
predicate is (Perennial's channel specs are), and the apply package's. -/

/-- The server `s`'s fields hold `v`, with their contracts; the backend's applier `uberApply`
is the apply package's uber-applier in the environment `E` (`apply.applierFor`), whose batch
lock has the protocol's invariant `batchLockInv γ TM` and runs the post-lock hook `v.hook`. -/
def srvFieldsAt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      srvWAddr s ↦□ v.w ∗ waitInv v.w ρ E ∗
      srvUberApplyAddr s ↦□ v.ua ∗ apply.applierFor v.ua E ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ srvQuotaAddr s ↦□ v.quota ∗
      srvLgMuAddr s ↦□ v.lgMu ∗ srvMemberIDAddr s ↦□ v.memberID ∗ srvLeadInv s ∗
      cfgElectionTicksAddr (srvCfgAddr s) ↦□ v.electionTicks ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ v.tickMs ∗
      isNotifier v.firstCommit ∗ isAlarmStore v.alarmStore)

instance srvFieldsAt_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) :
    Persistent (srvFieldsAt s γ ci TM E ρ v) := by
  unfold srvFieldsAt; infer_instance

/-- The apply thread's view of the server `s` (persistent): `s.consistIndex` (with the
protocol, `isServerCI`), the fields `applyEntryNormal` and `apply` read (the applier's in the
environment `E`), and the atomics. -/
def isServer (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isServerCI s γ ci ∗ (∃ v : SrvFields, srvFieldsAt s γ ci TM E ρ v) ∗ srvAtomics s)

instance isServer_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) : Persistent (isServer s γ ci TM E ρ) := by
  unfold isServer; infer_instance

/-- **The apply thread's applier state** at `x` (not persistent): the server's `uberApply`'s
(`apply.applyKV`: its current chain `x.chain`, the KV's resources at the committed log
`x.log`). -/
def srvApplyKV (s : Loc) (E : apply.AEnv GF) (x : apply.ApplyKV) : IProp GF :=
  iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦□ ua ∗ apply.applyKV E ua x ∗
    ∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗ waitOk w RD ∗ RD)

/-- `wait.New`'s contract gives the apply package's `waitOk` (the `IsRegistered` triple). -/
theorem isWait_waitOk (w : GoInterface) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) (RD : IProp GF) :
    isWait w γi γw R RD ⊢ waitOk w RD := by
  iintro H
  iunfold isWait at H
  icases H with ⟨%wi, %Hw, -, -, #HI⟩
  iunfold waitOk
  iexists wi
  iframe HI
  ipureintro; exact Hw

/-- The certificate of the KV's log, from the apply thread's applier state. -/
theorem applyKV_idxCert (E : apply.AEnv GF) (ua : GoInterface) (x : apply.ApplyKV) :
    apply.applyKV E ua x ⊢ apply.applyKV E ua x ∗ mvcc.idxCert E.γ.idx x.log := by
  iintro H
  ihave #Hc : iprop(mvcc.idxCert E.γ.idx x.log) $$ [H]
  · iunfold apply.applyKV at H
    icases H with ⟨%p, -, -, Hk⟩
    iunfold apply.kvOwn at Hk
    icases Hk with ⟨-, Hsw, -⟩
    iunfold txn.soleWriter at Hsw
    icases Hsw with ⟨#Hc, -⟩
    iexact Hc
  iframe H Hc

/-- Two claims of one id agree on the data. -/
theorem idClaim_agree' (γi : IdNames) (id : w64) (d1 d2 : List w8) :
    ⊢ idClaim (GF := GF) γi id d1 -∗ idClaim γi id d2 -∗ ⌜d1 = d2⌝ := by
  iintro H1 H2
  iunfold idClaim at H1 H2
  icombine H1 H2 gives %Hag
  ipureintro
  exact Option.some.inj Hag.2

end defs_lc

end EtcdGrove
end Perennial
