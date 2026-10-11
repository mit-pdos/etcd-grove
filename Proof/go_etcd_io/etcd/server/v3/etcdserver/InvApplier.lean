/-
The etcd server as its apply thread uses it: the shared vocabulary of the specs of
`applyEntryNormal`, `apply`, `applyEntries` and the applier's contract. Lean-first (no Rocq
counterpart); the protocol is `InvApply.lean`, the hook `InvServer.lean`.

**The applier (trust boundary).** `apply.Apply` (the `UberApplier`'s dispatch, through
mvcc, the lessor, auth, ...) and `applyConfChange` (the cluster's membership) write the
backend's batch transaction. What the protocol needs of them is their contract
(`Spec/apply_Apply.lean`, `Spec/EtcdServer__applyConfChange.lean`): an entry's writes happen
in one critical section of the batch lock, which runs the post-lock hook first, or not at
all. `applierFor ua P f` (an axiom: the applier and the backend are not translated) says
that `ua`'s backend's batch lock has invariant `P` and runs `f` right after every
`LockInsideApply`.

**The server** (`isServer s γ ci TM`, persistent): the fields the apply thread reads, their
values and contracts. `uberApply` is replaced by `applySnapshot` (not translated), on the
apply thread; here it is read-only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb

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
    uint.Z m.index = uint.Z f0 + n ∧ (m.typ = W32 0 ∨ m.typ = W32 1)

/-- The apply thread's relation between the protocol's state `st` and the applied index `a`
(`ep.appliedi`): out of flight, and processed through the larger of `ci` and `a`. It holds
when the server starts (the applied index is the snapshot's, at most the stored consistent
index, through which the backend holds everything) and `applyEntries` keeps it. -/
def loopOk (γ : ApplyNames) (st : ApplyState) (a : w64) : Prop :=
  st.pending = false ∧ uint.Z st.p = max (uint.Z (ciEff γ st.k)) (uint.Z a)

/-- The server's atomics' invariant's namespace. -/
abbrev srvN : Namespace := nroot.@"server"

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary.** `ua` (an `UberApplier`) applies entries to a backend whose batch
transaction's lock has invariant `P` and which runs the post-lock hook `f` right after every
`LockInsideApply` (`batchTx.LockInsideApply`; the server registers its hook with
`SetTxPostLockInsideApplyHook`). An axiom: the applier and the backend are not translated. -/
axiom applierFor (ua : GoInterface) (P : IProp GF) (f : val) : IProp GF

/-- **Trust boundary.** `applierFor` is persistent (a fact about the server's components). -/
axiom applierFor_persistent (ua : GoInterface) (P : IProp GF) (f : val) :
    Persistent (applierFor ua P f)

attribute [instance] applierFor_persistent

/-- `w` is a `wait.Wait` whose `Trigger` returns (it hands the result to a waiting
request; nothing of the protocol). -/
def waitOk (w : GoInterface) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜w = GoInterface.ok wi⌝ ∗
    □ (∀ (id : w64) (x : GoInterface),
      {{ True }} (App (App (Val #(methods wi.ty go!"Trigger" wi.v)) (Val #id)) (Val #x))
      {{ RET #(); True }}))

instance waitOk_persistent (w : GoInterface) : Persistent (waitOk (GF := GF) w) := by
  unfold waitOk; infer_instance

/-- `l` is a `lease.Lessor` whose `Promote` returns (in memory: no backend writes). -/
def lessorOk (l : GoInterface) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜l = GoInterface.ok li⌝ ∗
    □ (∀ d : w64,
      {{ True }} (App (Val #(methods li.ty go!"Promote" li.v)) (Val #d)) {{ RET #(); True }}))

instance lessorOk_persistent (l : GoInterface) : Persistent (lessorOk (GF := GF) l) := by
  unfold lessorOk; infer_instance

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

/-- The server `s`'s fields hold `v`, with their contracts; the backend's applier `uberApply`
runs the post-lock hook `v.hook` under a batch lock with the protocol's invariant
`batchLockInv γ TM`. -/
def srvFieldsAt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      srvWAddr s ↦□ v.w ∗ waitOk v.w ∗
      srvUberApplyAddr s ↦□ v.ua ∗ applierFor v.ua (batchLockInv γ TM) v.hook ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ srvQuotaAddr s ↦□ v.quota)

instance srvFieldsAt_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (v : SrvFields) : Persistent (srvFieldsAt s γ ci TM v) := by
  unfold srvFieldsAt; infer_instance

/-- The server's two atomics the apply thread stores (read by other goroutines). -/
def srvAtomics (s : Loc) : IProp GF :=
  iprop(inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v) ∗
    inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) v))

instance srvAtomics_persistent (s : Loc) : Persistent (srvAtomics (GF := GF) s) := by
  unfold srvAtomics; infer_instance

/-- The apply thread's view of the server `s` (persistent): `s.consistIndex` (with the
protocol, `isServerCI`), the fields `applyEntryNormal` and `apply` read, and the atomics. -/
def isServer (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) : IProp GF :=
  iprop(isServerCI s γ ci ∗ (∃ v : SrvFields, srvFieldsAt s γ ci TM v) ∗ srvAtomics s)

instance isServer_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) :
    Persistent (isServer s γ ci TM) := by
  unfold isServer; infer_instance

/-- The entries `ents` are modelled by `ms` (persistent). -/
def entriesAt (ents : List Loc) (ms : List EntryModel) : IProp GF :=
  iprop(⌜ents.length = ms.length⌝ ∗
    □ (∀ (n : Nat) (e : Loc) (m : EntryModel), ⌜ents[n]? = some e⌝ -∗ ⌜ms[n]? = some m⌝ -∗
      entryAt e m))

instance entriesAt_persistent (ents : List Loc) (ms : List EntryModel) :
    Persistent (entriesAt (GF := GF) ents ms) := by
  unfold entriesAt; infer_instance

/-- `ar` is an `*apply.Result` whose `Err` can be read (nil: no result). -/
def resultOk (ar : Loc) : IProp GF :=
  iprop(⌜ar = null⌝ ∨
    ∃ err : GoInterface, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result
      go!"Err" ar ↦□ err)

instance resultOk_persistent (ar : Loc) : Persistent (resultOk (GF := GF) ar) := by
  unfold resultOk; infer_instance

end defs

end EtcdGrove
end Perennial
