/-
The etcd server's request path (`v3_server.go`: a client request proposed through raft, the
proposer waiting for the apply thread's result): the shared vocabulary of the specs of
`EtcdServer.Range`/`Put`/`DeleteRange`/`Txn`, `processInternalRaftRequestOnce`, `doSerialize`,
the wait registry (`pkg/wait`) and the id generator (`pkg/idutil`). Lean-first (no Rocq
counterpart); plan: `notes/decisions.md`, "The request path: raft as a contract, the wait
registry, the checks as the premises' discharge".

**Raft as a contract** (`raftPropose`). Until stage R6 of the raft v3.7 retarget (2026-10-16)
the server's raft was etcd's dependency translated names-only (`EtcdDeps/`), not the verified
fork (118 commits earlier, before the protobuf-go v2 raftpb), and the two translations could not
be imported together; since R6 the server's translation is the verified raft's
(`Code/go_etcd_io/raft/`, raft v3.7 plus the read-index fix; `notes/decisions.md`, "The swap"),
and the contract stays until R7 discharges it from `node.Propose`'s spec. So
`raftNode.Propose` (= `raft.Node.Propose`, promoted) gets, as a contract of the server's `Node`
field, the statement the verified `node.Propose` proves for the register
(`Spec/go_etcd_io/raft/v3/node__Propose.lean`, `InvNode.lean`), restated over the server's own
ghost names (`ServerRaftNames`): a first proposal of `data` (`fresh`, with its fresh token)
deposits the client's atomic update `AU <{∃∃ L, srvCLog γ L}> <{srvCLog γ (L ++ [data]),
COMM Q L}>` (`srvPropAu1`), which raft fires when the data's one occurrence commits; the call
returns `srvDeposited γ data` and, for a fresh proposal, the ticket. The apply side's half of the
contract (`batchCommitted`): the client entries of a batch raft hands the apply thread
(`toApply`) are the committed client log's next entries (`srvCommittedLb`: a lower bound of the
sequence of committed client data, all occurrences), each deposited, each claimed by its id
(`idClaim`): unit 4 states the loops with it. Discharging the contract is retargeting the
verified raft to v3.7 (`notes/STATUS.md`, "Retargeting raft to upstream").

**Unique ids** (`idGen`, `idFresh`, `idClaim`: `pkg/v3/idutil/Defs.lean`, moved there in unit
2): `Next` returns an id nobody holds, which the proposer claims for its request's data. The ids
of other members' requests (other generators, other prefixes) are claimed in the same map: that
the members' prefixes (`uint16(memberID)`) differ is a premise of the raft contract's apply side
(`issues/etcd-request-id-member-prefix.md`).

**The wait registry** (`isWait w γi γw R RD`: `pkg/v3/wait/Defs.lean`, `wait.New`'s contract
since unit 2). The server's registration condition (`reqWaitR`): `Ψ` is `resultΨ E rq` for the
request `rq` the id was claimed for (`idClaim γi id d`, `irrDecode d = some rq`). So the apply
thread, applying an entry whose data `d'` decode to a request with id `id`, learns from
`idClaim` (the entry's, `entryWaitOk`, from the raft contract, and the registration's) that `d' =
d`, and proves `resultΨ E rq` of its result. A conf change's id (`ccIdOf`) is no KV request's
(`entryWaitOk` of a conf-change entry: unit 4 discharges it with typed claims).

**The result a proposer expects** (`resultΨ E rq x`): `x` is the `*apply.Result` of applying
`rq` (with `v3`) at some KV state `y`, to `y'` (`apply.applyStep`, `apply.applyResultIs`), with
mvcc's certificate of the log after (`idxCert`).

**Reads** (`isReadNotify r γr`): `LinearizableReadNotify(ctx)` (the read-index loop of `read.Read`,
proved in unit 4a, `read/Results.lean`, from contracts on the server and raft) returns `nil` only
once the applied index is at least the committed index the caller knew of (`committedAtLeast γr
c` in, `appliedAtLeast γr ci₀` with `c ≤ ci₀` out); its caller holds a reader slot of the read
loop's lock (`readReader`). Since the request path's unit 4b (2026-10-13) the applied index's
lower bounds are `s.appliedIndex`'s (`srvAppliedInv`: the atomic, half of the ghost index's
authority, the applied logs `γr.logs`), the apply thread holding the other half
(`srvAppliedOwn`) and depositing, at each `setAppliedIndex`, the KV log after the entry
(`appliedLogAt`); the committed index's are `s.committedIndex`'s (`srvCommittedInv`; the writer's
half `srvCommittedOwn` is the raft loop's, unit 4c).

**A write's witness** (2026-10-14, unit C2a; `notes/decisions.md`, "A write's witness for later
reads"). The apply thread deposits the log after an entry *before* the entry's result reaches its
proposer (`applied_predeposit`, `srvAppliedPre`: the ghost variable `γr.pend` says the next
index's log is in), and the applied logs are in their indices' order as prefixes (`srvAppliedInv`'s
`appliedMonoMap`, read as `appliedMono`); with the raft loop raising the committed index past a
batch before handing it over (`committedLast`, `batchCommittedIdx`), every result carries
`appliedWit γr log` (`resultIsW`): its log is applied through an index of the committed log, so a
linearizable read at that index reads a log extending it. The read names are the request path's
(`ReqNames.rd`; the apply thread's `isServer` has them its own, `ρ.rd = γr`).

**The auth store's request side** (`isReqAuth st RD`): `AuthInfoFromCtx`/`AuthInfoFromTLS` return
`nil` or an `*AuthInfo` with readable `Username`/`Revision` (`authInfoIs`), and an error;
`AuthInfoFromCtx` with the caller's reader resource `RD` (2026-10-14, unit A2: of the real store
`auth.authRd st R`, `isReqAuth_of_authInv`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WorkloadDefs
public import Spec.google_golang_org.protobuf.proto.MarshalIRR
public import Perennial.Std.Word.LittleEndian
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.Token
public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.FUpd
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
/-! ## Raft's committed log, at the server: `SrvRaftLog.lean` (2026-10-27, branch `server-port`:
over raft's node API; until then here, over raft's protocol) -/


/-! ## The KV ghost state (2026-10-14, unit T1; 2026-10-15, unit T2: the whole state)

`notes/decisions.md`, "Every KV operation as a persistent atomic update on the whole state". The
abstract state of etcd's KV is one exclusive predicate `etcdKV γk σ` (`σ : KVState`, the store at
its latest revision: every key-value and the current revision), half of a ghost variable whose
other half is in the KV invariant (`kvInv`) with the server's half of raft's committed log `L`,
`σ` being the state of the KV model of `L` (`kvModelSt γk L`). A client keeps `etcdKV`
in its own invariant (a per-key view, if it wants one, is its ghost map beside it). The invariant
also keeps `L` plain at the workload (`plainLog`, D19q): the only updates raft can fire
over `L` are the ones built from it (`kv_prop_au`, `kv_noop_au`), which check. -/

section kvGhost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The KV ghost state's names and the start state the model is folded from: the state's ghost
variable (`st`, halves: `etcdKV`'s and the KV invariant's), the consistent index `c0`, the chain
`ch0` and the log `log0` of the state the server started at; and the KV logs' certificates
(`cok`: mvcc's `certOk` map, `kvCertInv`) with the longest certified log's length (`hi`, a ghost
variable whose halves the certificates' invariant and the apply thread hold). 2026-10-15 (unit
T2): `st` replaces T1's points-to map and the non-plain credit's token. 2026-10-18 (D19c): the
request ids' names `ids` (the generator's: `ReqNames.ids` is this), under which the KV invariant
keeps every committed request's id claimed. (D19q's workload `wl`, a parameter fixed with the
names, is gone since D45: the invariant keeps the log plain, `plainLog`, the kinds the verified
proposers send.) -/
structure KVNames where
  st : GName
  c0 : w64
  ch0 : apply.Chain
  log0 : mvcc.Log
  cok : GName
  hi : GName
  ids : IdNames

/-- The KV invariant's namespace (disjoint from raft's commit). -/
def kvN : Namespace := nroot .@ "server_kv"

theorem kvN_raftN : (↑kvN : CoPset) ⊆ ⊤ \ ↑srvRaftN :=
  mask_ndot_ne' nroot "server_kv" "raft_commit" (by decide)

/-- States are countable (for the state's ghost variable; the key-values' instance is
`etcdKvCountableW`, `InvWatchStore`). -/
instance KVState.countable : Pos.Countable KVState :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.compacted, σ.base, σ.changes, σ.leases))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- **etcd's KV is at the state `σ`** (2026-10-15, unit T2), exclusively: half of the state's
ghost variable (the KV invariant holds the other). -/
def etcdKV (γk : KVNames) (σ : KVState) : IProp GF := ghostVar γk.st (1 : Qp).half σ

instance etcdKV_timeless (γk : KVNames) (σ : KVState) : Timeless (etcdKV (GF := GF) γk σ) := by
  unfold etcdKV; infer_instance

/-- **The KV model of the committed log `L`** (the fold of `kvEntry` from the start state). -/
def kvModel (γk : KVNames) (L : List EntryModel) : mvcc.Log := kvRaftOf γk.c0 γk.ch0 γk.log0 L

/-- **The lease table of the committed log `L`** (unit T3, L3a: the fold of `kvTable` from the
empty table). -/
def kvLeases (γk : KVNames) (L : List EntryModel) : LeaseTable := kvTableOf γk.c0 γk.ch0 [] L

/-- **The KV state of the committed log `L`** (unit T3, L3a): its model's log's state, with its
lease table. -/
def kvModelSt (γk : KVNames) (L : List EntryModel) : KVState := kvStateOf (kvModel γk L) (kvLeases γk L)

/-- **`id` was registered** (persistent; linkv-txn stage B1, 2026-10-20) in the wait registry of
the member of its prefix (the cluster's registries' map, `idWaitIs`), with the consumer token `t`:
what a proposal's entry carries, its proposer having registered the id before proposing. -/
def idRegd (γi : IdNames) (id : w64) : IProp GF :=
  iprop(∃ W t : GName, idWaitIs γi (idPfx id) W ∗ waitRegd W id t)

instance idRegd_persistent (γi : IdNames) (id : w64) : Persistent (idRegd (GF := GF) γi id) := by
  unfold idRegd; infer_instance

instance idRegd_timeless (γi : IdNames) (id : w64) : Timeless (idRegd (GF := GF) γi id) := by
  unfold idRegd idWaitIs waitRegd; infer_instance

/-- **A committed entry's id claimed** (persistent; D19c): a normal entry whose data decode to a
request with an id was claimed for its data under that id (`idClaim`, the generator's names
`γi`), and (linkv-txn stage B1, 2026-10-20) the id registered before the entry was proposed
(`idRegd`). -/
def entryClaim (γi : IdNames) (m : EntryModel) : IProp GF :=
  iprop(⌜m.typ ≠ W32 0 ∨ m.data = []⌝ ∨
    ∃ (rq : apply.IRRModel) (id : w64) (γf : GName),
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ ∗ idClaim γi id m.data γf ∗
      idRegd γi id)

instance entryClaim_persistent (γi : IdNames) (m : EntryModel) :
    Persistent (entryClaim (GF := GF) γi m) := by
  unfold entryClaim; infer_instance

instance entryClaim_timeless (γi : IdNames) (m : EntryModel) :
    Timeless (entryClaim (GF := GF) γi m) := by
  unfold entryClaim idClaim; infer_instance

/-- Every conf change of `L` is one the server's `applyConfChange` takes (`ccPolOk`, at raft's
configuration `cfg`; audit phase B3, 2026-10-18). -/
def ccLogOk (γ : SrvRaft) (L : List EntryModel) : Prop :=
  ∀ m ∈ L, m.typ ≠ W32 0 → ccPolOk γ m.data

/-- **The workload facts of the committed log `L`** (persistent; D19c): every entry of a good
shape (`logShape`: a request's premise at every log but for its size clauses; a conf change's id
`0`), every conf change one `applyConfChange` takes at raft's configuration `cfg` (`ccLogOk`,
audit phase B3), and every id claimed. -/
def kvWork (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) : IProp GF :=
  iprop(⌜logShape L ∧ ccLogOk cfg L⌝ ∗ [∗list] m ∈ L, entryClaim γk.ids m)

instance kvWork_persistent (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) :
    Persistent (kvWork (GF := GF) cfg γk L) := by
  unfold kvWork; infer_instance

instance kvWork_timeless (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) :
    Timeless (kvWork (GF := GF) cfg γk L) := by
  unfold kvWork; infer_instance

/-- **The KV invariant** (see the section header): the server's half of its log `L` of requested entries
(after `ai0`, consecutive, plain, every entry above the start's consistent index) and the other
half of the state's ghost variable at the state of `L`'s model; the start's chain the base chain
with auth disabled and no alarm, the start log not empty; and (D19c, 2026-10-18) the workload
facts of `L` (`kvWork`), which every update the server hands raft checks of its entry. (2026-10-27:
`L` the requested entries only, `srvRLog`; the start's consistent index at most the start index, so
that every entry of a log after the start is above it, `kvModel_eqv`.) -/
def kvInv (γ : ServerRaftNames) (γk : KVNames) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗ ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
    ⌜plainLog L ∧ srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ []⌝ ∗ kvWork γ.raft γk L)

instance kvInv_persistent (γ : ServerRaftNames) (γk : KVNames) :
    Persistent (kvInv (GF := GF) γ γk) := by
  unfold kvInv; infer_instance

/-- **A client's persistent atomic update of the KV by `f`** (2026-10-15, unit T2): `□ Q` of the
state it linearized at. Persistent: a write's may be applied more than once (the client's retry
interceptor, raft's duplicates), a read's is fired at every committed log from its deposit. -/
def kvAu (γk : KVNames) (f : KVState → KVState) (Q : KVState → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γk (f σ), COMM □ Q σ }>)

instance kvAu_persistent (γk : KVNames) (f : KVState → KVState) (Q : KVState → IProp GF) :
    Persistent (kvAu (GF := GF) γk f Q) := by
  unfold kvAu; infer_instance

/-- **A client's update for the operation `op`**: its step (`kvOpStep`; a rejected request's the
identity). (D23's premise of the workload, `γk.wl.writes`, is gone since D44.) -/
def kvOpAu (γk : KVNames) (op : KVOp) (Q : KVState → IProp GF) : IProp GF :=
  kvAu γk (kvOpStep op) Q

instance kvOpAu_persistent (γk : KVNames) (op : KVOp) (Q : KVState → IProp GF) :
    Persistent (kvOpAu (GF := GF) γk op Q) := by
  unfold kvOpAu; infer_instance

/-- **A client's update of the KV by `f`, fired at most once** (2026-10-19, D21 M6, D20 (b)): an
ordinary atomic update, its result `Q` of the state it linearized at not persistent. The server
proposes the request once and raft appends and commits it at most once (`srvPropAu1`), so the
update fires at most once. -/
def kvAu1 (γk : KVNames) (f : KVState → KVState) (Q : KVState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γk (f σ), COMM Q σ }>)

/-- **A client's update for the operation `op`, fired at most once** (D21 M6). -/
def kvOpAu1 (γk : KVNames) (op : KVOp) (Q : KVState → IProp GF) : IProp GF :=
  kvAu1 γk (kvOpStep op) Q

open Iris.ProofMode in
/-- A persistent update fires once, its result persistent. -/
theorem kvOpAu_one (γk : KVNames) (op : KVOp) (Q : KVState → IProp GF) :
    kvOpAu (GF := GF) γk op Q ⊢ kvOpAu1 γk op (fun σ => iprop(□ Q σ)) := by
  unfold kvOpAu kvAu kvOpAu1 kvAu1
  exact intuitionistically_elim

/-- The results' namespace (D21 M6): where an update fired at most once leaves its result. -/
def kvResN : Namespace := nroot .@ "server_kv_res"

/-- **The token of a result** (exclusive; D21 M6): whoever holds it takes the result. -/
def kvResTok (γc : GName) : IProp GF := dghostVar γc (DFrac.own 1) ()

/-- **A result, left where the update fired** (persistent; D21 M6): `Q σ`, until the token's
holder takes it. -/
def kvRes (γc : GName) (Q : KVState → IProp GF) (σ : KVState) : IProp GF :=
  inv kvResN iprop(Q σ ∨ kvResTok γc)

instance kvRes_persistent (γc : GName) (Q : KVState → IProp GF) (σ : KVState) :
    Persistent (kvRes (GF := GF) γc Q σ) := by
  unfold kvRes; infer_instance

theorem kvResTok_alloc : ⊢ |==> ∃ γc, kvResTok (GF := GF) γc := by
  unfold kvResTok; exact dghostVar_alloc ()

/-- Leaving a result (D21 M6). -/
theorem kvRes_alloc (γc : GName) (Q : KVState → IProp GF) (σ : KVState) (E : CoPset) :
    ⊢ Q σ ={E}=∗ kvRes (GF := GF) γc Q σ := by
  iintro HQ
  unfold kvRes
  iapply inv_alloc
  inext; ileft; iexact HQ

/-- Taking a result with its token (D21 M6). -/
theorem kvRes_take (γc : GName) (Q : KVState → IProp GF) (σ : KVState) (E : CoPset)
    (hE : ↑kvResN ⊆ E) :
    ⊢ kvRes (GF := GF) γc Q σ -∗ kvResTok γc -∗ £ 1 ={E}=∗ Q σ := by
  iintro #Hres Htok Hlc
  unfold kvRes
  iinv Hres with H Hclose
  imod lc_fupd_elim_later $$ Hlc H with H
  icases H with (HQ | Htok')
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    imodintro; iexact HQ
  · unfold kvResTok
    ihave %Hv := dghostVar_valid_2 _ _ _ _ _ $$ Htok Htok'
    exfalso
    have h := DFrac.valid_own_op Hv.1
    exact absurd h (by decide)

/-- **A client's read update**: the state unchanged. -/
def kvReadAu (γk : KVNames) (Q : KVState → IProp GF) : IProp GF :=
  kvAu γk (fun σ => σ) Q

instance kvReadAu_persistent (γk : KVNames) (Q : KVState → IProp GF) :
    Persistent (kvReadAu (GF := GF) γk Q) := by
  unfold kvReadAu; infer_instance

/-! ### The KV logs' certificates (mvcc's `certOk`)

The store certifies every log it commits by its caller's ghost map `γ.cok` (`mvcc.certOk`); the
server's elements say a log is the KV model of a committed raft log, which is what a reader of
the store learns of the log it read (`kv_cert_read`). The apply thread mints the certificate of
the log after an entry before applying it (`kv_cert_step`), at a length above every certified
one (`hi`). -/

/-- The certificates' invariant's namespace. -/
def kvcN : Namespace := nroot .@ "server_kv_cert"

/-- The certificates' map `C` (length ↦ log), below `hi`, each the KV model of a prefix of the
committed raft log `Lb`. -/
def certMapOk (γk : KVNames) (C : GMap w64 mvcc.Log) (hi : Nat) (Lb : List EntryModel) : Prop :=
  ∀ n l, C.lookup n = some l → l.length ≤ hi ∧ n = W64 (l.length : Int) ∧ l.length < 2 ^ 63 ∧
    ∃ A, A <+: Lb ∧ kvModel γk A = l

/-- **The certificates' invariant**: the map's authority, half of `hi`, a committed raft log
bounding the certified logs' raft logs; the start log of at least `NewStore`'s two revisions
(so no certificate is the store's free one, `0 ↦ []`, and every model log has two). -/
def kvCertInv (γ : ServerRaftNames) (γk : KVNames) : IProp GF :=
  inv kvcN iprop(∃ (C : GMap w64 mvcc.Log) (hi : Nat) (Lb : List EntryModel),
    ghostMapAuth γk.cok 1 C ∗ ghostVar γk.hi (1 : Qp).half hi ∗ srvRLogLb γ Lb ∗
    ⌜certMapOk γk C hi Lb ∧ 2 ≤ γk.log0.length⌝)

instance kvCertInv_persistent (γ : ServerRaftNames) (γk : KVNames) :
    Persistent (kvCertInv (GF := GF) γ γk) := by
  unfold kvCertInv; infer_instance

/-- **A KV log's certificate** (persistent): `NewStore`'s (at most two revisions) or an element
of the map. -/
def kvCert (γk : KVNames) (l : mvcc.Log) : IProp GF :=
  iprop(⌜l.length ≤ 2⌝ ∨ (W64 (l.length : Int)) ↪[γk.cok]□ l)

instance kvCert_persistent (γk : KVNames) (l : mvcc.Log) : Persistent (kvCert (GF := GF) γk l) := by
  unfold kvCert; infer_instance

/-- **The apply thread's KV ghost state** at the applied raft log `A` and the KV log `l`: `A`
committed, `l` its model, certified, the longest certified length. -/
def kvAppliedL (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) (l : mvcc.Log) :
    IProp GF :=
  iprop(srvRLogLb γ A ∗ ghostVar γk.hi (1 : Qp).half l.length ∗ kvCert γk l ∗
    ⌜l = kvModel γk A⌝)

/-- `kvAppliedL` of the apply thread's state `x`, at the start's chain (the plain log does not
change it). -/
def kvApplied (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) (x : apply.ApplyKV) :
    IProp GF :=
  iprop(kvAppliedL γ γk A x.log ∗ ⌜x.chain = γk.ch0⌝)

/-- **What a put of `op` needs** (2026-10-14, unit T1; 2026-10-15, unit T2: any flags but a
lease): the lease `0`, and its client's update; since 2026-10-19 (D21 M6) fired at most once. -/
def putPermit (γk : KVNames) (op : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜op.leaseID = W64 0⌝ ∗ kvOpAu1 γk (.put op) Q)

/-- **What a delete of `op` needs** (2026-10-15, unit T2): its range end not `[0]` (the wire
keeps it: `irrWireOf`), and its client's update, fired at most once (`kvOpAu1`, as a put's
since D21 M6; 2026-10-20, linkv-txn stage A). -/
def deletePermit (γk : KVNames) (op : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜op.base.rangeEnd ≠ [W8 0]⌝ ∗ kvOpAu1 γk (.deleteRange op) Q)

/-- No range end of a transaction's comparisons and operations is `[0]` (`irrNoZeroEnd` of its
request: the wire keeps it). -/
def txnNoZeroEnd (t : TxnModel) : Prop :=
  (∀ c ∈ t.cmps, c.rangeEnd ≠ [W8 0]) ∧ txnOpsNoZeroEnd t.thenOps ∧ txnOpsNoZeroEnd t.elseOps

/-- **What a writing transaction `t` needs** (2026-10-15, unit T2): plain (`txn.txnPlain`: its
gets at revision `0`, its puts with no lease and no `IgnoreLease`), no range end `[0]`, and its
client's update; since D19c (2026-10-18) its shape (`txn.txnShape`: the apply's premise but for
its size clauses, which the gRPC layer's checks give, `v3rpc.txnShape_of_check`). Since
2026-10-20 (linkv-txn stage A) the update is fired at most once (`kvOpAu1`, as a put's). -/
def txnPermit (γk : KVNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnPlain t ∧ txnNoZeroEnd t ∧ txn.txnShape t⌝ ∗ kvOpAu1 γk (.txn t) Q)

/-- **What a proposal of `rq` needs** (2026-10-14, unit T1; 2026-10-15, unit T2: every plain
write), with the result `Qr` its update gives: a plain request with no KV write (no put, no
delete, no transaction: `Qr` trivial); or a plain request of the KV operation `op` (`reqKVOp`),
no range end of it `[0]` (so the wire keeps it, `irrWireOf`), with its client's update (`Qr L`
the client's `□ Q` at the state of `L`'s model). Since D19c (2026-10-18) either of a good shape
(`rqShape`: the apply's premise at every log but for its size clauses) and, the first, with no
range end `[0]` either. Since D19q (2026-10-18) plain (`plainReq`). -/
def reqPropOk (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    IProp GF :=
  iprop((⌜plainReq rq ∧ ¬ writeKind (apply.dispatchKind rq) ∧ irrNoZeroEnd rq ∧ rqShape rq ∧
      Qr = fun _ => iprop(True)⌝) ∨
    (∃ (op : KVOp) (Q : KVState → IProp GF), ⌜plainReq rq ∧ reqKVOp rq = some op ∧
        irrNoZeroEnd rq ∧ rqShape rq ∧ Qr = fun L => iprop(□ Q (kvStateOf (kvModel γk L)))⌝ ∗
      kvOpAu γk op Q) ∨
    -- (2026-10-19, D21 M6) its client's update fired at most once, the result left at the
    -- token `γc` (`kvRes`)
    (∃ (op : KVOp) (Q : KVState → IProp GF) (γc : GName), ⌜plainReq rq ∧
        reqKVOp rq = some op ∧ irrNoZeroEnd rq ∧ rqShape rq ∧
        Qr = fun L => kvRes γc Q (kvStateOf (kvModel γk L))⌝ ∗
      kvOpAu1 γk op Q))

/-! ### Reads: a client's deposit and the results of a list of clients -/

/-- **The KV state of the committed log `L` in the auth mode `off`** (its model's, as the KV
invariant's ghost state on plain logs, `kvModelSt_plain`): the read side's default (E3r). -/
@[reducible] def kvStOff (γk : KVNames) (L : List EntryModel) : KVState := kvStateOf (kvModel γk L)

/-- **A client's read deposit** for the result predicate `Q` over committed logs: a read update
with result `Q0`, `Q` being `□ Q0` of the state of the log's model (2026-10-15, unit T2: the whole
state, T1's was a key's value); or no update at all (`Q` trivial: a read with no client update,
the read-only `Txn`'s). The state of a log is `F`'s (the auth plan's E3r, 2026-10-27: the read side
is generic in it), by default the auth mode `off`'s model's (`kvStOff`; with auth on, the mode-`on`
model's, `kvStOn`). -/
def kvDep (γk : KVNames) (Q : List EntryModel → IProp GF)
    (F : List EntryModel → KVState := kvStOff γk) : IProp GF :=
  iprop((∃ Q0 : KVState → IProp GF,
    ⌜Q = fun L => iprop(□ Q0 (F L))⌝ ∗ kvReadAu γk Q0) ∨
    ⌜Q = fun _ => iprop(True)⌝)

instance kvDep_persistent (γk : KVNames) (Q : List EntryModel → IProp GF)
    (F : List EntryModel → KVState) : Persistent (kvDep (GF := GF) γk Q F) := by
  unfold kvDep; infer_instance

/-- A registered client: its result predicate (a saved predicate at `g`) and its deposit. -/
def regOk (γk : KVNames) (g : GName) (F : List EntryModel → KVState := kvStOff γk) : IProp GF :=
  iprop(∃ Q : List EntryModel → IProp GF, savedPredOwn g DFrac.discard Q ∗ kvDep γk Q F)

instance regOk_persistent (γk : KVNames) (g : GName) (F : List EntryModel → KVState) :
    Persistent (regOk (GF := GF) γk g F) := by
  unfold regOk; infer_instance

/-- **The results of the clients `gs` at the log `L`**: each client's `□ Q L`. -/
def readQs (gs : List GName) (L : List EntryModel) : IProp GF :=
  iprop([∗list] g ∈ gs, ∃ Q : List EntryModel → IProp GF, savedPredOwn g DFrac.discard Q ∗ □ Q L)

instance readQs_persistent (gs : List GName) (L : List EntryModel) :
    Persistent (readQs (GF := GF) gs L) := by
  unfold readQs; infer_instance

end kvGhost

/-! ## Reads (`read.Read`, names-only until unit 4) -/

section readGhost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Raft's `ReadState` (v3.7) is countable (a channel's element type: the raft wrapper's
`readStateC`, the read loop's `ReadState()`; moved here from `InvRaftNode.lean`, 2026-10-13, for
the read package, which must not import the raft wrapper's invariants). -/
instance readState_countable : Pos.Countable go_etcd_io.raft.v3.ReadState :=
  countableOfLeftInverse (fun r : go_etcd_io.raft.v3.ReadState => (r.Index', r.RequestCtx'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

/-- **A notifier's ghost names** (2026-10-14, unit T1): its need (a mono nat: the largest
committed bound a client of the notifier required) and its clients' list (a mono list of the
saved predicates of their results). -/
structure NeedNames where
  need : GName
  list : GName

instance needNames_countable : Pos.Countable NeedNames :=
  countableOfLeftInverse (fun x : NeedNames => (x.need, x.list)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

/-- The read-index ghost names: lower bounds of the applied index and of the committed
index; and (2026-10-13, the request path's unit 4a) the read loop's current notifier, a ghost
variable of the notifier and the name of its need (`read/Inv.lean`), whose halves the read loop's
`RWMutex` and its invariant hold: the lock's resource (`readMuP`) names it, so a caller's reader
slot of the lock (`readReader`) is a predicate of the names; and (2026-10-13, unit 4b) the applied
logs, a ghost map from an applied index to the KV log the apply thread had right after applying
the entry at that index (`appliedLogAt`); and (2026-10-14, unit C2a) whether the log of the next
index is already deposited (`pend`, a ghost variable whose halves the applied index's invariant and
the apply thread hold: the apply thread deposits the log after an entry before `setAppliedIndex`,
so that the proposer the entry answers learns it, `srvAppliedPre`). -/
structure ReadNames where
  applied : GName
  committed : GName
  notifier : GName
  logs : GName
  pend : GName
  /-- the raft contract's names (2026-10-14, unit T1: a read's update is over raft's committed
  log; the request path's `ReqNames.raft` is this) -/
  raft : ServerRaftNames
  /-- the KV ghost state (2026-10-14, unit T1; `ReqNames.kv` is this) -/
  kv : KVNames

/-- **The KV log `L` applied through the index `i` is the KV model of a committed raft log**
(persistent; 2026-10-14, unit T1): the raft log `A` through `i`. -/
def kvLogAt (γr : ReadNames) (i : w64) (L : mvcc.Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
    ⌜uint.Z i = uint.Z γr.raft.ai0 + A.length ∧ L = kvModel γr.kv A⌝)

instance kvLogAt_persistent (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    Persistent (kvLogAt (GF := GF) γr i L) := by
  unfold kvLogAt; infer_instance

/-- **The applied logs are KV models of committed raft logs** (2026-10-14, unit T1): a committed
raft log `Lb` bounding, for every key `k` of the applied logs `M`, the raft log through `k`
whose model is `k`'s log. -/
def kvLogsOk (γr : ReadNames) (M : GMap w64 mvcc.Log) : IProp GF :=
  iprop(∃ Lb : List EntryModel, srvRLogLb γr.raft Lb ∗
    ⌜∀ k L, M.lookup k = some L → ∃ A, A <+: Lb ∧
      uint.Z k = uint.Z γr.raft.ai0 + A.length ∧ L = kvModel γr.kv A⌝)

instance kvLogsOk_persistent (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    Persistent (kvLogsOk (GF := GF) γr M) := by
  unfold kvLogsOk; infer_instance

instance kvLogsOk_timeless (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    Timeless (kvLogsOk (GF := GF) γr M) := by
  unfold kvLogsOk; infer_instance

open Iris.ProofMode in
theorem kvLogsOk_insert (γr : ReadNames) (M : GMap w64 mvcc.Log) (v : w64) (L : mvcc.Log) :
    kvLogsOk (GF := GF) γr M ∗ kvLogAt γr v L ⊢ kvLogsOk γr (M.insert v L) := by
  unfold kvLogAt
  iunfold kvLogsOk
  iintro ⟨⟨%Lb, #Hlb, %Hm⟩, ⟨%A, #HA, %Ha⟩⟩
  ihave %Hc := srvRLogLb_prefix γr.raft A Lb $$ [HA Hlb]
  · iframe HA Hlb
  rcases Hc with h | h
  · iexists Lb
    iframe Hlb
    ipureintro
    intro k L' hk
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact ⟨A, h, Ha.1, Ha.2⟩
    · exact Hm k L' hk
  · iexists A
    iframe HA
    ipureintro
    intro k L' hk
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact ⟨A, List.prefix_refl _, Ha.1, Ha.2⟩
    · obtain ⟨A', h1, h2, h3⟩ := Hm k L' hk
      exact ⟨A', h1.trans h, h2, h3⟩

/-- **A batch `ms` committed after the raft log `A` through the applied index `ai`**
(persistent; 2026-10-14, unit T1), whose entries are above the consistent index `c` iff above the
KV model's (`γr.kv.c0`): what the apply thread's steps need to follow the model. -/
def kvBatch (γr : ReadNames) (c ai : w64) (A ms : List EntryModel) : IProp GF :=
  iprop(srvRLogLb γr.raft (A ++ ms) ∗ ⌜uint.Z ai = uint.Z γr.raft.ai0 + A.length ∧
    ∀ m ∈ ms, (uint.Z c < uint.Z m.index ↔ uint.Z γr.kv.c0 < uint.Z m.index)⌝)

instance kvBatch_persistent (γr : ReadNames) (c ai : w64) (A ms : List EntryModel) :
    Persistent (kvBatch (GF := GF) γr c ai A ms) := by
  unfold kvBatch; infer_instance

/-- The applied index is at least `i` (persistent). -/
def appliedAtLeast (γr : ReadNames) (i : w64) : IProp GF := monoNatLbOwn γr.applied (uint.nat i)

/-- The cluster's committed index is at least `i` (persistent: what a caller knew). -/
def committedAtLeast (γr : ReadNames) (i : w64) : IProp GF :=
  monoNatLbOwn γr.committed (uint.nat i)

instance appliedAtLeast_persistent (γr : ReadNames) (i : w64) :
    Persistent (appliedAtLeast (GF := GF) γr i) := by
  unfold appliedAtLeast; infer_instance
instance committedAtLeast_persistent (γr : ReadNames) (i : w64) :
    Persistent (committedAtLeast (GF := GF) γr i) := by
  unfold committedAtLeast; infer_instance

/-- **The log applied through the index `i`** (persistent, agreeing: `appliedLogAt_agree`): the KV
log the apply thread had right after applying the entry at index `i` (deposited by
`setAppliedIndex`, the request path's unit 4b). -/
def appliedLogAt (γr : ReadNames) (i : w64) (L : mvcc.Log) : IProp GF := i ↪[γr.logs]□ L

instance appliedLogAt_persistent (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    Persistent (appliedLogAt (GF := GF) γr i L) := by
  unfold appliedLogAt; infer_instance

instance appliedLogAt_timeless (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    Timeless (appliedLogAt (GF := GF) γr i L) := by
  unfold appliedLogAt; infer_instance

/-- mvcc's certificate is timeless (ghost lower bounds and a pure fact). -/
instance idxCert_timeless_req (γ : mvcc.IdxNames) (log : mvcc.Log) :
    Timeless (mvcc.idxCert (GF := GF) γ log) := by
  unfold mvcc.idxCert; infer_instance

/-- mvcc's seal is timeless (a ghost lower bound and a pure fact; unit W-M2b). -/
instance idxSealed_timeless_req (γ : mvcc.IdxNames) (log : mvcc.Log) :
    Timeless (mvcc.idxSealed (GF := GF) γ log) := by
  unfold mvcc.idxSealed; infer_instance

/-- Two logs applied through one index are one. -/
theorem appliedLogAt_agree (γr : ReadNames) (i : w64) (L L' : mvcc.Log) :
    ⊢ appliedLogAt (GF := GF) γr i L -∗ appliedLogAt γr i L' -∗ ⌜L = L'⌝ := by
  iintro H1 H2
  iunfold appliedLogAt at H1 H2
  icombine H1 H2 gives %Hag
  ipureintro
  exact Hag.2

/-- A lower bound of the committed index is one of every smaller index. -/
theorem committedAtLeast_le (γr : ReadNames) (i j : w64) (h : uint.Z j ≤ uint.Z i) :
    ⊢ committedAtLeast (GF := GF) γr i -∗ committedAtLeast γr j := by
  iintro H
  iunfold committedAtLeast at H
  iunfold committedAtLeast
  iapply monoNatLbOwn_le (uint.nat j) (by word) $$ H

/-- **A batch's last entry is committed** (persistent; 2026-10-14, unit C2a): the committed index
has reached the batch's last index (the raft loop's `updateCommittedIndex` before it hands the
batch to the apply thread); nothing for an empty batch. -/
def committedLast (γr : ReadNames) (ce : List EntryModel) : IProp GF :=
  match ce.getLast? with
  | some m => committedAtLeast γr m.index
  | none => iprop(True)

instance committedLast_persistent (γr : ReadNames) (ce : List EntryModel) :
    Persistent (committedLast (GF := GF) γr ce) := by
  unfold committedLast; split <;> infer_instance

/-- **Every entry of a batch is committed** (persistent; 2026-10-14, unit C2a): the committed
index has reached each entry's index. -/
def batchCommittedIdx (γr : ReadNames) (ms : List EntryModel) : IProp GF :=
  iprop(□ ∀ m, ⌜m ∈ ms⌝ -∗ committedAtLeast γr m.index)

instance batchCommittedIdx_persistent (γr : ReadNames) (ms : List EntryModel) :
    Persistent (batchCommittedIdx (GF := GF) γr ms) := by
  unfold batchCommittedIdx; infer_instance

/-- **The applied logs grow with the index** (persistent; 2026-10-14, unit C2a): two logs applied
through two indices are in the indices' order as prefixes. A capability: the applied index's
invariant (`srvAppliedInv`, `appliedMono_of_inv`) keeps the applied logs in prefix order. -/
def appliedMono (γr : ReadNames) : IProp GF :=
  iprop(□ ∀ (i j : w64) (L1 L2 : mvcc.Log), ⌜uint.Z i ≤ uint.Z j⌝ -∗ appliedLogAt γr i L1 -∗
    appliedLogAt γr j L2 ={⊤}=∗ ⌜L1 <+: L2⌝)

instance appliedMono_persistent (γr : ReadNames) : Persistent (appliedMono (GF := GF) γr) := by
  unfold appliedMono; infer_instance

/-- **A write's witness for later reads** (persistent; 2026-10-14, unit C2a): the KV log `log` is
the log applied through an index `i` of the cluster's committed log (`committedAtLeast γr i`: the
raft loop raised the committed index past the entry before the apply thread applied it), and the
applied logs grow with the index (`appliedMono`). A linearizable read at `i` (`readLogOk γr i`)
reads a log that extends `log`. -/
def appliedWit (γr : ReadNames) (log : mvcc.Log) : IProp GF :=
  iprop(∃ i : w64, committedAtLeast γr i ∗ appliedLogAt γr i log ∗ appliedMono γr)

instance appliedWit_persistent (γr : ReadNames) (log : mvcc.Log) :
    Persistent (appliedWit (GF := GF) γr log) := by
  unfold appliedWit; infer_instance

/-- **`LinearizableReadNotify` succeeded**: the applied index has reached an index at least the
committed index `c` the caller knew of. -/
def readIndexOk (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(∃ ci₀ : w64, ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedAtLeast γr ci₀)

/-- **A served read** (persistent; 2026-10-14, unit T1): the client registered at `g` is in the
frozen list `gs` of a read round whose read index `ci` (at least the client's bound `c`) the
applied index has reached, and raft's witness of the round's update at `ci` (`srvReadWit`: the
round's clients' results at every committed log through an index at least `ci`). -/
def readServed (γr : ReadNames) (c : w64) (g : GName) : IProp GF :=
  iprop(∃ (ci ai : w64) (gs : List GName) (k : Nat),
    ⌜uint.Z c ≤ uint.Z ci ∧ uint.Z ci ≤ uint.Z ai ∧ gs[k]? = some g⌝ ∗
    appliedAtLeast γr ai ∗ srvReadWit γr.raft (readQs gs) ci)

instance readServed_persistent (γr : ReadNames) (c : w64) (g : GName) :
    Persistent (readServed (GF := GF) γr c g) := by
  unfold readServed; infer_instance

instance readIndexOk_persistent (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance

end readGhost


/-! ## The wait registry (`pkg/wait`) -/

section wait
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The request path's ghost names: the raft contract's, the ids', the wait's registered
ids' (`isWait`'s `γw`), and (2026-10-14, unit C2a) the read names the apply thread's answers are
stated at (`rd`: a result carries the read names' witness of its log, `resultIsW`; the apply
thread's view `isServer` has them the read side's). -/
structure ReqNames where
  wait : GName
  rd : ReadNames

/-- The raft contract's names: the read names' (2026-10-14, unit T1: until then a field). -/
abbrev ReqNames.raft (ρ : ReqNames) : ServerRaftNames := ρ.rd.raft

/-- The KV ghost state's names: the read names' (2026-10-14, unit T1). -/
abbrev ReqNames.kv (ρ : ReqNames) : KVNames := ρ.rd.kv

/-- The request ids' names: the KV ghost state's (D19c, 2026-10-18: until then a field), under
which the KV invariant keeps the committed requests' claims. -/
abbrev ReqNames.ids (ρ : ReqNames) : IdNames := ρ.rd.kv.ids


/-! ### The revisions' tokens (the vertical slice's unit V1) -/

/-- **The token of revision `r`** (the server's `etcdRevToken`, `v3rpc.etcdModelOfServer`):
the exclusive element `r ↪[E.γrev] ()` of the ghost map of revisions the apply thread minted. -/
def revTok (E : apply.AEnv GF) (r : w64) : IProp GF := r ↪[E.γrev] ()

/-- **Two tokens of one revision: impossible.** -/
theorem revTok_excl (E : apply.AEnv GF) (r : w64) : revTok E r ∗ revTok E r ⊢ False := by
  unfold revTok
  iintro ⟨H1, H2⟩
  ihave %H := ghostMapElem_ne E.γrev r r (DFrac.own 1) () () $$ H1 H2
  exact absurd rfl H

/-- **The authority of the revisions' tokens** at the KV's log `log` (the apply thread's, in
`srvApplyKV`): every revision minted so far is below the log's length. A revision is minted when
the log grows to it, once: the log only grows. -/
def revAuth (E : apply.AEnv GF) (log : mvcc.Log) : IProp GF :=
  iprop(∃ m : GMap w64 Unit, ghostMapAuth E.γrev 1 m ∗
    ⌜∀ k : w64, (m.lookup k).isSome → uint.nat k < log.length⌝)

/-- **What a step of the KV's log minted**: nothing (the log unchanged), or the token of the
revision it appended (`log.length`, the new log's last). -/
def revMinted (E : apply.AEnv GF) (log log' : mvcc.Log) : IProp GF :=
  iprop(⌜log' = log⌝ ∨
    ∃ cs : List mvcc.Change, ⌜log' = log ++ [cs]⌝ ∗ revTok E (W64 (log.length : Int)))

/-- A certified log has fewer than `2 ^ 63` revisions. -/
theorem idxCert_len (γ : mvcc.IdxNames) (log : mvcc.Log) :
    mvcc.idxCert (GF := GF) γ log ⊢ ⌜log.length < 2 ^ 63⌝ := by
  unfold mvcc.idxCert
  iintro ⟨-, %H, -⟩
  ipureintro; exact H.2.1

/-- Two certified logs have a certified common extension, one of them (the vertical slice's unit
V2: a read or a write opened at the longer of a log the server knows and a caller's floor). -/
theorem idxCert_join [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions] (γ : mvcc.IdxNames)
    (log F : mvcc.Log) :
    mvcc.idxCert (GF := GF) γ log ∗ mvcc.idxCert γ F ⊢
      ∃ L0 : mvcc.Log, mvcc.idxCert γ L0 ∗ ⌜log <+: L0 ∧ F <+: L0⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave %Hp := mvcc.idxCert_prefix γ log F $$ [$H1 $H2]
  rcases Hp with h | h
  · iexists F; iframe H2; ipureintro; exact ⟨h, List.prefix_refl _⟩
  · iexists log; iframe H1; ipureintro; exact ⟨List.prefix_refl _, h⟩

/-- **Minting**: a step of the log that appends at most one revision moves the authority along
and mints the new revision's token. -/
theorem revAuth_step (E : apply.AEnv GF) (log log' : mvcc.Log)
    (hg : log' = log ∨ ∃ cs, log' = log ++ [cs]) (hlen : log'.length < 2 ^ 63) (M : CoPset) :
    revAuth E log ={M}=∗ revAuth E log' ∗ revMinted E log log' := by
  unfold revAuth revMinted revTok
  iintro ⟨%m, Ha, %Hm⟩
  rcases hg with rfl | ⟨cs, rfl⟩
  · imodintro
    isplitl [Ha]
    · iexists m; iframe Ha; ipureintro; exact Hm
    · ileft; ipureintro; rfl
  · have hl : log.length < 2 ^ 63 := by simp at hlen; omega
    have hw : uint.nat (W64 (log.length : Int)) = log.length := by word
    have hk : m.lookup (W64 (log.length : Int)) = none := by
      cases h : m.lookup (W64 (log.length : Int)) with
      | none => rfl
      | some u =>
        have := Hm _ (by rw [h]; rfl)
        omega
    imod ghost_map_insert (W64 (log.length : Int)) () hk $$ Ha with ⟨Ha, Ht⟩
    imodintro
    isplitl [Ha]
    · iexists _
      iframe Ha
      ipureintro
      intro k hk'
      simp only [List.length_append, List.length_singleton]
      by_cases he : W64 (log.length : Int) = k
      · subst he; omega
      · rw [GMap.lookup_insert_ne _ _ he] at hk'
        have := Hm k hk'
        omega
    · iright; iexists cs; iframe Ht; ipureintro; rfl

theorem backendStep_grow {rq : apply.IRRModel} {log : mvcc.Log} {o : apply.Outcome}
    (h : apply.backendStep rq log o) :
    o.logAfter log = log ∨ ∃ cs, o.logAfter log = log ++ [cs] := by
  unfold apply.backendStep at h
  split at h
  · obtain ⟨op, -, h | h | h⟩ := h
    · rw [h.2]; left; rfl
    · rw [h.2.2]; left; rfl
    · rw [h.2]; right; exact ⟨_, rfl⟩
  · obtain ⟨op, -, h⟩ := h
    rw [h]; exact commitLog_grow _ _
  · rw [h]; left; rfl
  · obtain ⟨t, -, h | h⟩ := h
    · rw [h.1]; left; rfl
    · rw [h.1]; exact commitLog_grow _ _
  · obtain ⟨pend, -, h⟩ := h
    rw [h]; exact commitLog_grow _ _
  · exact h.elim
  · exact h.elim
  · rcases h with h | h <;> (rw [h]; left; rfl)

theorem chainStep_grow : ∀ (c : apply.Chain) {rq : apply.IRRModel} {log : mvcc.Log}
    {o : apply.Outcome}, apply.chainStep apply.backendStep c rq log o →
      o.logAfter log = log ∨ ∃ cs, o.logAfter log = log ++ [cs]
  | .backend, _, _, _, h => backendStep_grow h
  | .corrupt c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rw [h]; left; rfl
    · exact chainStep_grow c h
  | .capped c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rw [h]; left; rfl
    · split at h
      · rcases h with h | h
        · rw [h]; left; rfl
        · exact chainStep_grow c h
      · exact chainStep_grow c h
  | .auth _ c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · rw [h]; left; rfl
      · exact chainStep_grow c h
    · exact chainStep_grow c h
  | .quota c, _, _, _, h => by
    simp only [apply.chainStep] at h
    exact chainStep_grow c h

/-- **An application step appends at most one revision** to the KV's log. -/
theorem applyStep_grow {rq : apply.IRRModel} {v3 : Bool} {x x' : apply.ApplyKV}
    {out : apply.ApplyOut} (h : apply.applyStep rq v3 x x' out) :
    x'.log = x.log ∨ ∃ cs, x'.log = x.log ++ [cs] := by
  cases out with
  | skipped => rw [h.2]; left; rfl
  | rejected => rw [h.2]; left; rfl
  | dispatched o skip =>
    obtain ⟨-, hd, hl, -⟩ := h
    rw [hl]
    unfold apply.dispatchStep at hd
    split at hd
    · rw [hd]; left; rfl
    · split at hd
      · exact chainStep_grow _ hd
      · left; exact hd

/-! ### Floors (the vertical slice's unit V2) -/

/-- **The floor recorded at `γf`** (persistent, agreeing): the log `F` a request's proposer
recorded when it claimed the request's id (`idClaim`'s ghost name): a certified log the
request's client had seen. The apply thread runs a KV write at a log extending it
(`apply.kvFloorOk`): linearizability, `notes/decisions.md`, "Linearizability as a theorem". -/
def floorAt (γf : GName) (F : mvcc.Log) : IProp GF := dghostVar γf DFrac.discard F

instance floorAt_persistent (γf : GName) (F : mvcc.Log) : Persistent (floorAt (GF := GF) γf F) := by
  unfold floorAt; infer_instance

theorem floorAt_agree (γf : GName) (F F' : mvcc.Log) :
    ⊢ floorAt (GF := GF) γf F -∗ floorAt γf F' -∗ ⌜F = F'⌝ := by
  unfold floorAt
  iintro H1 H2
  iapply dghostVar_agree $$ H1 H2

/-- **The server's claimers' fact** (the id generator's `Φ`, `idGen ρ.ids g (srvFloorFact E)`):
a claim's ghost name records a certified floor. -/
def srvFloorFact (E : apply.AEnv GF) (_id : w64) (_d : List w8) (γf : GName) : IProp GF :=
  iprop(∃ F : mvcc.Log, floorAt γf F ∗ mvcc.idxCert E.γ.idx F)

instance srvFloorFact_timeless (E : apply.AEnv GF) (id : w64) (d : List w8) (γf : GName) :
    Timeless (srvFloorFact (GF := GF) E id d γf) := by
  unfold srvFloorFact floorAt mvcc.idxCert; infer_instance

/-- **The result `ar` of applying `rq`**: a non-nil `*apply.Result` of applying `rq` (with `v3`)
at some KV state `y`, to `y'` (`apply.applyStep`, `apply.applyResultIs`), with mvcc's
certificate of the log after, and what the step minted (`revMinted`: the token of the revision
it appended, if it appended one; the vertical slice's unit V1); and (unit V2) a KV write met the
floor `F` (`apply.applyFloorOk`: it ran at a log `y.log` extending `F`). -/
def resultIs (E : apply.AEnv GF) (rq : apply.IRRModel) (F : mvcc.Log) (ar : Loc) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out ∧ apply.applyFloorOk rq true F y.log out⌝ ∗
      apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log ∗ revMinted E y.log y'.log)

/-- **The result `ar` of applying `rq`, with its witness** (2026-10-14, unit C2a): `resultIs`
(with its minted token, `revMinted`, unit V1, and its floor, the vertical slice's unit V2), and
the log after is applied through an index of the committed log (`appliedWit γr y'.log`: the apply
thread deposits it before it hands the result over, `srvAppliedPre`); and (unit W-M3) the log the
entry met is `lb` (`y.log`: the proposer ties it to the raft prefix its update fired at,
`entryWit`) and the log after is certified (`certOk`: the KV model of a committed raft prefix,
what makes its revisions reached in the clients' model). Since linkv-txn stage B1 (2026-10-20)
the outcome is not waived (`out.waived = false`: the apply thread found the id registered, so a
transaction's ranges were run): a result reaches the registered proposer only then. -/
def resultIsW (E : apply.AEnv GF) (γr : ReadNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (ar : Loc) (lb : mvcc.Log) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out ∧ apply.applyFloorOk rq true F y.log out ∧ y.log = lb ∧
        out.waived = false⌝ ∗
      apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log ∗ revMinted E y.log y'.log ∗ appliedWit γr y'.log ∗
      mvcc.certOk E.γ y'.log)

/-- **The committed entry a result is of** (persistent; 2026-10-14, unit T1): an entry `e` at
position `m` of a committed log `L`, normal, its data claimed under the id of `rq` (with some
floor's ghost name, the vertical slice's unit V2), which they decode to (the proposer, who claimed
its own data under that id, learns `e.data` are its data, and collects its proposal's result there,
`srvPropWits`); and (unit W-M3) the KV model of the raft prefix before it is `lb`, the log the
entry met (`resultIsW`'s): so the proposer's update fired at the state of the log the write met. -/
def entryWit (ρ : ReqNames) (rq : apply.IRRModel) (lb : mvcc.Log) : IProp GF :=
  iprop(∃ (L : List EntryModel) (m : Nat) (e : EntryModel) (id : w64) (γf : GName),
    srvRLogLb ρ.raft L ∗ idClaim ρ.ids id e.data γf ∗
    ⌜L[m]? = some e ∧ e.typ = W32 0 ∧ apply.irrDecode e.data = some rq ∧
      apply.irrId rq = some id ∧ kvModel ρ.kv (L.take m) = lb⌝)

instance entryWit_persistent (ρ : ReqNames) (rq : apply.IRRModel) (lb : mvcc.Log) :
    Persistent (entryWit (GF := GF) ρ rq lb) := by
  unfold entryWit; infer_instance

/-- **The result the proposer of `rq` (with the floor `F`, the vertical slice's unit V2)
expects**: the `*apply.Result` `ar` (as an interface value) with `resultIsW E ρ.rd rq F ar`
(`resultIs` until 2026-10-14, unit C2a), its trace (`apply.resTrace`, unit P1b), and (2026-10-14,
unit T1) the committed entry it is of (`entryWit`, unit W-M3: at the log `lb` the entry met). -/
def resultΨ (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (x : GoInterface) : IProp GF :=
  iprop(∃ (ar : Loc) (lb : mvcc.Log),
    ⌜x = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar⌝ ∗
    apply.resTrace ar ∗ resultIsW E ρ.rd rq F ar lb ∗ entryWit ρ rq lb)

/-- **The server's registration condition**: the expectation of a registered id is
`resultΨ E ρ rq F` for the request `rq` its data decode to, the id claimed for those data with a
ghost name recording the floor `F` (the vertical slice's unit V2); and (D21e (A), stage M4) the id
is of the member's prefix (its generator issued it), so an entry of another member's id has no
waiter here. -/
def reqWaitR (ρ : ReqNames) (E : apply.AEnv GF) (id : w64)
    (Ψ : GoInterface → IProp GF) : IProp GF :=
  iprop(∃ (d : List w8) (rq : apply.IRRModel) (γf : GName) (F : mvcc.Log), idClaim ρ.ids id d γf ∗
    floorAt γf F ∗ ⌜apply.irrDecode d = some rq ∧ Ψ = resultΨ E ρ rq F ∧ idPfx id = ρ.ids.pfx⌝)

/-- **The server's wait** `s.w` (persistent): a `wait.Wait` (`wait.New`'s contract) with the
server's registration condition, the ids `ρ.ids`, the registered ids' map `ρ.wait`, and some
reader's resource (the apply thread's `srvApplyKV` holds `IsRegistered`'s, as the apply package's
`waitOk`). Replaces the apply package's `waitOk` in `srvFieldsAt` (unit 2). Since linkv-txn stage
B1 (2026-10-20) also `ρ.wait` as the member's entry of the cluster's registries' map. -/
def waitInv (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) : IProp GF :=
  iprop((∃ RD : IProp GF, isWait w ρ.ids ρ.wait (reqWaitR ρ E) RD) ∗
    -- (linkv-txn stage B1, 2026-10-20) the member's registry in the cluster's registries' map
    idWaitIs ρ.ids ρ.ids.pfx ρ.wait)

instance waitInv_persistent (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) :
    Persistent (waitInv (GF := GF) w ρ E) := by
  unfold waitInv; infer_instance

/-- **What the apply thread knows of a committed entry's id** (persistent; the raft contract's
apply side, `batchCommitted`, gives the first half; unit 4): a normal entry's data, if they
decode to a request with an id, were claimed under that id, and (linkv-txn stage B1) the id
registered (`idRegd`); a conf change's id (`ccIdOf`) is no
KV request's registration (the conf change's proposer claimed it for the conf change: typed
claims, unit 4), and the change is one `applyConfChange` takes (`ccPolOk` at raft's
configuration; audit phase B3, 2026-10-18). -/
def entryWaitOk (ρ : ReqNames) (E : apply.AEnv GF) (m : EntryModel) : IProp GF :=
  if m.typ = W32 0 then
    iprop((∀ (rq : apply.IRRModel) (id : w64),
      ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
        (∃ γf : GName, idClaim ρ.ids id m.data γf) ∗ idRegd ρ.ids id) ∗
      ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L⌝)
  else iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
    ⌜ccPolOk ρ.raft.raft m.data⌝)

instance entryWaitOk_persistent (ρ : ReqNames) (E : apply.AEnv GF) (m : EntryModel) :
    Persistent (entryWaitOk (GF := GF) ρ E m) := by
  unfold entryWaitOk; split <;> infer_instance

/-- `entryWaitOk` of every entry of a batch (persistent). -/
def batchWaitOk (ρ : ReqNames) (E : apply.AEnv GF) (ms : List EntryModel) : IProp GF :=
  iprop(□ ∀ m, ⌜m ∈ ms⌝ -∗ entryWaitOk ρ E m)

instance batchWaitOk_persistent (ρ : ReqNames) (E : apply.AEnv GF) (ms : List EntryModel) :
    Persistent (batchWaitOk (GF := GF) ρ E ms) := by
  unfold batchWaitOk; infer_instance

/-! ## The raft contract -/

/-- **The server's raft node `n`** (persistent; the `Node` field of the server's `raftNode`):
its `Propose(ctx, data)`, from any goroutine, at any context, with `data`'s slice read-only, is
the verified `node.Propose`'s statement over the server's ghost names (see the file header), and
its error is `nil` or one the gRPC layer can take (`applyErrIs`: raft's `ErrStopped`,
`ErrProposalDropped`, `errors.New` errors, or the context's `Canceled`/`DeadlineExceeded`;
2026-10-12, unit 3a). A theorem since stage R7b (`NodeBridge.lean`, `raftPropose_of_isNode`).
**`ApplyConfChange(c)`** (audit phase B3, 2026-10-18; `applyConfChange`'s call): of a v1 change,
read-only, that leaves raft's configuration as it is (`ccRaftOk`, raft's static mode's
`CCShrink`), it returns the new `*ConfState`, owned (`node.ApplyConfChange.spec`); (D43 M3,
2026-10-25) in raft's static mode (`reDyn = none`): the dynamic mode's is `raftApplyCCDyn`. -/
def raftPropose (γ : ServerRaftNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗ srvRaftLogInv γ ∗ srvPropWits γ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (data_sl : GoSlice)
        (data : List w8) (Q : List EntryModel → IProp GF),
      -- (2026-10-16, stage R7b, B3) non-empty data: raft's `node.Propose` wants it (D6: an empty
      -- proposal would be a leader's own entry); the server's request marshals to a non-empty
      -- string (`irrWireOf`, `processInternalRaftRequestOnce`)
      {{ mvcc.txnCtx ctx cd ∗ data_sl ↦*□ data ∗ ⌜data ≠ []⌝ ∗ srvPropArg γ data Q ∗ £ 1 }}
        (App (App (Val #(methods ni.ty go!"Propose" ni.v)) (Val #(GoInterface.ok ctx)))
          (Val #data_sl))
      {{ (err : GoInterface), RET #err; srvPropRes γ data Q ∗ applyErrIs err }}) ∗
    □ (∀ (c : GoInterface) (cm : ConfChangeM), ⌜γ.raft.dyn = false⌝ -∗ ⌜ccRaftOk γ.raft.cfg cm⌝ -∗
      {{ ownConfChangeI c DFrac.discard (some (.v1 cm)) }}
        (App (Val #(methods ni.ty go!"ApplyConfChange" ni.v)) (Val #c))
      {{ (csp : Loc), RET #csp; ∃ cs : ConfStateM, csPts csp (DFrac.own 1) cs true }}))

instance raftPropose_persistent (γ : ServerRaftNames) (n : GoInterface) :
    Persistent (raftPropose (GF := GF) γ n) := by
  unfold raftPropose; infer_instance

end wait

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvRAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"r" s
/-- The address of the server's raft `Node` (`s.r.raftNodeConfig.Node`). -/
abbrev srvNodeAddr (s : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"Node" (structFieldRef raftNode go!"raftNodeConfig" (srvRAddr s))
abbrev srvReqIDGenAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"reqIDGen" s
abbrev srvReadAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"read" s
abbrev srvAuthStoreAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"authStore" s
abbrev srvKVAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"kv" s
abbrev srvDoneAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"done" s
abbrev srvCommittedIndexAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"committedIndex" s
/-- The address of `s.appliedIndex` (moved here from `InvApplier.lean`, 2026-10-13, unit 4b). -/
abbrev srvAppliedIndexAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"appliedIndex" s

end addrs

section raftNode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server `s`'s raft node** (persistent): `s.r`'s `Node` is fixed and meets the raft
contract. -/
def srvRaftNode (s : Loc) (γ : ServerRaftNames) : IProp GF :=
  iprop(∃ n : GoInterface, srvNodeAddr s ↦□ n ∗ raftPropose γ n)

instance srvRaftNode_persistent (s : Loc) (γ : ServerRaftNames) :
    Persistent (srvRaftNode (GF := GF) s γ) := by
  unfold srvRaftNode; infer_instance

end raftNode

section applied
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The server's atomics' invariants' namespace (moved here from `InvApplier.lean`, 2026-10-13). -/
abbrev srvN : Namespace := nroot.@"server"

/-- The applied logs' keys at the applied index `v`: at most `v`, or `v + 1` once its log is
deposited ahead (`p`, unit C2a). -/
def appliedKeysOk (M : GMap w64 mvcc.Log) (v : w64) (p : Bool) : Prop :=
  ∀ k L', M.lookup k = some L' → uint.Z k ≤ uint.Z v ∨ (p = true ∧ uint.Z k = uint.Z v + 1)

/-- The applied logs are in their indices' order as prefixes (unit C2a). -/
def appliedMonoMap (M : GMap w64 mvcc.Log) : Prop :=
  ∀ k k' L1 L2, M.lookup k = some L1 → M.lookup k' = some L2 → uint.Z k ≤ uint.Z k' → L1 <+: L2

/-- A deposit at the next index of a log extending the current one keeps the order. -/
theorem appliedMonoMap_insert (M : GMap w64 mvcc.Log) (v v' : w64) (L0 L : mvcc.Log)
    (hk : ∀ k L', M.lookup k = some L' → uint.Z k ≤ uint.Z v) (hmono : appliedMonoMap M)
    (hv : M.lookup v = some L0) (hp : L0 <+: L) (hv' : uint.Z v < uint.Z v') :
    appliedMonoMap (M.insert v' L) := by
  intro k k' L1 L2 h1 h2 hle
  rw [GMap.lookup_insert_Some] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨hk1, h1⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨hk2, h2⟩
  · exact List.prefix_refl _
  · have := hk k' L2 h2; omega
  · exact (hmono k v L1 L0 h1 hv (hk k L1 h1)).trans hp
  · exact hmono k k' L1 L2 h1 h2 hle

/-- **The applied index's invariant** (persistent; the request path's unit 4b, see
`notes/decisions.md`, "The applied index: a certified log per index"): the atomic
`s.appliedIndex` at `v`, half of the authority of the applied index's lower bounds (`γr.applied`:
the apply thread, the only writer, holds the other half, `srvAppliedOwn`) at `v`, the authority of
the applied logs (`γr.logs`), every key at most `v` (so `setAppliedIndex` of a larger index
deposits a fresh one), and the log applied through `v`, with mvcc's certificate. Since 2026-10-14
(unit C2a): half of the ghost variable `γr.pend` (`p`: the apply thread deposited the log of `v +
1` ahead, `applied_predeposit`, so the key `v + 1` may be present), and the applied logs in their
indices' order as prefixes (`appliedMonoMap`: what `appliedMono` reads). Since 2026-10-14 (unit
T1): every applied log the KV model of the committed raft log through its index (`kvLogsOk`).

(D22 J5, 2026-10-26) **The atomic lags the ghost index**: the atomic is at some `v` at most the
ghost applied index `a` (`uint.Z v ≤ uint.Z a`), and the authority, the applied logs' keys and the
current log are the ghost index's. Go's `applySnapshot` raises the applied index (`ep.appliedi`)
to the snapshot's without calling `setAppliedIndex` (`issues/etcd-applied-index-stale-after-snapshot.md`),
so after a snapshot the atomic stays behind until the next entry's `setAppliedIndex`: the ghost
index jumps (`applied_jump`), the atomic does not. A reader of the atomic still learns a lower
bound of the ghost index (`appliedAtLeast γr v`). Until J5 the atomic was the ghost index. -/
def srvAppliedBody (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ (v a : w64) (L : mvcc.Log) (M : GMap w64 mvcc.Log) (p : Bool),
    sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v ∗
    monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat a) ∗
    ghostMapAuth γr.logs 1 M ∗ ghostVar γr.pend (1 : Qp).half p ∗
    ⌜uint.Z v ≤ uint.Z a ∧ appliedKeysOk M a p ∧ appliedMonoMap M⌝ ∗
    appliedLogAt γr a L ∗ mvcc.idxCert E.γ.idx L ∗ kvLogsOk γr M)

/-- The applied index's invariant: `srvAppliedBody` (see there). -/
def srvAppliedInv (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  inv srvN (srvAppliedBody s E γr)

instance srvAppliedInv_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAppliedInv s E γr) := by
  unfold srvAppliedInv; infer_instance

/-- **The apply thread's half of the applied index's authority** at `v` (the only writer of
`s.appliedIndex`; `setAppliedIndex` moves it), and (2026-10-14, unit C2a) its half of `γr.pend`,
`false`: the next index's log not deposited yet. -/
def srvAppliedOwn (γr : ReadNames) (v : w64) : IProp GF :=
  iprop(monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat v) ∗ ghostVar γr.pend (1 : Qp).half false)

/-- **The apply thread at the applied index `v`, the log `L` of the next index `v'` deposited
ahead** (2026-10-14, unit C2a; `applied_predeposit`): what `setAppliedIndex(v')` takes. -/
def srvAppliedPre (γr : ReadNames) (v v' : w64) (L : mvcc.Log) : IProp GF :=
  iprop(monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat v) ∗ ghostVar γr.pend (1 : Qp).half true ∗
    appliedLogAt γr v' L ∗ ⌜uint.Z v' = uint.Z v + 1⌝)

/-- The deposited log, kept. -/
theorem srvAppliedPre_log (γr : ReadNames) (v v' : w64) (L : mvcc.Log) :
    srvAppliedPre (GF := GF) γr v v' L ⊢ srvAppliedPre γr v v' L ∗ appliedLogAt γr v' L := by
  iintro H
  iunfold srvAppliedPre at H
  icases H with ⟨Ha, Hp, #HL, %Hv⟩
  iframe HL
  iunfold srvAppliedPre
  iframe Ha Hp HL
  ipureintro; exact Hv

/-- The apply thread's half gives a lower bound of the applied index. -/
theorem srvAppliedOwn_lb (γr : ReadNames) (v : w64) :
    srvAppliedOwn (GF := GF) γr v ⊢ srvAppliedOwn γr v ∗ appliedAtLeast γr v := by
  iintro H
  iunfold srvAppliedOwn at H
  icases H with ⟨Ha, Hp⟩
  ihave #Hlb := monoNatLbOwn_get γr.applied _ _ $$ Ha
  iunfold srvAppliedOwn
  iunfold appliedAtLeast
  iframe Ha Hp Hlb

/-- **The log after the next entry, deposited ahead** (2026-10-14, unit C2a): the apply thread at
the applied index `v`, whose log is `L₀` (`appliedLogAt γr v L₀`), deposits a log `L` extending it
as the log applied through `v' = v + 1`, before `setAppliedIndex(v')` publishes the index: so the
proposer of the entry learns `appliedLogAt γr v' L` with its result. -/
theorem applied_predeposit (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v v' : w64)
    (L₀ L : mvcc.Log) (hv : uint.Z v' = uint.Z v + 1) (hp : L₀ <+: L) :
    ⊢ srvAppliedInv (GF := GF) s E γr -∗ srvAppliedOwn γr v -∗ appliedLogAt γr v L₀ -∗
      kvLogAt γr v' L ={⊤}=∗ srvAppliedPre γr v v' L := by
  iintro #Hinv Hown #HL₀ #HkA
  iunfold srvAppliedInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBody at Hi
  icases Hi with ⟨%vat, %v0, %Lc, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HLc, >#Hc, >#Hkl⟩
  iunfold srvAppliedOwn at Hown
  icases Hown with ⟨Hown, Hpo⟩
  ihave %Hag := monoNatAuthOwn_agree γr.applied _ _ _ _ $$ Hown Hauth
  have hv0 : v0 = v := by
    have h2 := Hag.2
    unfold uint.nat at h2
    exact (BitVec.eq_of_toNat_eq h2).symm
  subst hv0
  ihave %Hpg := ghostVar_agree γr.pend _ _ _ _ $$ Hpo Hp
  subst Hpg
  ihave %HLeq := appliedLogAt_agree γr v0 Lc L₀ $$ HLc HL₀
  subst HLeq
  ihave %HMv : iprop(⌜M.lookup v0 = some Lc⌝) $$ [HM]
  · iunfold appliedLogAt at HLc
    iapply ghost_map_lookup $$ HM HLc
  have hk : ∀ k L', M.lookup k = some L' → uint.Z k ≤ uint.Z v0 := by
    intro k L' h
    rcases HMk.2.1 k L' h with h | ⟨h, -⟩
    · exact h
    · cases h
  have hfresh : M.lookup v' = none := by
    cases h : M.lookup v' with
    | none => rfl
    | some L' => have := hk v' L' h; omega
  imod ghost_map_insert_persist v' L hfresh $$ HM with ⟨HM, #HLv'⟩
  imod ghostVar_update_halves true γr.pend false false $$ Hpo Hp with ⟨Hpo, Hp⟩
  ihave #Hkl' := kvLogsOk_insert γr M v' L $$ [Hkl HkA]
  · iframe Hkl HkA
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBody
    iexists vat, v0, Lc, M.insert v' L, true
    iframe Hat Hauth HM Hp HLc Hc Hkl'
    ipureintro
    refine ⟨HMk.1, ?_, appliedMonoMap_insert M v0 v' Lc L hk HMk.2.2 HMv hp (by omega)⟩
    intro k L' h
    rw [GMap.lookup_insert_Some] at h
    rcases h with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact Or.inr ⟨rfl, hv⟩
    · exact Or.inl (hk k L' h)
  imodintro
  iunfold srvAppliedPre
  iframe Hown Hpo
  isplitr
  · iunfold appliedLogAt; iexact HLv'
  ipureintro; exact hv

/-- Two halves of a mono nat's authority move together. -/
theorem monoNat_halves_update (γ : GName) (n n' : Nat) (h : n ≤ n') :
    ⊢ monoNatAuthOwn (GF := GF) γ (1 : Qp).half n -∗ monoNatAuthOwn γ (1 : Qp).half n ==∗
      monoNatAuthOwn γ (1 : Qp).half n' ∗ monoNatAuthOwn γ (1 : Qp).half n' ∗ monoNatLbOwn γ n' := by
  iintro H1 H2
  have hf := (monoNatAuthOwn_fractional (GF := GF) γ n).fractional (1 : Qp).half (1 : Qp).half
  have hf' := (monoNatAuthOwn_fractional (GF := GF) γ n').fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf hf'
  ihave H := hf.2 $$ [H1 H2]
  · iframe H1 H2
  imod mono_nat_own_update n' h $$ H with ⟨H, #Hlb⟩
  icases hf'.1 $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2 Hlb

/-- (D22 J5, 2026-10-26) **The ghost applied index jumps** (a snapshot's install): the apply
thread at the ghost index `a` with its log `L₀`, no log deposited ahead (`srvAppliedOwn`), raises
the ghost index to `i > a` and publishes `L`, extending `L₀`, the KV model of the committed log
through `i` (`kvLogAt`), with mvcc's certificate, as the log applied through `i`. The atomic
`s.appliedIndex` is not touched (Go's `applySnapshot` does not call `setAppliedIndex`): it lags
until the next entry's `setAppliedIndex`. -/
theorem applied_jump (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (a i : w64)
    (L₀ L : mvcc.Log) (hi : uint.Z a < uint.Z i) (hp : L₀ <+: L) :
    ⊢ srvAppliedInv (GF := GF) s E γr -∗ srvAppliedOwn γr a -∗ appliedLogAt γr a L₀ -∗
      kvLogAt γr i L -∗ mvcc.idxCert E.γ.idx L ={⊤}=∗
      srvAppliedOwn γr i ∗ appliedAtLeast γr i ∗ appliedLogAt γr i L := by
  iintro #Hinv Hown #HL₀ #HkA #HcL
  iunfold srvAppliedInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBody at Hi
  icases Hi with ⟨%vat, %v0, %Lc, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HLc, >#Hc, >#Hkl⟩
  iunfold srvAppliedOwn at Hown
  icases Hown with ⟨Hown, Hpo⟩
  ihave %Hag := monoNatAuthOwn_agree γr.applied _ _ _ _ $$ Hown Hauth
  have hv0 : v0 = a := by
    have h2 := Hag.2
    unfold uint.nat at h2
    exact (BitVec.eq_of_toNat_eq h2).symm
  subst hv0
  ihave %Hpg := ghostVar_agree γr.pend _ _ _ _ $$ Hpo Hp
  subst Hpg
  ihave %HLeq := appliedLogAt_agree γr v0 Lc L₀ $$ HLc HL₀
  subst HLeq
  ihave %HMv : iprop(⌜M.lookup v0 = some Lc⌝) $$ [HM]
  · iunfold appliedLogAt at HLc
    iapply ghost_map_lookup $$ HM HLc
  have hk : ∀ k L', M.lookup k = some L' → uint.Z k ≤ uint.Z v0 := by
    intro k L' h
    rcases HMk.2.1 k L' h with h | ⟨h, -⟩
    · exact h
    · cases h
  have hfresh : M.lookup i = none := by
    cases h : M.lookup i with
    | none => rfl
    | some L' => have := hk i L' h; omega
  imod ghost_map_insert_persist i L hfresh $$ HM with ⟨HM, #HLi⟩
  ihave #Hkl' := kvLogsOk_insert γr M i L $$ [Hkl HkA]
  · iframe Hkl HkA
  imod monoNat_halves_update γr.applied (uint.nat v0) (uint.nat i) (by word) $$ Hown Hauth
    with ⟨Hown, Hauth, #Hlb⟩
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBody
    iexists vat, i, L, M.insert i L, false
    iframe Hat Hauth HM Hp HcL Hkl'
    isplitr
    · ipureintro
      refine ⟨by omega, ?_, appliedMonoMap_insert M v0 i Lc L hk HMk.2.2 HMv hp hi⟩
      intro k L' h
      rw [GMap.lookup_insert_Some] at h
      rcases h with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact Or.inl (Int.le_refl _)
      · exact Or.inl (by have := hk k L' h; omega)
    iunfold appliedLogAt; iexact HLi
  imodintro
  iunfold srvAppliedOwn
  iframe Hown Hpo
  iunfold appliedAtLeast
  iframe Hlb
  iunfold appliedLogAt; iexact HLi

/-- **The applied logs grow with the index** (`appliedMono`, from the invariant). -/
theorem appliedMono_of_inv (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAppliedInv (GF := GF) s E γr ⊢ appliedMono γr := by
  iintro #Hinv
  iunfold appliedMono
  iintro !> %i %j %L1 %L2 %hij #H1 #H2
  iunfold srvAppliedInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBody at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  ihave %Hm1 : iprop(⌜M.lookup i = some L1⌝) $$ [HM]
  · iunfold appliedLogAt at H1
    iapply ghost_map_lookup $$ HM H1
  ihave %Hm2 : iprop(⌜M.lookup j = some L2⌝) $$ [HM]
  · iunfold appliedLogAt at H2
    iapply ghost_map_lookup $$ HM H2
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBody
    iexists vat, v, L, M, p
    iframe Hat Hauth HM Hp HL Hc Hkl
    ipureintro; exact HMk
  imodintro
  ipureintro
  exact HMk.2.2 i j L1 L2 Hm1 Hm2 hij

/-- **An applied log is the KV model of the committed raft log through its index** (2026-10-14,
unit T1). -/
theorem appliedLogAt_kvLogAt (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (i : w64) (L1 : mvcc.Log) :
    ⊢ srvAppliedInv (GF := GF) s E γr -∗ appliedLogAt γr i L1 ={⊤}=∗ kvLogAt γr i L1 := by
  iintro #Hinv #H1
  iunfold srvAppliedInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBody at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  ihave %Hm1 : iprop(⌜M.lookup i = some L1⌝) $$ [HM]
  · iunfold appliedLogAt at H1
    iapply ghost_map_lookup $$ HM H1
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBody
    iexists vat, v, L, M, p
    iframe Hat Hauth HM Hp HL Hc Hkl
    ipureintro; exact HMk
  imodintro
  iunfold kvLogsOk at Hkl
  icases Hkl with ⟨%Lb, #Hlb, %Hm⟩
  obtain ⟨A, hA, hi, hL⟩ := Hm i L1 Hm1
  iunfold kvLogAt
  iexists A
  isplitr
  · iapply srvRLogLb_mono γr.raft A Lb hA $$ Hlb
  ipureintro; exact ⟨hi, hL⟩

/-- **The committed index's invariant** (persistent; unit 4b, symmetric to `srvAppliedInv`, no
log): the atomic `s.committedIndex` at `v` and half of the authority of the committed index's
lower bounds (`γr.committed`) at `v`; the writer (`updateCommittedIndex`, the raft loop's ready
handler, unit 4c) holds the other half, `srvCommittedOwn`. -/
def srvCommittedInv (s : Loc) (γr : ReadNames) : IProp GF :=
  inv srvN iprop(∃ v : w64,
    sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) v ∗
    monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v) ∗
    -- (2026-10-16, stage R7b) the committed log the index was read from: raft's `ReadIndex`
    -- needs a committed log of length at least the bound a caller passes
    (∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜uint.Z v ≤ uint.Z γr.raft.ai0 + L.length⌝))

instance srvCommittedInv_persistent (s : Loc) (γr : ReadNames) :
    Persistent (srvCommittedInv (GF := GF) s γr) := by
  unfold srvCommittedInv; infer_instance

/-- **A lower bound of the committed index has a committed log at least that long** (2026-10-16,
stage R7b: what raft's `ReadIndex` takes for the bound). -/
theorem committedAtLeast_log (s : Loc) (γr : ReadNames) (n : w64) (E : CoPset)
    (hE : ↑srvN ⊆ E) :
    ⊢ srvCommittedInv (GF := GF) s γr -∗ committedAtLeast γr n ={E}=∗
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜uint.Z n ≤ uint.Z γr.raft.ai0 + L.length⌝ := by
  iintro #Hinv #Hn
  iunfold srvCommittedInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%v, Hv, Hauth, ⟨%L, #HL, %HvL⟩⟩
  iunfold committedAtLeast at Hn
  ihave %Hle := monoNatLbOwn_valid γr.committed _ _ _ $$ Hauth Hn
  imod Hclose $$ [Hv Hauth] with -
  · inext; iexists v; iframe Hv Hauth; iexists L; iframe HL; ipureintro; exact HvL
  imodintro
  iexists L
  iframe HL
  ipureintro
  have h := Hle.2
  have h1 := uint_nat_eq n
  have h2 := uint_nat_eq v
  omega

/-- **The writer's half of the committed index's authority** at `v` (unit 4c's
`updateCommittedIndex`; unused in 4b). -/
def srvCommittedOwn (γr : ReadNames) (v : w64) : IProp GF :=
  monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v)

/-- The committed index's writer half, if the caller holds it (`some v`): what
`getCommittedIndex` may take, to learn the index is exactly `v` (2026-10-13, the request path's
unit 4c: the ready handler's `updateCommittedIndex` reads it before raising it). -/
def srvCommittedOwnOpt (γr : ReadNames) : Option w64 → IProp GF
  | none => iprop(True)
  | some v => srvCommittedOwn γr v

/-- **The applied and committed indices' invariants, at some names** (persistent): the proposer's
view (`srvReqFieldsAt`: it reads both indices only for the request limit's gap, so it needs no
particular names). -/
def srvIndexInvs (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γr : ReadNames, srvAppliedInv s E γr ∗ srvCommittedInv s γr)

instance srvIndexInvs_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvIndexInvs (GF := GF) s E) := by
  unfold srvIndexInvs; infer_instance

/-- **A lower bound of the applied index has a certified applied log**: from `readIndexOk γr c`
(the applied index reached some `ci₀ ≥ c`) and the applied index's invariant, the log applied
through the current applied index `v ≥ ci₀`, with mvcc's certificate. -/
theorem readIndexOk_log (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    ⊢ srvAppliedInv s E γr -∗ readIndexOk γr c ={⊤}=∗
      ∃ (ci₀ : w64) (L₀ : mvcc.Log), ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedLogAt γr ci₀ L₀ ∗
        mvcc.idxCert E.γ.idx L₀ := by
  iintro #Hinv #Hok
  iunfold readIndexOk at Hok
  icases Hok with ⟨%ci, %Hci, #Hlb⟩
  iunfold srvAppliedInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBody at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  iunfold appliedAtLeast at Hlb
  ihave %Hle := monoNatLbOwn_valid γr.applied _ _ _ $$ Hauth Hlb
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext; iunfold srvAppliedBody; iexists vat, v, L, M, p; iframe Hat Hauth HM Hp HL Hc Hkl; ipureintro; exact HMk
  imodintro
  iexists v, L
  iframe HL Hc
  ipureintro
  have h2 := Hle.2
  word

end applied

section readAddrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the read loop's current notifier (`r.notifier`). -/
abbrev readNotifierAddr (r : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"notifier" r
/-- The address of the read loop's lock (`r.mux`). -/
abbrev readMuAddr (r : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"mux" r

end readAddrs

section read
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The read loop's lock resource** at fraction `q` (`r.mux`, a `sync.RWMutex`; 2026-10-13, the
request path's unit 4a): `r.notifier` (at `q`) and the ghost variable of the current notifier and
its need's name (at `q / 2`; the read invariant holds the other half, `read/Inv.lean`). A reader
(`LinearizableReadNotify`) learns which notifier is current; the writer (the loop) swaps it. -/
def readMuP (r : Loc) (γr : ReadNames) (q : Qp) : IProp GF :=
  iprop(∃ (nc : Loc) (γn : NeedNames), (readNotifierAddr r ↦{DFrac.own q} nc : IProp GF) ∗
    ghostVar γr.notifier q.half (nc, γn))

/-- **A reader slot of the read loop's lock** (`r.mux`): Perennial's `RWMutex` admits a bounded
number of readers (`sync.ownRWMutex`), so each goroutine calling `LinearizableReadNotify` holds
one (as `srvLgReader` for `s.lgMu`; `read.NewRead` returns them). -/
def readReader (r : Loc) (γr : ReadNames) : IProp GF :=
  sync.ownRWMutex (GF := GF) (readMuAddr r) (readMuP r γr)

/-- **The `*read.Read` `r`** (persistent; `read.NewRead`'s result, `read/Results.lean`, the request
path's unit 4a): `LinearizableReadNotify(ctx)`, with a reader slot of `r.mux` (`readReader`, given
back; 2026-10-13, unit 4a: Perennial's `RWMutex` bounds the readers), returns `nil` only once the
applied index has reached the committed index the caller knew of (`readIndexOk`), or an error
the gRPC layer can take (`applyErrIs`: the read loop's `ErrStopped`, `ErrLeaderChanged`, ...,
`errors.New` errors, or the context's `Canceled`/`DeadlineExceeded`; 2026-10-12, unit 3b, as
`raftPropose`). The deposit at the state function `F` (E3r; by default the mode `off`'s). -/
def isReadNotify (r : Loc) (γr : ReadNames) (F : List EntryModel → KVState := kvStOff γr.kv) :
    IProp GF :=
  iprop(□ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (c : w64) (g : GName)
      (Q : List EntryModel → IProp GF),
    {{ mvcc.txnCtx ctx cd ∗ committedAtLeast γr c ∗ readReader r γr ∗
        savedPredOwn g DFrac.discard Q ∗ kvDep γr.kv Q F }}
      (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
        go!"LinearizableReadNotify")) (Val #(GoInterface.ok ctx)))
    {{ (err : GoInterface), RET #err; readReader r γr ∗ applyErrIs err ∗
        (⌜err = GoInterface.nil⌝ -∗ readIndexOk γr c ∗ readServed γr c g) }}))

instance isReadNotify_persistent (r : Loc) (γr : ReadNames) (F : List EntryModel → KVState) :
    Persistent (isReadNotify (GF := GF) r γr F) := by
  unfold isReadNotify; infer_instance

/-- The `*auth.AuthInfo` `a` (not nil): its `Username` and `Revision`, read-only. -/
def authInfoIs (a : Loc) (user : GoString) (rev : w64) : IProp GF :=
  iprop(⌜a ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.auth.AuthInfo go!"Username" a ↦□ user ∗
    structFieldRef go_etcd_io.etcd.server.v3.auth.AuthInfo go!"Revision" a ↦□ rev)

/-- An auth info returned by the auth store: `nil`, or one with its fields. -/
def authInfoOpt (a : Loc) : IProp GF :=
  iprop(⌜a = null⌝ ∨ ∃ user rev, authInfoIs a user rev)

/-- **The auth store's request side** (persistent): `AuthInfoFromCtx(ctx)`, with the caller's
reader resource `RD` (held and given back; 2026-10-14, unit A2: the real method read-locks
`enabledMu`), returns an auth info (or `nil`) and an error (`nil`, or one the gRPC layer can take:
`applyErrIs`; 2026-10-12, unit 3a); `AuthInfoFromTLS(ctx)` an auth info (or `nil`). Of the real
store: `isReqAuth_of_authInv` (`AuthReqDerive.lean`). The permission checks and `Revision` are the
apply package's `isAuthStore`. -/
def isReqAuth (st : GoInterface) (RD : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd ∗ RD }}
        (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
          applyErrIs err }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd }}
        (App (Val #(methods ai.ty go!"AuthInfoFromTLS" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc), RET #a; authInfoOpt a }}))

instance isReqAuth_persistent (st : GoInterface) (RD : IProp GF) :
    Persistent (isReqAuth (GF := GF) st RD) := by
  unfold isReqAuth; infer_instance

/-- **The request side with the token binding** (persistent; the auth plan's S5, 2026-10-24):
`isReqAuth`'s `AuthInfoFromCtx`, whose auth info is moreover bound to the context's own token in
the mode `M` (`auth.ctxBound`: the token `auth.ctxTokenOf ctx` its metadata carries, the auth plan's
E2c; in `on γa`, its user is one the token was issued to). Stated beside
`isReqAuth` (which the request path's and `NewAuthStore`'s statements name) rather than in it; with
auth on, a row of the server's reader view (`srvReadFieldsAt`). Of the real store:
`isReqAuthBound_of_authInv` (`AuthReqDerive.lean`). -/
def isReqAuthBound (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd ∗ RD }}
        (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
          applyErrIs err ∗ auth.ctxBound M (GoInterface.ok ctx) a }}))

instance isReqAuthBound_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) :
    Persistent (isReqAuthBound (GF := GF) st RD M) := by
  unfold isReqAuthBound; infer_instance

end read

end EtcdGrove
end Perennial
