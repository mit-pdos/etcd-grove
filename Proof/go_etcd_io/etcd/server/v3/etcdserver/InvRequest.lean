/-
The etcd server's request path (`v3_server.go`: a client request proposed through raft, the
proposer waiting for the apply thread's result): the shared vocabulary of the specs of
`EtcdServer.Range`/`Put`/`DeleteRange`/`Txn`, `processInternalRaftRequestOnce`, `doSerialize`,
the wait registry (`pkg/wait`) and the id generator (`pkg/idutil`). Lean-first (no Rocq
counterpart); plan: `notes/decisions.md`, "The request path: raft as a contract, the wait
registry, the checks as the premises' discharge".

**Raft as a contract** (`raftPropose`). The server's raft is etcd's dependency (raft v3.7,
`EtcdDeps/`, names-only), not the verified fork (`Code/go_etcd_io/raft/`, 118 commits earlier,
before the protobuf-go v2 raftpb); the two translations cannot be imported together. So
`raftNode.Propose` (= `raft.Node.Propose`, promoted) gets, as a contract of the server's `Node`
field, the statement the verified `node.Propose` proves for the register
(`Spec/go_etcd_io/raft/v3/node__Propose.lean`, `InvNode.lean`), restated over the server's own
ghost names (`ServerRaftNames`): a first proposal of `data` (`fresh`, with its fresh token)
deposits the client's atomic update `AU <{∃∃ L, srvCLog γ L}> <{srvCLog γ (L ++ [data]),
COMM Q L}>` (`srvPropAu`), which raft fires when the data's first occurrence commits; the call
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

**Reads** (`isRead r γr`): `LinearizableReadNotify(ctx)` (the read-index loop of `read.Read`,
proved in unit 4a, `read/Results.lean`, from contracts on the server and raft) returns `nil` only
once the applied index is at least the committed index the caller knew of (`committedAtLeast γr
c` in, `appliedAtLeast γr ci₀` with `c ≤ ci₀` out); its caller holds a reader slot of the read
loop's lock (`readReader`). Unit 4b ties the two lower bounds to the consistent-index protocol.

**The auth store's request side** (`isReqAuth st`): `AuthInfoFromCtx`/`AuthInfoFromTLS` return
`nil` or an `*AuthInfo` with readable `Username`/`Revision` (`authInfoIs`), and an error.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.Token
public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.FUpd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## Raft's client log, at the server -/

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The ghost names of the server's raft contract (the register's `RaftNames`' client-log
part, restated): the client log (`ghostVar`, halves), the fresh-data tokens and the deposited
proposals (ghost maps keyed by the data), and the committed client data (a mono list, every
occurrence, in commit order). -/
structure ServerRaftNames where
  cLog : GName
  fresh : GName
  props : GName
  committed : GName

/-- The namespace of raft's commit invariant (the register's `raftN`): the deposited updates
are fired with it closed. -/
def srvRaftN : Namespace := nroot .@ "server_raft_commit"

/-- The client's half of the client log `L` (the data of the committed client entries, first
occurrences): `cLog`. -/
def srvCLog (γ : ServerRaftNames) (L : List (List w8)) : IProp GF :=
  ghostVar γ.cLog (1 : Qp).half L

/-- The token for depositing `d` the first time: `propFresh`. -/
def srvPropFresh (γ : ServerRaftNames) (d : List w8) : IProp GF :=
  d ↪[γ.fresh] ()

/-- `d`'s atomic update was deposited (persistent): `deposited`. -/
def srvDeposited (γ : ServerRaftNames) (d : List w8) : IProp GF :=
  iprop(∃ γp : GName × GName, d ↪[γ.props]□ γp)

instance srvDeposited_persistent (γ : ServerRaftNames) (d : List w8) :
    Persistent (srvDeposited (GF := GF) γ d) := by
  unfold srvDeposited; infer_instance

/-- The proposer's handle on its deposited proposal, with result `Q`: `isProp`. -/
def srvIsProp (γ : ServerRaftNames) (d : List w8) (γp : GName × GName)
    (Q : List (List w8) → IProp GF) : IProp GF :=
  iprop(d ↪[γ.props]□ γp ∗ savedPredOwn γp.1 DFrac.discard Q)

/-- The ticket the proposer trades for the result: `propTok`. -/
def srvPropTok (γp : GName × GName) : IProp GF := token γp.2


/-- The proposer's atomic update for `d` (`propAu`): fired by raft at `d`'s first commit. -/
def srvPropAu (γ : ServerRaftNames) (d : List w8) (Q : List (List w8) → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (L : List (List w8)), srvCLog γ L }> @ ⊤ \ ↑srvRaftN, ∅
          <{ srvCLog γ (L ++ [d]), COMM Q L }>)

/-- What `Propose` takes for `d` (`propArg`): a first proposal's fresh token and update, or a
retry's `srvDeposited`. -/
def srvPropArg (γ : ServerRaftNames) (d : List w8) (Q : List (List w8) → IProp GF)
    (fresh : Bool) : IProp GF :=
  if fresh then iprop(srvPropFresh γ d ∗ srvPropAu γ d Q) else srvDeposited γ d

/-- What it gives back (`propRes`): `d` deposited, and a first proposal's handle and ticket. -/
def srvPropRes (γ : ServerRaftNames) (d : List w8) (Q : List (List w8) → IProp GF)
    (fresh : Bool) : IProp GF :=
  iprop(srvDeposited γ d ∗
    if fresh then iprop(∃ γp, srvIsProp γ d γp Q ∗ srvPropTok γp) else iprop(True))

/-! ## The apply side of the contract: what the committed batches hold (pure and ghost) -/

/-- The client data of a batch: the data of its normal entries with data, in order. -/
def batchData (ms : List EntryModel) : List (List w8) :=
  (ms.filter (fun m => decide (m.typ = W32 0 ∧ m.data ≠ []))).map EntryModel.data

/-- The client log after more committed client data: first occurrences only (`firstOcc`). -/
def appendFirstOcc (L : List (List w8)) : List (List w8) → List (List w8)
  | [] => L
  | d :: ds => appendFirstOcc (if d ∈ L then L else L ++ [d]) ds

/-- A lower bound of the committed client data (every occurrence, in commit order). -/
def srvCommittedLb (γ : ServerRaftNames) (cs : List (List w8)) : IProp GF :=
  monoListLbOwn γ.committed cs

instance srvCommittedLb_persistent (γ : ServerRaftNames) (cs : List (List w8)) :
    Persistent (srvCommittedLb (GF := GF) γ cs) := by
  unfold srvCommittedLb; infer_instance

end ghost

/-! ## The wait registry (`pkg/wait`) -/

section wait
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The request path's ghost names: the raft contract's, the ids', and the wait's registered
ids' (`isWait`'s `γw`). -/
structure ReqNames where
  raft : ServerRaftNames
  ids : IdNames
  wait : GName

/-- **The result `ar` of applying `rq`** (persistent if its parts are): a non-nil `*apply.Result`
of applying `rq` (with `v3`) at some KV state `y`, to `y'` (`apply.applyStep`,
`apply.applyResultIs`), with mvcc's certificate of the log after. -/
def resultIs (E : apply.AEnv GF) (rq : apply.IRRModel) (ar : Loc) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out⌝ ∗ apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log)

/-- **The result the proposer of `rq` expects**: the `*apply.Result` `ar` (as an interface
value) with `resultIs E rq ar`. -/
def resultΨ (E : apply.AEnv GF) (rq : apply.IRRModel) (x : GoInterface) : IProp GF :=
  iprop(∃ ar : Loc,
    ⌜x = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar⌝ ∗
    resultIs E rq ar)

/-- **The server's registration condition**: the expectation of a registered id is
`resultΨ E rq` for the request `rq` its data decode to, the id claimed for those data. -/
def reqWaitR (γi : IdNames) (E : apply.AEnv GF) (id : w64) (Ψ : GoInterface → IProp GF) :
    IProp GF :=
  iprop(∃ (d : List w8) (rq : apply.IRRModel), idClaim γi id d ∗
    ⌜apply.irrDecode d = some rq ∧ Ψ = resultΨ E rq⌝)

instance reqWaitR_persistent (γi : IdNames) (E : apply.AEnv GF) (id : w64)
    (Ψ : GoInterface → IProp GF) : Persistent (reqWaitR γi E id Ψ) := by
  unfold reqWaitR; infer_instance

/-- **The server's wait** `s.w` (persistent): a `wait.Wait` (`wait.New`'s contract) with the
server's registration condition, the ids `ρ.ids`, the registered ids' map `ρ.wait`, and some
reader's resource (the apply thread's `srvApplyKV` holds `IsRegistered`'s, as the apply package's
`waitOk`). Replaces the apply package's `waitOk` in `srvFieldsAt` (unit 2). -/
def waitInv (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ RD : IProp GF, isWait w ρ.ids ρ.wait (reqWaitR ρ.ids E) RD)

instance waitInv_persistent (w : GoInterface) (ρ : ReqNames) (E : apply.AEnv GF) :
    Persistent (waitInv (GF := GF) w ρ E) := by
  unfold waitInv; infer_instance

/-- **What the apply thread knows of a committed entry's id** (persistent; the raft contract's
apply side, `batchCommitted`, gives the first half; unit 4): a normal entry's data, if they
decode to a request with an id, were claimed under that id; a conf change's id (`ccIdOf`) is no
KV request's registration (the conf change's proposer claimed it for the conf change: typed
claims, unit 4). -/
def entryWaitOk (ρ : ReqNames) (E : apply.AEnv GF) (m : EntryModel) : IProp GF :=
  if m.typ = W32 0 then
    iprop(∀ (rq : apply.IRRModel) (id : w64),
      ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
        idClaim ρ.ids id m.data)
  else iprop(□ ∀ Ψ, reqWaitR ρ.ids E (ccIdOf m.data) Ψ -∗ False)

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
2026-10-12, unit 3a). -/
def raftPropose (γ : ServerRaftNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (data_sl : GoSlice)
        (data : List w8) (Q : List (List w8) → IProp GF) (fresh : Bool),
      {{ mvcc.txnCtx ctx cd ∗ data_sl ↦*□ data ∗ srvPropArg γ data Q fresh }}
        (App (App (Val #(methods ni.ty go!"Propose" ni.v)) (Val #(GoInterface.ok ctx)))
          (Val #data_sl))
      {{ (err : GoInterface), RET #err; srvPropRes γ data Q fresh ∗ applyErrIs err }}))

instance raftPropose_persistent (γ : ServerRaftNames) (n : GoInterface) :
    Persistent (raftPropose (GF := GF) γ n) := by
  unfold raftPropose; infer_instance

/-- **What a batch of committed entries holds** (the contract's apply side; unit 4 states the
loops with it): after the committed client data `cs` the apply thread has applied, the batch's
client data `batchData ms` are the next committed ones, each deposited and claimed by the id of
the request it decodes to (claims are cluster-wide: the members' id prefixes differ, a premise). -/
def batchCommitted (γ : ServerRaftNames) (γi : IdNames) (cs : List (List w8))
    (ms : List EntryModel) : IProp GF :=
  iprop(srvCommittedLb γ (cs ++ batchData ms) ∗
    [∗list] d ∈ batchData ms, srvDeposited γ d ∗
      ∀ rq id, ⌜apply.irrDecode d = some rq ∧ apply.irrId rq = some id⌝ -∗ idClaim γi id d)

end wait

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-! ## Reads (`read.Read`, names-only until unit 4) -/

section readGhost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Raft's `ReadState` (v3.7) is countable (a channel's element type: the raft wrapper's
`readStateC`, the read loop's `ReadState()`; moved here from `InvRaftNode.lean`, 2026-10-13, for
the read package, which must not import the raft wrapper's invariants). -/
instance readState_countable : Pos.Countable go_etcd_io.raft.v3.ReadState :=
  countableOfLeftInverse (fun r : go_etcd_io.raft.v3.ReadState => (r.Index', r.RequestCtx'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

/-- The read-index ghost names: lower bounds of the applied index and of the committed
index; and (2026-10-13, the request path's unit 4a) the read loop's current notifier, a ghost
variable of the notifier and the name of its need (`read/Inv.lean`), whose halves the read loop's
`RWMutex` and its invariant hold: the lock's resource (`readMuP`) names it, so a caller's reader
slot of the lock (`readReader`) is a predicate of the names; and (2026-10-13, unit 4b) the applied
logs, a ghost map from an applied index to the KV log the apply thread had right after applying
the entry at that index (`appliedLogAt`). -/
structure ReadNames where
  applied : GName
  committed : GName
  notifier : GName
  logs : GName

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

/-- Two logs applied through one index are one. -/
theorem appliedLogAt_agree (γr : ReadNames) (i : w64) (L L' : mvcc.Log) :
    ⊢ appliedLogAt (GF := GF) γr i L -∗ appliedLogAt γr i L' -∗ ⌜L = L'⌝ := by
  iintro H1 H2
  iunfold appliedLogAt at H1 H2
  icombine H1 H2 gives %Hag
  ipureintro
  exact Hag.2

/-- **`LinearizableReadNotify` succeeded**: the applied index has reached an index at least the
committed index `c` the caller knew of. -/
def readIndexOk (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(∃ ci₀ : w64, ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedAtLeast γr ci₀)

instance readIndexOk_persistent (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance

end readGhost

section applied
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The server's atomics' invariants' namespace (moved here from `InvApplier.lean`, 2026-10-13). -/
abbrev srvN : Namespace := nroot.@"server"

/-- **The applied index's invariant** (persistent; the request path's unit 4b, see
`notes/decisions.md`, "The applied index: a certified log per index"): the atomic
`s.appliedIndex` at `v`, half of the authority of the applied index's lower bounds (`γr.applied`:
the apply thread, the only writer, holds the other half, `srvAppliedOwn`) at `v`, the authority of
the applied logs (`γr.logs`), every key at most `v` (so `setAppliedIndex` of a larger index
deposits a fresh one), and the log applied through `v`, with mvcc's certificate. -/
def srvAppliedInv (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  inv srvN iprop(∃ (v : w64) (L : mvcc.Log) (M : GMap w64 mvcc.Log),
    sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v ∗
    monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat v) ∗
    ghostMapAuth γr.logs 1 M ∗ ⌜∀ k L', M.lookup k = some L' → uint.Z k ≤ uint.Z v⌝ ∗
    appliedLogAt γr v L ∗ mvcc.idxCert E.γ.idx L)

instance srvAppliedInv_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAppliedInv s E γr) := by
  unfold srvAppliedInv; infer_instance

/-- **The apply thread's half of the applied index's authority** at `v` (the only writer of
`s.appliedIndex`; `setAppliedIndex` moves it). -/
def srvAppliedOwn (γr : ReadNames) (v : w64) : IProp GF :=
  monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat v)

/-- **The committed index's invariant** (persistent; unit 4b, symmetric to `srvAppliedInv`, no
log): the atomic `s.committedIndex` at `v` and half of the authority of the committed index's
lower bounds (`γr.committed`) at `v`; the writer (`updateCommittedIndex`, the raft loop's ready
handler, unit 4c) holds the other half, `srvCommittedOwn`. -/
def srvCommittedInv (s : Loc) (γr : ReadNames) : IProp GF :=
  inv srvN iprop(∃ v : w64,
    sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) v ∗
    monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v))

instance srvCommittedInv_persistent (s : Loc) (γr : ReadNames) :
    Persistent (srvCommittedInv (GF := GF) s γr) := by
  unfold srvCommittedInv; infer_instance

/-- **The writer's half of the committed index's authority** at `v` (unit 4c's
`updateCommittedIndex`; unused in 4b). -/
def srvCommittedOwn (γr : ReadNames) (v : w64) : IProp GF :=
  monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v)

/-- **The applied and committed indices' invariants, at some names** (persistent): the proposer's
view (`srvReqFieldsAt`: it reads both indices only for the request limit's gap, so it needs no
particular names). -/
def srvIndexInvs (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γr : ReadNames, srvAppliedInv s E γr ∗ srvCommittedInv s γr)

instance srvIndexInvs_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvIndexInvs (GF := GF) s E) := by
  unfold srvIndexInvs; infer_instance

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
  icases Hi with ⟨%v, %L, %M, Hat, >Hauth, >HM, >%HMk, >#HL, >#Hc⟩
  iunfold appliedAtLeast at Hlb
  ihave %Hle := monoNatLbOwn_valid γr.applied _ _ _ $$ Hauth Hlb
  imod Hclose $$ [Hat Hauth HM] with -
  · inext; iexists v, L, M; iframe Hat Hauth HM HL Hc; ipureintro; exact HMk
  imodintro
  iexists v, L
  iframe HL Hc
  ipureintro
  have h2 := Hle.2
  word

end applied

section readAddrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the read loop's current notifier (`r.notifier`). -/
abbrev readNotifierAddr (r : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"notifier" r
/-- The address of the read loop's lock (`r.mux`). -/
abbrev readMuAddr (r : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"mux" r

end readAddrs

section read
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The read loop's lock resource** at fraction `q` (`r.mux`, a `sync.RWMutex`; 2026-10-13, the
request path's unit 4a): `r.notifier` (at `q`) and the ghost variable of the current notifier and
its need's name (at `q / 2`; the read invariant holds the other half, `read/Inv.lean`). A reader
(`LinearizableReadNotify`) learns which notifier is current; the writer (the loop) swaps it. -/
def readMuP (r : Loc) (γr : ReadNames) (q : Qp) : IProp GF :=
  iprop(∃ (nc : Loc) (γn : GName), (readNotifierAddr r ↦{DFrac.own q} nc : IProp GF) ∗
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
`raftPropose`). -/
def isRead (r : Loc) (γr : ReadNames) : IProp GF :=
  iprop(□ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (c : w64),
    {{ mvcc.txnCtx ctx cd ∗ committedAtLeast γr c ∗ readReader r γr }}
      (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
        go!"LinearizableReadNotify")) (Val #(GoInterface.ok ctx)))
    {{ (err : GoInterface), RET #err; readReader r γr ∗ applyErrIs err ∗
        (⌜err = GoInterface.nil⌝ -∗ readIndexOk γr c) }}))

instance isRead_persistent (r : Loc) (γr : ReadNames) : Persistent (isRead (GF := GF) r γr) := by
  unfold isRead; infer_instance

/-- The `*auth.AuthInfo` `a` (not nil): its `Username` and `Revision`, read-only. -/
def authInfoIs (a : Loc) (user : GoString) (rev : w64) : IProp GF :=
  iprop(⌜a ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.auth.AuthInfo go!"Username" a ↦□ user ∗
    structFieldRef go_etcd_io.etcd.server.v3.auth.AuthInfo go!"Revision" a ↦□ rev)

/-- An auth info returned by the auth store: `nil`, or one with its fields. -/
def authInfoOpt (a : Loc) : IProp GF :=
  iprop(⌜a = null⌝ ∨ ∃ user rev, authInfoIs a user rev)

/-- **The auth store's request side** (persistent; trust boundary: `auth` is names-only):
`AuthInfoFromCtx(ctx)` returns an auth info (or `nil`) and an error (`nil`, or one the gRPC layer
can take: `applyErrIs`; 2026-10-12, unit 3a); `AuthInfoFromTLS(ctx)` an auth info (or `nil`). The permission checks and `Revision` are the apply package's
`isAuthStore`. -/
def isReqAuth (st : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd }}
        (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); authInfoOpt a ∗ applyErrIs err }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd }}
        (App (Val #(methods ai.ty go!"AuthInfoFromTLS" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc), RET #a; authInfoOpt a }}))

instance isReqAuth_persistent (st : GoInterface) : Persistent (isReqAuth (GF := GF) st) := by
  unfold isReqAuth; infer_instance

/-- **`RaftKV`'s value is the server** (the `kv` field of `v3rpc.kvServer`: `NewKVServer(s)`
stores `s`): its methods are `*EtcdServer`'s. -/
def isRaftKV (kv : GoInterface) (s : Loc) : Prop :=
  kv = interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s

end read

end EtcdGrove
end Perennial
