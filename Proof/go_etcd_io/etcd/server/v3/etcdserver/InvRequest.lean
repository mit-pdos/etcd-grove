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

**Unique ids** (`idGen`, `idFresh`, `idClaim`): `idutil.Generator.Next` returns `prefix |
lowbit(suffix, 48)` for an atomically incremented `suffix`: `2 ^ 48` consecutive calls return
distinct ids. `idGen γi g` hands out `2 ^ 48 - 1` credits (`idCred`), `Next` consumes one and
returns an id nobody holds (`idFresh γi id`: the right to claim the id for a request's data,
`idClaim γi id d` (persistent, agreeing), and the id's slot in the wait registry, `idSlot`).
The ids of other members' requests (other generators, other prefixes) are claimed in the same
map: that the members' prefixes (`uint16(memberID)`) differ is a premise of the raft contract's
apply side (`issues/etcd-request-id-member-prefix.md`).

**The wait registry** (`isWait w γi R`, the contract `wait.list`'s proof establishes, unit 2):
`Register(id)` with the id's slot and an expectation `Ψ` satisfying the registration condition
`R id Ψ` (persistent) returns a channel the proposer receives `Ψ`'s value from (`waitRecv`: a
handoff channel, buffer 1, sent once then closed, `cache/v3/Handoff.lean`); `Trigger(id, x)`
needs `Ψ x` for every `Ψ` registered under `id` by `R` (`waitTrig`), or, from the proposer
giving up (`x = nil`), its consumer token; `IsRegistered(id)` returns a boolean. The server's
condition (`reqWaitR`): `Ψ` is `resultΨ E rq` for the request `rq` the id was claimed for
(`idClaim γi id d`, `irrDecode d = some rq`). So the apply thread, applying an entry whose data
`d'` decode to a request with id `id`, learns from `idClaim` (the entry's, from the raft
contract, and the registration's) that `d' = d`, and proves `resultΨ E rq` of its result.

**The result a proposer expects** (`resultΨ E rq x`): `x` is the `*apply.Result` of applying
`rq` (with `v3`) at some KV state `y`, to `y'` (`apply.applyStep`, `apply.applyResultIs`), with
mvcc's certificate of the log after (`idxCert`).

**Reads** (`isRead r γr`): `LinearizableReadNotify(ctx)` (the read-index loop of `read.Read`,
names-only until unit 4) returns `nil` only once the applied index is at least the committed
index the caller knew of (`committedAtLeast γr c` in, `appliedAtLeast γr ci₀` with `c ≤ ci₀`
out): unit 4 ties the two lower bounds to the consistent-index protocol and to raft's
`ReadIndex`/`ReadState` contracts.

**The auth store's request side** (`isReqAuth st`): `AuthInfoFromCtx`/`AuthInfoFromTLS` return
`nil` or an `*AuthInfo` with readable `Username`/`Revision` (`authInfoIs`), and an error.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.cache.v3.Handoff
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

/-! ## Unique ids (`pkg/idutil`) -/

/-- The id generator's ghost names: the credits (`Auth Nat`), and two ghost maps keyed by id:
the data an id was claimed for (`none` until claimed), and the id's wait slot. -/
structure IdNames where
  cred : GName
  issued : GName
  slot : GName

/-- `n` id credits (one per `Next`). -/
def idCred (γi : IdNames) (n : Nat) : IProp GF := own γi.cred (◯ n : Auth Nat)

/-- The right to claim the id `id` for a request's data. -/
def idUnclaimed (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.issued] (none : Option (List w8))

/-- The id `id` was claimed for the data `d` (persistent; agreeing). -/
def idClaim (γi : IdNames) (id : w64) (d : List w8) : IProp GF :=
  id ↪[γi.issued]□ (some d)

instance idClaim_persistent (γi : IdNames) (id : w64) (d : List w8) :
    Persistent (idClaim (GF := GF) γi id d) := by
  unfold idClaim; infer_instance

/-- The id's slot in the wait registry (exclusive): `Register(id)` takes it. -/
def idSlot (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.slot] ()

/-- **An id nobody holds** (what `Next` returns): its claim and its wait slot. -/
def idFresh (γi : IdNames) (id : w64) : IProp GF :=
  iprop(idUnclaimed γi id ∗ idSlot γi id)

/-- `id` is among the first `k` ids of the generator with prefix `pfx` and initial suffix
`s0`: `pfx | lowbit(s0 + j, 48)` for `1 ≤ j ≤ k`. -/
def idIssued (pfx s0 : w64) (k : Nat) (id : w64) : Prop :=
  ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ id = pfx ||| ((s0 + W64 (j : Int)) &&& W64 (2 ^ 48 - 1))

def idN : Namespace := nroot .@ "idutil"

/-- **The generator `g`** (persistent): its `prefix` field fixed, its `suffix` an atomic in an
invariant with the credits' authority (`2 ^ 48 - 1` less the `k` ids issued) and the issued
ids' ghost maps (the ids issued, `idIssued`, and only those, are in both maps). `NewGenerator`
establishes it with `idCred γi (2 ^ 48 - 1)`; `Next` consumes a credit and returns an
`idFresh` id (unit 2). The bound is the premise that a process issues fewer than `2 ^ 48`
request ids (the 48-bit suffix wraps after `2 ^ 48`). -/
def idGen (γi : IdNames) (g : Loc) : IProp GF :=
  iprop(∃ (pfx s0 : w64), ⌜g ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ pfx ∗
    ⌜uint.Z s0 < 2 ^ 48⌝ ∗
    inv idN iprop(∃ (k : Nat) (I : GMap w64 (Option (List w8))) (S : GMap w64 Unit),
      sync.atomic.ownUint64
        (structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" g) (DFrac.own 1)
        (s0 + W64 (k : Int)) ∗
      own γi.cred (● (2 ^ 48 - 1 - k) : Auth Nat) ∗ ⌜k ≤ 2 ^ 48 - 1⌝ ∗
      ghostMapAuth γi.issued 1 I ∗ ghostMapAuth γi.slot 1 S ∗
      ⌜∀ id, ((I !! id).isSome ↔ idIssued pfx s0 k id) ∧ ((S !! id).isSome ↔ idIssued pfx s0 k id)⌝))

instance idGen_persistent (γi : IdNames) (g : Loc) : Persistent (idGen (GF := GF) γi g) := by
  unfold idGen; infer_instance

end ghost

/-! ## The wait registry (`pkg/wait`) -/

section wait
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What the registered channel carries: the expectation's value, or `nil` from the proposer
giving up (`Trigger(id, nil)`, with its consumer token, which it then no longer has). -/
def waitVal (γh : HandoffNames) (Ψ : GoInterface → IProp GF) (x : GoInterface) : IProp GF :=
  iprop(Ψ x ∨ (⌜x = GoInterface.nil⌝ ∗ handoffConsumer γh false))

/-- **The proposer's receive right** on the channel `ch` `Register(id)` returned, for `Ψ`: a
handoff channel of `waitVal`, and its consumer token (nothing taken yet). -/
def waitRecv (γh : HandoffNames) (ch : Loc) (Ψ : GoInterface → IProp GF) : IProp GF :=
  iprop(isHandoff (V := GoInterface) γh ch (waitVal γh Ψ) iprop(True) iprop(True) ∗
    handoffConsumer γh false)

/-- **What `Trigger(id, x)` takes from anyone but the proposer**: `Ψ x` for every expectation
registered under `id` (by the registration condition `R`). Trivial if nothing is registered
(another member's request, or a registration already triggered: then nothing is sent). -/
def waitTrig (R : w64 → (GoInterface → IProp GF) → IProp GF) (id : w64) (x : GoInterface) :
    IProp GF :=
  iprop(∀ Ψ, R id Ψ -∗ Ψ x)

/-- **The `wait.Wait` `w`** (persistent: the contract `wait.list`'s methods meet, unit 2),
with the registration condition `R` (persistent). -/
def isWait (w : GoInterface) (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF) :
    IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜w = GoInterface.ok wi⌝ ∗
    □ (∀ (id : w64) (Ψ : GoInterface → IProp GF),
      {{ idSlot γi id ∗ □ R id Ψ }}
        (App (Val #(methods wi.ty go!"Register" wi.v)) (Val #id))
      {{ (ch : Loc), RET #ch; ∃ γh, waitRecv γh ch Ψ }}) ∗
    □ (∀ (id : w64) (x : GoInterface),
      {{ (∃ γh, ⌜x = GoInterface.nil⌝ ∗ handoffConsumer γh false) ∨ waitTrig R id x }}
        (App (App (Val #(methods wi.ty go!"Trigger" wi.v)) (Val #id)) (Val #x))
      {{ RET #(); True }}) ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods wi.ty go!"IsRegistered" wi.v)) (Val #id))
      {{ (b : Bool), RET #b; True }}))

instance isWait_persistent (w : GoInterface) (γi : IdNames)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) : Persistent (isWait (GF := GF) w γi R) := by
  unfold isWait; infer_instance

/-- **The result the proposer of `rq` expects** (persistent): the `*apply.Result` of applying
`rq` with `v3` at some KV state `y`, to `y'`, with mvcc's certificate of the log after. -/
def resultΨ (E : apply.AEnv GF) (rq : apply.IRRModel) (x : GoInterface) : IProp GF :=
  iprop(∃ ar : Loc,
    ⌜x = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar ∧
      ar ≠ null⌝ ∗
    ∃ (y y' : apply.ApplyKV) (out : apply.ApplyOut),
      ⌜apply.applyStep rq true y y' out⌝ ∗ apply.applyResultIs rq true y.log ar out ∗
      mvcc.idxCert E.γ.idx y'.log)

/-- **The server's registration condition**: the expectation of a registered id is
`resultΨ E rq` for the request `rq` its data decode to, the id claimed for those data. -/
def reqWaitR (γi : IdNames) (E : apply.AEnv GF) (id : w64) (Ψ : GoInterface → IProp GF) :
    IProp GF :=
  iprop(∃ (d : List w8) (rq : apply.IRRModel), idClaim γi id d ∗
    ⌜apply.irrDecode d = some rq ∧ Ψ = resultΨ E rq⌝)

instance reqWaitR_persistent (γi : IdNames) (E : apply.AEnv GF) (id : w64)
    (Ψ : GoInterface → IProp GF) : Persistent (reqWaitR γi E id Ψ) := by
  unfold reqWaitR; infer_instance

/-- **The server's wait** `s.w` (persistent): a `wait.Wait` with the server's registration
condition. Unit 2 replaces the apply package's `waitOk` (which `srvFieldsAt` still states) with
it. -/
def waitInv (w : GoInterface) (γi : IdNames) (E : apply.AEnv GF) : IProp GF :=
  isWait w γi (reqWaitR γi E)

/-! ## The raft contract -/

/-- **The server's raft node `n`** (persistent; the `Node` field of the server's `raftNode`):
its `Propose(ctx, data)`, from any goroutine, at any context, with `data`'s slice read-only, is
the verified `node.Propose`'s statement over the server's ghost names (see the file header). -/
def raftPropose (γ : ServerRaftNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (data_sl : GoSlice)
        (data : List w8) (Q : List (List w8) → IProp GF) (fresh : Bool),
      {{ mvcc.txnCtx ctx cd ∗ data_sl ↦*□ data ∗ srvPropArg γ data Q fresh }}
        (App (App (Val #(methods ni.ty go!"Propose" ni.v)) (Val #(GoInterface.ok ctx)))
          (Val #data_sl))
      {{ (err : GoInterface), RET #err; srvPropRes γ data Q fresh }}))

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

/-- The read-index ghost names: lower bounds of the applied index and of the committed
index. -/
structure ReadNames where
  applied : GName
  committed : GName

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

/-- **`LinearizableReadNotify` succeeded**: the applied index has reached an index at least the
committed index `c` the caller knew of. -/
def readIndexOk (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(∃ ci₀ : w64, ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedAtLeast γr ci₀)

end readGhost

section read
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*read.Read` `r`** (persistent; the contract until unit 4 proves `read/read.go`):
`LinearizableReadNotify(ctx)` returns `nil` only once the applied index has reached the
committed index the caller knew of (`readIndexOk`), or an error. -/
def isRead (r : Loc) (γr : ReadNames) : IProp GF :=
  iprop(□ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (c : w64),
    {{ mvcc.txnCtx ctx cd ∗ committedAtLeast γr c }}
      (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
        go!"LinearizableReadNotify")) (Val #(GoInterface.ok ctx)))
    {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ -∗ readIndexOk γr c }}))

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
`AuthInfoFromCtx(ctx)` returns an auth info (or `nil`) and an error; `AuthInfoFromTLS(ctx)` an
auth info (or `nil`). The permission checks and `Revision` are the apply package's
`isAuthStore`. -/
def isReqAuth (st : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd }}
        (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); authInfoOpt a }}) ∗
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
