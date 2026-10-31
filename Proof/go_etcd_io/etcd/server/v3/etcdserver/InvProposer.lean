/-
The request path's proposer side (`v3_server.go`'s `processInternalRaftRequestOnce`, `raftRequest`,
`Put`, `DeleteRange`, the writing `Txn`): the shared vocabulary of their specs. Lean-first (no
Rocq counterpart); the request path's unit 2 (2026-10-12); plan: `notes/decisions.md`, "The
request path".

**The request** (pure): the requests the server builds (`irrPut`, `irrDeleteRange`, `irrTxn`:
one field set, no id, no header), the request limit (`exceedsLimit`, `util.go`'s
`exceedsRequestLimit`: wrapping `uint64` sums, as the code), the request's metric label
(`reqTypeName`, `getRequestType`'s switch).

**In the heap**: the request before its header is set (`irrNoHdrIs`: every field but `Header`
read-only, as `apply.internalRaftRequestIs`; the proposer owns `Header` and writes it).

**The server, as a proposer sees it** (`isServerReq s E ρ`, persistent): the fields the request
path reads (the id generator `idGen`, the wait `waitInv`, the raft node `srvRaftNode`, the
configuration's `MaxRequestBytes`, feature gate, `ClientCertAuthEnabled`, election ticks, tick
length, the auth store's request side `isReqAuth`, the `done` channel, the member id, the
leader's atomic, the cluster and the transport, the applied and committed indices' invariants at
some read names, `srvIndexInvs`: 2026-10-13, unit 4b), and two
invariants of the request path's ghost state: the **mint** (`srvMintInv`: the authority of raft's
fresh-data tokens; every token is of data that decode to a request claimed under its id, so a
proposer that claims a fresh id for its data mints the data's token: `srv_claim_mint`; and, since
2026-10-16, stage R7b, the read contexts' mint `srvRdFreshInv`: the read loop's request ids mint
raft's fresh read-context tokens and read credits, `srvRdFresh_mint`), and (2026-10-14,
unit T1) the **KV invariant** (`kvInv ρ.raft ρ.kv`: the server's half of raft's committed log with
the KV ghost state; a proposal's update is built from it, `kv_prop_au`; until then the client
log's other half, `srvCLogInv`, and a trivial update).

**The proposer's own resources**: a reader slot of `s.leadTimeMu` (`srvLeadTimeReader`:
`parseProposeCtxErr` read-locks it, Perennial's `RWMutex` admits a bounded number of readers,
so each request goroutine holds a token) and one id credit (`idCred ρ.ids 1`: the premise that a
process serves fewer than `2 ^ 48` requests).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.features.Defs
public import Spec.google_golang_org.protobuf.proto.MarshalIRR
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-! ## The request, purely -/

/-- The request with nothing set (`&pb.InternalRaftRequest{}`). -/
def apply.irrEmpty : apply.IRRModel where
  id := W64 0
  header := none
  range := none
  put := none
  deleteRange := none
  txnW := none
  compaction := none
  leaseGrant := none
  leaseRevoke := none
  alarm := none
  leaseCheckpoint := none
  authEnable := false
  authDisable := false
  authStatus := false
  authenticate := none
  authUserAdd := none
  authUserDelete := false
  authUserGet := none
  authUserChangePassword := false
  authUserGrantRole := none
  authUserRevokeRole := false
  authUserList := false
  authRoleList := false
  authRoleAdd := none
  authRoleDelete := false
  authRoleGet := none
  authRoleGrantPermission := none
  authRoleRevokePermission := false
  clusterVersionSet := none
  clusterMemberAttrSet := none
  downgradeInfoSet := none
  downgradeVersionTest := false

/-- `&pb.InternalRaftRequest{Put: r}` for `r` holding `op`. -/
def irrPut (op : OpFull) : apply.IRRModel := { apply.irrEmpty with put := some op }
/-- `&pb.InternalRaftRequest{DeleteRange: r}`. -/
def irrDeleteRange (op : OpFull) : apply.IRRModel :=
  { apply.irrEmpty with deleteRange := some op }
/-- `&pb.InternalRaftRequest{Txn: r}` for `r` holding the wire transaction `tw` (E3e: its model
`tw.toModel` until then). -/
def irrTxn (tw : txn.TxnModelW) : apply.IRRModel := { apply.irrEmpty with txnW := some tw }

@[simp] theorem irrTxn_txn (tw : txn.TxnModelW) : (irrTxn tw).txn = some tw.toModel := rfl
@[simp] theorem irrTxn_txnW (tw : txn.TxnModelW) : (irrTxn tw).txnW = some tw := rfl
@[simp] theorem irrEmpty_txn : apply.irrEmpty.txn = none := rfl

/-- **`exceedsRequestLimit(ai, ci, r, enable)`** (`util.go`), `prio` = `isPriorityRequest(r)`
(a lease revocation): the committed index more than `maxNormalGap` (5000) past the applied one,
unless a priority request with the feature enabled is within `maxPriorityGap` (10000); the sums
in `uint64`, wrapping, as the code. -/
def exceedsLimit (ai ci : w64) (prio enable : Bool) : Bool :=
  if uint.Z ci ≤ uint.Z (ai + W64 5000) then false
  else if enable && prio && decide (uint.Z ci ≤ uint.Z (ai + W64 10000)) then false
  else true

/-- **`getRequestType(r)`**: the metric label, the first set field in the switch's order. -/
def reqTypeName (rq : apply.IRRModel) : GoString :=
  if rq.range.isSome then go!"Range"
  else if rq.put.isSome then go!"Put"
  else if rq.deleteRange.isSome then go!"DeleteRange"
  else if rq.txn.isSome then go!"Txn"
  else if rq.compaction.isSome then go!"Compaction"
  else if rq.leaseGrant.isSome then go!"LeaseGrant"
  else if rq.leaseRevoke.isSome then go!"LeaseRevoke"
  else if rq.leaseCheckpoint.isSome then go!"LeaseCheckpoint"
  else if rq.alarm.isSome then go!"Alarm"
  else if rq.authenticate.isSome then go!"Authenticate"
  else if rq.authEnable then go!"AuthEnable"
  else if rq.authDisable then go!"AuthDisable"
  else if rq.authStatus then go!"AuthStatus"
  else if rq.authUserAdd.isSome then go!"AuthUserAdd"
  else if rq.authUserDelete then go!"AuthUserDelete"
  else if rq.authUserChangePassword then go!"AuthUserChangePassword"
  else if rq.authUserGrantRole.isSome then go!"AuthUserGrantRole"
  else if rq.authUserGet.isSome then go!"AuthUserGet"
  else if rq.authUserRevokeRole then go!"AuthUserRevokeRole"
  else if rq.authRoleAdd.isSome then go!"AuthRoleAdd"
  else if rq.authRoleGrantPermission.isSome then go!"AuthRoleGrantPermission"
  else if rq.authRoleGet.isSome then go!"AuthRoleGet"
  else if rq.authRoleRevokePermission then go!"AuthRoleRevokePermission"
  else if rq.authRoleDelete then go!"AuthRoleDelete"
  else if rq.authUserList then go!"AuthUserList"
  else if rq.authRoleList then go!"AuthRoleList"
  else if rq.clusterVersionSet.isSome then go!"ClusterVersionSet"
  else if rq.clusterMemberAttrSet.isSome then go!"ClusterMemberAttrSet"
  else if rq.downgradeInfoSet.isSome then go!"DowngradeInfoSet"
  else if rq.downgradeVersionTest then go!"DowngradeVersionTest"
  else go!"Unknown"

/-- `int64` is not an interface type (Perennial states `NotInterface` of the type constructors,
not of the predeclared named types): so a method of a named integer type (`time.Duration`'s
`Seconds`) resolves on a value receiver. -/
instance notInterface_int64 : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩

/-- Namespaces of the request path's invariants (disjoint from raft's commit, `srvRaftN`). -/
def srvMintN : Namespace := nroot .@ "server_mint"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-! ## The request in the heap -/

/-- **The `*pb.InternalRaftRequest` `p` holds `rq` but for its `Header`** (persistent): every
field but `Header` read-only, as `apply.internalRaftRequestIs`. -/
def irrNoHdrIs (p : Loc) (rq : apply.IRRModel) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    structFieldRef etcdserverpb.InternalRaftRequest go!"ID" p ↦□ rq.id ∗
    apply.irrField p go!"Range" (fun l => apply.optReqIs l rq.range txn.rangeRequestIs) ∗
    apply.irrField p go!"Put" (fun l => apply.optReqIs l rq.put txn.putRequestIs) ∗
    apply.irrField p go!"DeleteRange" (fun l => apply.optReqIs l rq.deleteRange txn.deleteRangeRequestIs) ∗
    apply.irrField p go!"Txn" (fun l => apply.optReqIs l rq.txnW txn.txnRequestIsW) ∗
    apply.irrField p go!"Compaction" (fun l => apply.optReqIs l rq.compaction apply.compactionIs) ∗
    apply.irrField p go!"LeaseGrant" (fun l => apply.optReqIs l rq.leaseGrant apply.leaseGrantIs) ∗
    apply.irrField p go!"LeaseRevoke" (fun l => apply.optReqIs l rq.leaseRevoke apply.leaseRevokeIs) ∗
    apply.irrField p go!"Alarm" (fun l => apply.optReqIs l rq.alarm apply.alarmRequestIs) ∗
    apply.irrField p go!"LeaseCheckpoint" (fun l => apply.optReqIs l rq.leaseCheckpoint apply.leaseCheckpointIs) ∗
    apply.irrField p go!"AuthEnable" (fun l => apply.presentIs l rq.authEnable) ∗
    apply.irrField p go!"AuthDisable" (fun l => apply.presentIs l rq.authDisable) ∗
    apply.irrField p go!"AuthStatus" (fun l => apply.presentIs l rq.authStatus) ∗
    apply.irrField p go!"Authenticate" (fun l => apply.optReqIs l rq.authenticate apply.authenticateIs) ∗
    apply.irrField p go!"AuthUserAdd" (fun l => apply.optReqIs l rq.authUserAdd apply.authUserAddIs) ∗
    apply.irrField p go!"AuthUserDelete" (fun l => apply.presentIs l rq.authUserDelete) ∗
    apply.irrField p go!"AuthUserGet" (fun l => apply.optReqIs l rq.authUserGet apply.authUserGetIs) ∗
    apply.irrField p go!"AuthUserChangePassword" (fun l => apply.presentIs l rq.authUserChangePassword) ∗
    apply.irrField p go!"AuthUserGrantRole"
      (fun l => apply.optReqIs l rq.authUserGrantRole apply.authUserGrantRoleIs) ∗
    apply.irrField p go!"AuthUserRevokeRole" (fun l => apply.presentIs l rq.authUserRevokeRole) ∗
    apply.irrField p go!"AuthUserList" (fun l => apply.presentIs l rq.authUserList) ∗
    apply.irrField p go!"AuthRoleList" (fun l => apply.presentIs l rq.authRoleList) ∗
    apply.irrField p go!"AuthRoleAdd" (fun l => apply.optReqIs l rq.authRoleAdd apply.authRoleAddIs) ∗
    apply.irrField p go!"AuthRoleDelete" (fun l => apply.presentIs l rq.authRoleDelete) ∗
    apply.irrField p go!"AuthRoleGet" (fun l => apply.optReqIs l rq.authRoleGet apply.authRoleGetIs) ∗
    apply.irrField p go!"AuthRoleGrantPermission"
      (fun l => apply.optReqIs l rq.authRoleGrantPermission apply.authRoleGrantPermissionIs) ∗
    apply.irrField p go!"AuthRoleRevokePermission" (fun l => apply.presentIs l rq.authRoleRevokePermission) ∗
    apply.irrField p go!"ClusterVersionSet" (fun l => apply.optReqIs l rq.clusterVersionSet apply.clusterVersionSetIs) ∗
    apply.irrField p go!"ClusterMemberAttrSet"
      (fun l => apply.optReqIs l rq.clusterMemberAttrSet apply.memberAttrSetIs) ∗
    apply.irrField p go!"DowngradeInfoSet" (fun l => apply.optReqIs l rq.downgradeInfoSet apply.downgradeInfoSetIs) ∗
    apply.irrField p go!"DowngradeVersionTest" (fun l => apply.presentIs l rq.downgradeVersionTest))

instance irrNoHdrIs_persistent (p : Loc) (rq : apply.IRRModel) :
    Persistent (irrNoHdrIs (GF := GF) p rq) := by
  unfold irrNoHdrIs apply.compactionIs apply.leaseGrantIs apply.leaseRevokeIs
    apply.alarmRequestIs apply.leaseCheckpointIs apply.checkpointIs apply.authenticateIs
    apply.authUserGetIs apply.authRoleGetIs apply.authUserAddIs apply.authRoleAddIs
    apply.clusterVersionSetIs apply.memberAttrSetIs
    apply.downgradeInfoSetIs
  infer_instance


/-- **A put's permission is its proposal's** (2026-10-14, unit T1; 2026-10-15, unit T2: the
whole state; 2026-10-19, D21 M6: its update fired at most once, its result left at the token
`γc`). -/
theorem putPermit_reqPropOk (γk : KVNames) (op : OpFull) (Q : KVState → IProp GF) (γc : GName) :
    putPermit (GF := GF) γk op Q ⊢
      reqPropOk γk (irrPut op) (fun L => kvRes γc Q (kvStateOf (kvModel γk L))) := by
  unfold putPermit reqPropOk
  iintro ⟨%Hl, Hau⟩
  iright; iright
  iexists .put op, Q, γc
  iframe Hau
  ipureintro
  have hk : apply.dispatchKind (irrPut op) = .put := by
    simp [apply.dispatchKind, irrPut, apply.irrEmpty]
  have hpl : plainCover (irrPut op) := by
    unfold plainCover
    rw [hk]
    refine ⟨by simp [apply.noSideEffect, irrPut, apply.irrEmpty],
      by simp [apply.needAdminPermission, irrPut, apply.irrEmpty], ?_⟩
    intro op' hop'
    simp only [irrPut, Option.some.injEq] at hop'
    subst hop'
    exact Hl
  refine ⟨⟨hpl, putgetKind_kv _ (by simp only [hk]; simp)⟩, ?_, ?_,
    rqShape_of_plain _ hpl (by rw [hk]; decide), rfl⟩
  · unfold reqKVOp; rw [hk]; rfl
  · refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [irrPut, apply.irrEmpty] at h

/-- **A delete's permission is its proposal's** (2026-10-15, unit T2). -/
theorem deletePermit_reqPropOk (γk : KVNames) (op : OpFull) (Q : KVState → IProp GF)
    (γc : GName) :
    deletePermit (GF := GF) γk op Q ⊢
      reqPropOk γk (irrDeleteRange op) (fun L => kvRes γc Q (kvStateOf (kvModel γk L))) := by
  unfold deletePermit reqPropOk
  iintro ⟨%Hz, Hau⟩
  iright; iright
  iexists .deleteRange op, Q, γc
  iframe Hau
  ipureintro
  have hk : apply.dispatchKind (irrDeleteRange op) = .deleteRange := by
    simp [apply.dispatchKind, irrDeleteRange, apply.irrEmpty]
  have hpl : plainCover (irrDeleteRange op) := by
    unfold plainCover
    rw [hk]
    exact ⟨by simp [apply.noSideEffect, irrDeleteRange, apply.irrEmpty],
      by simp [apply.needAdminPermission, irrDeleteRange, apply.irrEmpty]⟩
  refine ⟨⟨hpl, putgetKind_kv _ (by simp only [hk]; simp)⟩, ?_, ?_,
    rqShape_of_plain _ hpl (by rw [hk]; decide), rfl⟩
  · unfold reqKVOp; rw [hk]; rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h
    · intro o h; simp only [irrDeleteRange, Option.some.injEq] at h; subst h; exact Hz
    · intro _ h; simp [irrDeleteRange, apply.irrEmpty] at h

/-- **A writing transaction's permission is its proposal's** (2026-10-15, unit T2). -/
theorem txnPermit_reqPropOk (γk : KVNames) (tw : txn.TxnModelW) (Q : KVState → IProp GF)
    (γc : GName) :
    txnPermit (GF := GF) γk tw.toModel Q ⊢
      reqPropOk γk (irrTxn tw) (fun L => kvRes γc Q (kvStateOf (kvModel γk L))) := by
  unfold txnPermit reqPropOk
  iintro ⟨%Ht, Hau⟩
  iright; iright
  iexists .txn tw.toModel, Q, γc
  iframe Hau
  ipureintro
  have hk : apply.dispatchKind (irrTxn tw) = .txn := by
    simp [apply.dispatchKind, irrTxn, apply.irrEmpty]
  have hpl : plainCover (irrTxn tw) := by
    unfold plainCover
    rw [hk]
    refine ⟨by simp [apply.noSideEffect, irrTxn, apply.irrEmpty],
      by simp [apply.needAdminPermission, irrTxn, apply.irrEmpty], ?_⟩
    intro t' h; simp only [irrTxn_txn, Option.some.injEq] at h; subst h; exact Ht.1
  refine ⟨⟨hpl, putgetKind_kv _ (by simp only [hk]; simp)⟩, ?_, ?_,
    rqShape_of_txn _ hpl hk ?_, rfl⟩
  · unfold reqKVOp; rw [hk]; rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro _ h; simp [irrTxn, apply.irrEmpty] at h
    · intro _ h; simp [irrTxn, apply.irrEmpty] at h
    · intro t' h; simp only [irrTxn_txn, Option.some.injEq] at h; subst h; exact Ht.2.1
  · intro t' h; simp only [irrTxn_txn, Option.some.injEq] at h; subst h; exact Ht.2.2

end defs

/-! ## The server, as a proposer sees it -/

section typeRepr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

instance (priority := high) raftNode_typeRepr_u : TypeRepr raftNode.underlying raftNode :=
  go.type_repr_underlying (u := raftNode.underlying)
instance (priority := high) raftNodeConfig_typeRepr_u :
    TypeRepr raftNodeConfig.underlying raftNodeConfig :=
  go.type_repr_underlying (u := raftNodeConfig.underlying)

end typeRepr

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The configuration's fields the request path reads. -/
abbrev srvCfgFieldAddr (s : Loc) (f : GoString) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig f
    (structFieldRef EtcdServer go!"Cfg" s)

end addrs

section srv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The proposals' mint** (persistent; the cluster's since stage M4, 2026-10-19, allocated once,
`srvPropMint_alloc`): the authority of raft's fresh-data tokens `F`, each token's data decoding to a
request claimed under its id (in the cluster's claims, D21e (A): every member's proposals mint
here). -/
def srvPropMint (γ : ServerRaftNames) (γi : IdNames) : IProp GF :=
  inv srvMintN iprop(∃ F : GMap (List w8) Unit, ghostMapAuth γ.raft.fresh 1 F ∗
    [∗map] d ↦ _u ∈ F, ∃ (rq : apply.IRRModel) (id : w64),
      ⌜apply.irrDecode d = some rq ∧ apply.irrId rq = some id⌝ ∗ ∃ γf : GName, idClaim γi id d γf)

instance srvPropMint_persistent (γ : ServerRaftNames) (γi : IdNames) :
    Persistent (srvPropMint (GF := GF) γ γi) := by
  unfold srvPropMint; infer_instance

/-- **The mint** (see the file header): the authority of raft's fresh-data tokens `F`, each
token's data decoding to a request claimed under its id; and (2026-10-16, stage R7b) the read
contexts' mint (`srvRdFreshInv`, `InvRequest.lean`: the authority of raft's fresh read-context
tokens and its read credits, both minted from the request ids the read loop takes). -/
def srvMintInv (ρ : ReqNames) : IProp GF :=
  iprop(srvPropMint ρ.raft ρ.ids ∗ srvRdFreshInv ρ.raft ρ.ids)

instance srvMintInv_persistent (ρ : ReqNames) : Persistent (srvMintInv (GF := GF) ρ) := by
  unfold srvMintInv; infer_instance


/-- The server's `done` channel (closed when it stops; receiving gives nothing). -/
def srvDoneChan (ch : GoChan) : IProp GF :=
  iprop(∃ γ : ChanNames, ownBroadcastChan ch γ iprop(True) .Unknown)

instance srvDoneChan_persistent (ch : GoChan) : Persistent (srvDoneChan (GF := GF) ch) := by
  unfold srvDoneChan; infer_instance

/-- An atomic `uint64` field of the server, in an invariant (any value). -/
def srvAtomicU64 (a : Loc) : IProp GF :=
  inv (nroot.@"server") iprop(∃ v : w64, sync.atomic.ownUint64 a (DFrac.own 1) v)

instance srvAtomicU64_persistent (a : Loc) : Persistent (srvAtomicU64 (GF := GF) a) := by
  unfold srvAtomicU64; infer_instance

/-- The values of the server's fields the request path reads. -/
structure ReqFields where
  gen : Loc
  w : GoInterface
  maxReq : w64
  fg : GoInterface
  cca : Bool
  electionTicks : w64
  tickMs : w64
  auth : GoInterface
  done : GoChan
  memberID : w64
  cluster : Loc
  tr : GoInterface
  cid : w64

/-- **The cluster and the transport, as the request path reads them** (persistent; unit P1b,
2026-10-14): the cluster's id `cid` (`RaftCluster.ID`, the response header's), its members
(`isRaftCluster`: `Members()`, in `parseProposeCtxErr`), and the transport's `ActiveSince`
(`isConnectedSince`, there too). Contracts of names-only code
(`membership`'s fields, rafthttp): premises of the server's start (`srvReqBuilt`). -/
def srvPeersOk (cl : Loc) (cid : w64) (tr : GoInterface) : IProp GF :=
  iprop(membership.clusterCid cl cid ∗ membership.isRaftCluster cl ∗ rafthttp.isTransporter tr)

instance srvPeersOk_persistent (cl : Loc) (cid : w64) (tr : GoInterface) :
    Persistent (srvPeersOk (GF := GF) cl cid tr) := by
  unfold srvPeersOk; infer_instance

/-- **The server `s` as a proposer sees it** at the fields' values `v` (persistent; see the file
header), the applier's environment `E` (whose store's certificates the results carry), the
request path's ghost names `ρ`. -/
def srvReqFieldsAt (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) : IProp GF :=
  iprop(structFieldRef EtcdServer go!"reqIDGen" s ↦□ v.gen ∗ idGen ρ.ids v.gen (srvFloorFact E) ∗
    structFieldRef EtcdServer go!"w" s ↦□ v.w ∗ waitInv v.w ρ E ∗
    srvRaftNode s ρ.raft ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ v.maxReq ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ v.fg ∗ isFeatureGate v.fg ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ v.cca ∗
    srvCfgFieldAddr s go!"ElectionTicks" ↦□ v.electionTicks ∗
    srvCfgFieldAddr s go!"TickMs" ↦□ v.tickMs ∗
    structFieldRef EtcdServer go!"authStore" s ↦□ v.auth ∗ isReqAuth v.auth E.RD ∗
    structFieldRef EtcdServer go!"done" s ↦□ v.done ∗ srvDoneChan v.done ∗
    structFieldRef EtcdServer go!"memberID" s ↦□ v.memberID ∗
    srvAtomicU64 (structFieldRef EtcdServer go!"lead" s) ∗
    structFieldRef EtcdServer go!"cluster" s ↦□ v.cluster ∗
    structFieldRef raftNodeConfig go!"transport"
      (structFieldRef raftNode go!"raftNodeConfig" (structFieldRef EtcdServer go!"r" s)) ↦□ v.tr ∗
    srvPeersOk v.cluster v.cid v.tr ∗
    srvIndexInvs s E ∗
    srvMintInv ρ ∗ kvInv ρ.raft ρ.kv ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

instance srvReqFieldsAt_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    Persistent (srvReqFieldsAt s E ρ v) := by
  unfold srvReqFieldsAt; infer_instance

/-- **The server `s`, as a proposer sees it** (persistent), with auth off (the auth-mode merge's
step 5, 2026-10-29: `⌜E.authOn = false⌝`, so that the one spec of a function over the mode
`E.authOn` gives the mode-off one, `isServerReq_authOff`). -/
def isServerReq (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop((∃ v : ReqFields, srvReqFieldsAt s E ρ v) ∗ ⌜E.authOn = false⌝)

instance isServerReq_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (isServerReq s E ρ) := by
  unfold isServerReq; infer_instance

/-- A server seen as a proposer with auth off has auth off. -/
theorem isServerReq_authOff (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ ⌜E.authOn = false⌝ := by
  unfold isServerReq
  iintro ⟨-, %h⟩
  ipureintro; exact h

/-- The fields of a server seen as a proposer. -/
theorem isServerReq_fields (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ ∃ v : ReqFields, srvReqFieldsAt s E ρ v := by
  unfold isServerReq
  iintro ⟨H, -⟩
  iexact H

/-- `s.leadTimeMu`'s lock invariant: the time the current leader was elected. -/
def leadTimeP (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ t : time.Time, structFieldRef EtcdServer go!"leadElectedTime" s ↦{DFrac.own q} t)

/-- **A reader slot of `s.leadTimeMu`** (a request goroutine's; see the file header). -/
def srvLeadTimeReader (s : Loc) : IProp GF :=
  sync.ownRWMutex (structFieldRef EtcdServer go!"leadTimeMu" s) (leadTimeP s)

/-- **The proposal may have been made** (the error case of a request): either it was not, or its
data `d`, which decode to the request `rq'` (the encoding of the proposer's request with its
header), were deposited with raft (`srvDeposited`): raft fires the update at the data's first
commit, so the apply thread may still apply the request after the proposer gave up (etcd's
documented behavior for a timeout). -/
def srvMaybeDeposited (ρ : ReqNames) (rq : apply.IRRModel) : IProp GF :=
  iprop(∃ proposed : Bool, if proposed then iprop(∃ (d : List w8) (hm : apply.HeaderModel)
      (rq' : apply.IRRModel), srvDeposited ρ.raft d ∗
      ⌜apply.irrDecode d = some rq' ∧ irrWireOf (apply.withHeader rq hm) rq'⌝)
    else iprop(True))

/-- **The apply thread's answer to `rq'` was a success** with the response `resp`: it dispatched
the request at the KV state `x` (its log `x.log`, the log the entry met), to `x'`
(`apply.applyStep`, outcome `o`, `skip` the wrapper's `SkipRangeExecution`), the response is the
apply package's (`dispatchAnswer` with no error), mvcc's certificate of the log after, the
token of the revision the step appended, if it appended one (`revMinted`, unit V1);
(2026-10-14, unit C2a) the log after applied through an index of the committed log
(`appliedWit γr`, the result's witness, `resultIsW`); and (the vertical slice's unit V2) a KV
write ran at a log extending the proposer's floor `F` (`apply.kvFloorOk`); and (unit W-M3) the log
the entry met is `lb` (`x.log`, which the raft request's result ties to the raft prefix the
proposal's update fired at) and the log after is certified (`certOk`); and (linkv-txn stage B1,
2026-10-20) the ranges were run (`skip = false`: the apply thread found the id registered). -/
def appliedOk (E : apply.AEnv GF) (γr : ReadNames) (rq' : apply.IRRModel) (F : mvcc.Log)
    (resp : GoInterface) (lb : mvcc.Log) :
    IProp GF :=
  iprop(∃ (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
    ⌜apply.applyStep rq' true x x' (.dispatched o skip) ∧ apply.kvFloorOk rq' true F x.log o ∧
      x.log = lb ∧ skip = false⌝ ∗
    apply.dispatchAnswer rq' x.log skip resp GoInterface.nil null o ∗ mvcc.idxCert E.γ.idx x'.log ∗
    revMinted E x.log x'.log ∗ appliedWit γr x'.log ∗ mvcc.certOk E.γ x'.log)

/-- **The apply thread's answer to `rq'` carried the error `err`** (`result.Err`): the result
`ar` of applying `rq'` (`resultIs`), whose `Err` is `err`. -/
def appliedErr (E : apply.AEnv GF) (rq' : apply.IRRModel) (F : mvcc.Log) (err : GoInterface) :
    IProp GF :=
  iprop(∃ (ar : Loc) (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result),
    ar ↦□ v ∗ ⌜v.Err' = err⌝ ∗ resultIs E rq' F ar)

end srv

end EtcdGrove
end Perennial
