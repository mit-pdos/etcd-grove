/-
**The server's contract instantiated** (units 3a and 3b of the request path, 2026-10-12): the
parameters `A : KVAns GF` of unit 1's `raftKV s A` (`InvKV.lean`) for the server `s`
(`srvKVAns s E ρ γr c`), and every conjunct of `raftKV` proved from the server's linked specs
(`EtcdServer.Put`/`DeleteRange`, unit 2; `Range`/`Txn`, the getters, unit 3b):
`kvPutOk_of_server`, `kvDeleteOk_of_server`, `kvRangeOk_of_server`, `kvTxnOk_of_server`,
`kvGetOk_of_server`, `raftKV_of_server` (no premise but the server's facts). Lean-first (no
Rocq counterpart); plan: `notes/decisions.md`, "The request path".

**`srvKVAns s E ρ γr c`**: what a call needs (`srvCall`: the request's context, one id credit, a
reader slot of `s.leadTimeMu`; `srvRdCall`: the store's reader slots, the logger's, the committed
index `c` the caller knew of), what a request must satisfy beyond its check (`pre`: a read-only
transaction's gets within the txn package's model, `txnInModel`), what a successful answer is
(`putAppliedOk`, `deleteAppliedOk`: applied by the apply thread at the log the entry met;
`rangeAnsOk`: the txn package's range at a certified log, after the read index unless
serializable; `txnReadAns`/`txnAppliedAns`: a read-only transaction run at a certified log, or a
writing one applied by the apply thread), what an error is (the apply's or the proposal's for
the writes, any for the reads), every resource of the call back with each answer but the id
credit a write consumed; `KV().Rev()` needs the store's reader slots (`revR`), which `fill`
never uses on these answers since their revision is not `0`.

**What the server's answers give the handler** (`kvAnswer`): the response header's four id
fields owned (`txn.respHdrOwn`, from `apply.appliedHdr` for the writes, from the txn package's
`asembleRangeResponse`/`newTxnResp` for the reads → `hdrW`), its revision read-only and not `0`
(the log has `NewStore`'s two revisions: `hdrRevIn`'s first case), an error `togRPCError` can
take (`srvErrIs`, from `applyErrIs`: `srvErrIs_of_applyErrIs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckShape
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite
@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An error `togRPCError` can take, from the apply package's facts**: a non-nil error with
`applyErrIs` (its tree, a safe map key, an `Error()` that returns). -/
theorem srvErrIs_of_applyErrIs (err : GoInterface) (hne : err ≠ GoInterface.nil) :
    applyErrIs (GF := GF) err ⊢ srvErrIs err := by
  iintro #H
  iunfold srvErrIs
  isplitr
  · ipureintro; exact hne
  isplitr
  · iexact H
  ihave #Hkm : iprop(errKeyMsg err) $$ []
  · iunfold applyErrIs at H; icases H with ⟨-, #Hkm⟩; iexact Hkm
  iunfold errKeyMsg at Hkm
  icases Hkm with (%Hn | ⟨%Hsafe, %ei, %Hei, #Hm⟩)
  · exact absurd Hn hne
  isplitr
  · ipureintro; exact Hsafe
  iexists ei
  isplitr
  · ipureintro; exact Hei
  iunfold errMsgOk at Hm
  iexact Hm

/-- **What one call of the server's write path needs** (`EtcdServer.Put`/`DeleteRange`): the
request's context (a `context.Context` value with Perennial's `isContext`), one id credit (for
`reqIDGen.Next()`), a reader slot of `s.leadTimeMu` (`parseProposeCtxErr` read-locks it; given
back with the answer). The context carries no trace (`traceutil.ctxTraceIs ci none`, unit P1b,
2026-10-14: `EtcdServer.Range`/`Txn` take the context's trace, `EnsureTrace` makes theirs; a
gRPC handler's context has no `TraceKey` value). -/
def srvCall (s : Loc) (ρ : ReqNames) (ctx : GoInterface) : IProp GF :=
  iprop(∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)), ⌜ctx = GoInterface.ok ci⌝ ∗
    context.isContext ci cd ∗ traceutil.ctxTraceIs ci none ∗ idCred ρ.ids 1 ∗
    srvLeadTimeReader s)

/-- `putAppliedOk` but the caller's reader slot: the answer's facts (the vertical slice's unit
V1: what the client learns of the response; `client/v3/Results.lean`'s `etcd_putRunOk`), with
(2026-10-14, unit C2a) the write's witness at the read names `γw` (`appliedWit`), and (the
vertical slice's unit V2) the log the put met extending the caller's floor `F`. -/
def putApplied (E : apply.AEnv GF) (γw : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) :
    IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log)
      (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x' (.dispatched (.applied l false) skip) ∧
      r = W64 (x.log.length : Int) ∧ F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    apply.putOutcomeIs x.log o resp GoInterface.nil (.applied l false) ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γw x'.log ∗
    mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log))

/-- **A successful `Put` of `o`** (`EtcdServer.Put`'s success, at the handler's level): the
request with the server's header (`hm`) was dispatched by the apply thread at the KV state `x`
to `x'` and applied (`applied l false`: `putModel`'s, no `ErrNoSpace`), the response is the
put's (`putOutcomeIs` at `x.log`: header revision `x.log.length`, the previous key-value if
asked), the header's revision `r` is that revision, mvcc's certificate of the log after, the
token of the revision it appended (`revMinted`, unit V1), (2026-10-14, unit C2a) the log
after applied through an index of the committed log (`appliedWit γw`, at the request path's read
names: a linearizable read at that index reads a log extending it), and (the vertical slice's
unit V2) the log the put met extending the caller's floor `F`; and (unit W-M3) the caller's
certificate of the log after (`certOk`) and the deposited update's `□ Q` at the state of the log
the put met (the update fired there); the caller's reader slot back. -/
def putAppliedOk (s : Loc) (E : apply.AEnv GF) (γw : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ putApplied E γw F o Q resp r)

/-- `deleteAppliedOk` but the caller's reader slot (as `putApplied`). -/
def deleteApplied (E : apply.AEnv GF) (γw : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
      (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      r = W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    apply.deleteOutcomeIs x.log op' resp GoInterface.nil (.applied l false) ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γw x'.log ∗
    mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log))

/-- **A successful `DeleteRange` of `o`**: as `putAppliedOk`, for the request the proposed data
decode to (`rq'`, whose delete `op'` is `o` unless its range end is `[0]`, `irrWireOf`); the
header's revision the delete's (`writeRev`). -/
def deleteAppliedOk (s : Loc) (E : apply.AEnv GF) (γw : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ deleteApplied E γw F o Q resp r)

/-- `putErrOk` but the reader slot (the vertical slice's unit V1: what the client learns of a
failed put). -/
def putErr (E : apply.AEnv GF) (ρ : ReqNames) (F : mvcc.Log) (o : OpFull) (err : GoInterface) :
    IProp GF :=
  iprop((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut o) hm) F err) ∨
    srvMaybeDeposited ρ (irrPut o))

/-- **A failed `Put` of `o`**: the apply thread's error (`appliedErr`), or the proposal's (made
or not; if made, deposited: it may still be applied, `srvMaybeDeposited`); the reader slot
back. -/
def putErrOk (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (F : mvcc.Log) (o : OpFull)
    (err : GoInterface) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ putErr E ρ F o err)

/-- `deleteErrOk` but the reader slot (as `putErr`). -/
def deleteErr (E : apply.AEnv GF) (ρ : ReqNames) (F : mvcc.Log) (o : OpFull) (err : GoInterface) :
    IProp GF :=
  iprop((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
      ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
    srvMaybeDeposited ρ (irrDeleteRange o))

/-- **A failed `DeleteRange` of `o`** (as `putErrOk`). -/
def deleteErrOk (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (F : mvcc.Log) (o : OpFull)
    (err : GoInterface) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ deleteErr E ρ F o err)

/-- **The transaction model of a checked transaction request** (`none` if an operation is
empty: the check rejects it). -/
def txnModelOf (cs : List CmpModel) (ts es : List ReqOp) : Option TxnModel :=
  match ReqOp.toTxnOps ts, ReqOp.toTxnOps es with
  | some ts', some es' => some { cmps := cs, thenOps := ts', elseOps := es' }
  | _, _ => none

/-- The branches' models of a transaction model built from operations. -/
theorem txnModelOf_ops {cs : List CmpModel} {ts es : List ReqOp} {t : TxnModel}
    (h : txnModelOf cs ts es = some t) :
    ReqOp.toTxnOps ts = some t.thenOps ∧ ReqOp.toTxnOps es = some t.elseOps := by
  unfold txnModelOf at h
  split at h
  · rename_i ts' es' h1 h2
    simp only [Option.some.injEq] at h; subst h
    exact ⟨h1, h2⟩
  · cases h

/-- **A transaction request within the txn package's model** (`srvKVAns`' `pre`, a premise):
if read-only, each of its gets reads the transaction's revision (`0`) and is not a sort cut early
by a limit (`txn.cutEarly`, `issues/etcd-range-sort-none-limit.md`): `txn.txnGetsOk` but for the
sort target, which `checkRangeRequest` gives. A writing transaction's premises are the apply
thread's (`TxnPre`, on the committed entries). -/
def txnInModel (cs : List CmpModel) (ts es : List ReqOp) : Prop :=
  ∀ t, txnModelOf cs ts es = some t → txn.txnReadonly t = true →
    ∀ o : OpFull, TxnOp.get o ∈ t.thenOps ++ t.elseOps → o.base.rev = W64 0 ∧ ¬ txn.cutEarly o

/-- **A successful `Range` of `o`, at the handler's level** (persistent; `rangeReadOk` but the
header's fields, which `hdrW` takes): the txn package's answer at a certified log of at least
two revisions, the header's revision `r` its last, after the read index unless serializable, the
log extending the log applied through an index at least `c` (`readLogOk`, 2026-10-13, unit 4b),
the log extending the floor `F` (the vertical slice's unit V2), and (2026-10-14, unit T1) a
linearizable read's log the KV model of a committed raft log at which the read's update gave
`□ Q`. -/
def rangeAnsOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (resp : Loc) (r : w64) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ r = W64 ((log.length : Int) - 1) ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true)

/-- **A successful read-only `Txn` of `t`, at the handler's level** (`txnReadOk` but the
header's fields; unit W-M3: with the read deposit's result, as `rangeAnsOk`'s). -/
def txnReadAns (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : List EntryModel → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ r = W64 ((log.length : Int) - 1) ∧ F <+: log⌝ ∗
    (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
    (if txn.txnSerializable t then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2)

/-- **A successful writing `Txn` of `t`, at the handler's level** (`txnAppliedOk` but the
header's fields): the request the proposed data decode to, applied by the apply thread at `x`,
the response the transaction's, the header's revision `r` its write revision. -/
def txnAppliedAns (E : apply.AEnv GF) (γw : ReadNames) (F : mvcc.Log) (t : TxnModel)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (t' : TxnModel)
      (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq' ∧ rq'.txn = some t' ∧
      (irrNoZeroEnd (irrTxn t) → t' = t) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      r = W64 (mvcc.writeRev x.log
        (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 : Int) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    apply.txnOutcomeIs x.log t' skip resp GoInterface.nil (.applied l false) ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γw x'.log ∗
    mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log))

/-- **A client's update, deposited with a call** (2026-10-14, unit T1; 2026-10-15, unit T2: over
the whole state): none, a write's update for the KV operation `o` with result `Q` (`kvOpAu`: a
put, a delete or a writing transaction), or a read's with result `Q` (`kvReadAu`: a linearizable
range). -/
inductive KVDep (GF : BundledGFunctors) where
  | none
  | op (o : KVOp) (Q : KVState → IProp GF)
  | read (Q : KVState → IProp GF)
  /-- (2026-10-19, D21 M6) a put's update fired at most once (`kvOpAu1`); since 2026-10-20
  (linkv-txn stage A) a delete's and a writing transaction's too -/
  | op1 (o : KVOp) (Q : KVState → IProp GF)

/-- The deposit's update: a write's at the request path's KV names, a read's at the read names'
(both persistent). -/
def kvDepOwn (ρ : ReqNames) (γr : ReadNames) : KVDep GF → IProp GF
  | .none => iprop(True)
  | .op o Q => kvOpAu ρ.kv o Q
  | .read Q => kvReadAu γr.kv Q
  | .op1 o Q => kvOpAu1 ρ.kv o Q

/-- A write's result under the deposit. -/
def opDepQ : KVDep GF → KVState → IProp GF
  | .op _ Q => Q
  | .op1 _ Q => Q
  | _ => fun _ => iprop(True)

/-- A range's result over committed logs under the deposit (`kvDep`'s form). -/
def rangeDepQ (γk : KVNames) : KVDep GF → List EntryModel → IProp GF
  | .read Q => fun L => iprop(□ Q (kvStateOf (kvModel γk L)))
  | _ => fun _ => iprop(True)

/-- **What a request must be under the deposit** (2026-10-15, unit T2): a put, a delete or a
writing transaction the deposited write's operation (a put with no lease; a delete with its range
end not `[0]`; a plain transaction, `txn.txnPlain`, no range end `[0]`: `txnNoZeroEnd`); a range
linearizable if a read is deposited. Since D19c (2026-10-18) a writing transaction also has no
nested transaction putting a key a later sibling deletes (`ReqOp.siblingSafeL`) and no get, at any
depth, sorting cut by a limit (`txn.OpsNoCut`): with the checks they give its apply's shape
(`txnShape_of_check`, `CheckShape.lean`). -/
def kvDepPre (d : KVDep GF) : KVReq → Prop
  | .put o => (∃ Q, d = .op1 (.put o) Q) ∧ o.leaseID = W64 0
  | .range o => ∀ Q, d = .read Q → o.base.serializable = false
  | .deleteRange o => (∃ Q, d = .op1 (.deleteRange o) Q) ∧ o.base.rangeEnd ≠ [W8 0]
  | .txn cs ts es => ∀ t, txnModelOf cs ts es = some t →
      (txn.txnReadonly t = true ∧ ∀ Q, d = .read Q → txn.txnSerializable t = false) ∨
      ((∃ Q, d = .op1 (.txn t) Q) ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧
        ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es ∧ txn.OpsNoCut t.thenOps ∧
        txn.OpsNoCut t.elseOps)

/-- **The server's parameters of `raftKV`** (see the file header), with the caller's floor `F`
(the vertical slice's unit V2) and the client's deposit `d` (2026-10-14, unit T1). -/
def srvKVAns (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : KVDep GF) : KVAns GF where
  call ctx := iprop(srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d ∗ mvcc.idxCert E.γ.idx F)
  pre q := (match q with
    | .txn cs ts es => txnInModel cs ts es
    | _ => True) ∧ kvDepPre d q
  ok q resp _h r := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putAppliedOk s E ρ.rd F o (opDepQ d) resp r
    | .deleteRange o => deleteAppliedOk s E ρ.rd F o (opDepQ d) resp r
    | .range o => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
        rangeAnsOk E γr c F o resp r (rangeDepQ γr.kv d))
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗ txnReadAns E γr c F t (rangeDepQ γr.kv d) resp r)
        else txnAppliedAns E ρ.rd F t (opDepQ d) resp r))
  err q e := iprop(srvRdCall s E γr c ∗ match q with
    | .put o => putErrOk s E ρ F o e
    | .deleteRange o => deleteErrOk s E ρ F o e
    | .range _ => iprop(idCred ρ.ids 1 ∗ srvLeadTimeReader s)
    | .txn cs ts es => iprop(srvLeadTimeReader s ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e))
  revR := mvcc.storeReader E.s E.γ

open Iris.ProofMode in
/-- A deposit is a read deposit (`kvDep`) of its range result. -/
theorem kvDep_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) :
    kvDepOwn ρ γr d ⊢ kvDep γr.kv (rangeDepQ γr.kv d) := by
  iintro H
  iunfold kvDep
  cases d with
  | none => iright; ipureintro; rfl
  | op o Q => iright; ipureintro; rfl
  | op1 o Q => iright; ipureintro; rfl
  | read Q =>
    ileft
    iexists Q
    iunfold kvDepOwn at H
    iframe H
    ipureintro; rfl

open Iris.ProofMode in
/-- A put's permit (`putPermit`) from its deposit. -/
theorem putPermit_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) (o : OpFull)
    (hd : kvDepPre d (.put o)) : kvDepOwn ρ γr d ⊢ putPermit ρ.kv o (opDepQ d) := by
  iintro H
  iunfold putPermit
  simp only [kvDepPre] at hd
  obtain ⟨⟨Q, rfl⟩, hl⟩ := hd
  isimp only [kvDepOwn] at H
  isplitr
  · ipureintro; exact hl
  simp only [opDepQ]
  iexact H

open Iris.ProofMode in
/-- A delete's permit (`deletePermit`) from its deposit. -/
theorem deletePermit_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) (o : OpFull)
    (hd : kvDepPre d (.deleteRange o)) : kvDepOwn ρ γr d ⊢ deletePermit ρ.kv o (opDepQ d) := by
  iintro H
  iunfold deletePermit
  simp only [kvDepPre] at hd
  obtain ⟨⟨Q, rfl⟩, hz⟩ := hd
  isimp only [kvDepOwn] at H
  isplitr
  · ipureintro; exact hz
  simp only [opDepQ]
  iexact H

open Iris.ProofMode in
/-- A writing transaction's permit (`txnPermit`) from its deposit. -/
theorem txnPermit_of_dep (ρ : ReqNames) (γr : ReadNames) (d : KVDep GF) (t : TxnModel)
    (hd : (∃ Q, d = .op1 (.txn t) Q) ∧ txn.txnPlain t ∧ txnNoZeroEnd t) (hs : txn.txnShape t) :
    kvDepOwn ρ γr d ⊢ txnPermit ρ.kv t (opDepQ d) := by
  iintro H
  iunfold txnPermit
  obtain ⟨⟨Q, rfl⟩, hp, hz⟩ := hd
  isimp only [kvDepOwn] at H
  isplitr
  · ipureintro; exact ⟨hp, hz, hs⟩
  simp only [opDepQ]
  iexact H

/-- **The `*kvServer` `p`, but for the server's contract** (`kvServerIs` without `raftKV`): its
header, `kv` the server `s`, the transaction budget `n`. What `NewKVServer(s)` builds, apart
from the server's own triples (`kvServerIs_of_at`). -/
def kvServerAt (p : Loc) (s : Loc) (A : KVAns GF) (cid mid n : w64) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    hdrIs (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"hdr" p)
      s A cid mid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"kv" p ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"maxTxnOps" p ↦□ n)

instance kvServerAt_persistent (p s : Loc) (A : KVAns GF) (cid mid n : w64) :
    Persistent (kvServerAt p s A cid mid n) := by
  unfold kvServerAt; infer_instance

theorem kvServerIs_of_at (p s : Loc) (A : KVAns GF) (cid mid n : w64) :
    kvServerAt (GF := GF) p s A cid mid n ∗ raftKV s A ⊢ kvServerIs p s A cid mid n := by
  iintro ⟨#Hat, #HKV⟩
  iunfold kvServerAt at Hat
  icases Hat with ⟨%Hpn, #Hh, #Hk, #Hn⟩
  iunfold kvServerIs
  iframe #
  ipureintro; exact Hpn

end defs

/-- A revision at a log of `NewStore`'s two revisions at least, and room: not `0`. -/
theorem w64_rev_ne_zero (n : Nat) (h1 : 1 ≤ n) (h2 : n + 4 ≤ 2 ^ 63) : W64 (n : Int) ≠ W64 0 := by
  intro h
  have := congrArg (fun w : w64 => uint.Z w) h
  word

/-- The delete's revision (`writeRev`) at such a log: at least `1`. -/
theorem writeRev_ne_zero (log : mvcc.Log) (pend : List mvcc.Change) (h1 : 2 ≤ log.length)
    (h2 : log.length + 4 ≤ 2 ^ 63) : W64 ((mvcc.writeRev log pend : Nat) : Int) ≠ W64 0 := by
  apply w64_rev_ne_zero
  · unfold mvcc.writeRev; split <;> omega
  · unfold mvcc.writeRev; split <;> omega

/-- A range passing `checkRangeRequest` has a valid sort target. -/
theorem validSortTarget_of_rangeCheck (o : OpFull) (h : rangeCheck o = none) :
    txn.validSortTarget o := by
  unfold rangeCheck at h
  unfold txn.validSortTarget
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h3
  simp only [sortTargetKnown, Bool.not_eq_true', decide_eq_false_iff_not] at h3
  exact Classical.not_not.1 h3

mutual
/-- The model of a checked operation is a get only for a range. -/
theorem toTxnOp_get (u : ReqOp) (o : OpFull) (h : ReqOp.toTxnOp u = some (.get o)) :
    u = .range o := by
  cases u with
  | range o' => simp only [ReqOp.toTxnOp, Option.some.injEq, TxnOp.get.injEq] at h; rw [h]
  | put o' =>
    simp only [ReqOp.toTxnOp, Option.some.injEq] at h
    unfold txn.putTxnOp at h; split at h <;> (try split at h) <;> cases h
  | delete o' => simp [ReqOp.toTxnOp] at h
  | txn cs ts es =>
    simp only [ReqOp.toTxnOp] at h
    split at h <;> simp at h
  | empty => simp [ReqOp.toTxnOp] at h

/-- A get of the model of checked operations is one of their ranges. -/
theorem toTxnOps_get_mem : ∀ (us : List ReqOp) (ts : List TxnOp),
    ReqOp.toTxnOps us = some ts → ∀ o, TxnOp.get o ∈ ts → ReqOp.range o ∈ us
  | [], ts, h, o, hm => by
    simp only [ReqOp.toTxnOps, Option.some.injEq] at h; subst h; simp at hm
  | u :: us, ts, h, o, hm => by
    simp only [ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.1 hm with he | he
      · subst he; exact List.mem_cons.2 (Or.inl (toTxnOp_get u o h1).symm)
      · exact List.mem_cons.2 (Or.inr (toTxnOps_get_mem us ts' h2 o he))
    · cases h
end

/-- **A checked read-only transaction within the model has its gets within the txn package's
model** (`txn.txnGetsOk`): the sort target from the check. -/
theorem txnGetsOk_of_check (n : Int) (cs : List CmpModel) (ts es : List ReqOp) (t : TxnModel)
    (hck : txnReqOk n cs ts es) (hm : txnModelOf cs ts es = some t)
    (hin : txnInModel cs ts es) : txn.txnReadonly t = true → txn.txnGetsOk t := by
  intro hro o ho
  obtain ⟨h1, h2⟩ := hin t hm hro o ho
  refine ⟨h1, h2, ?_⟩
  have hok := (txnCheck_ok_iff n cs ts es).1 hck
  unfold txnModelOf at hm
  split at hm
  · rename_i ts' es' hts hes
    simp only [Option.some.injEq] at hm
    subst hm
    rcases List.mem_append.1 ho with ho | ho
    · have hu := toTxnOps_get_mem ts ts' hts o ho
      have := hok.2.2.1 _ hu
      exact validSortTarget_of_rangeCheck o this
    · have hu := toTxnOps_get_mem es es' hes o ho
      have := hok.2.2.2 _ hu
      exact validSortTarget_of_rangeCheck o this
  · cases hm

/-- A checked transaction has a model. -/
theorem txnModelOf_of_check {n : Int} {cs : List CmpModel} {ts es : List ReqOp}
    (h : txnReqOk n cs ts es) : ∃ ts' es', ReqOp.toTxnOps ts = some ts' ∧
      ReqOp.toTxnOps es = some es' ∧
      txnModelOf cs ts es = some { cmps := cs, thenOps := ts', elseOps := es' } := by
  obtain ⟨ts', es', h1, h2⟩ := txnCheck_toTxnOps h
  exact ⟨ts', es', h1, h2, by simp [txnModelOf, h1, h2]⟩

/-- The last revision of a log of `NewStore`'s two revisions at least: not `0`. -/
theorem w64_last_ne_zero (log : mvcc.Log) (h1 : 2 ≤ log.length) (h2 : log.length + 3 ≤ 2 ^ 63) :
    W64 ((log.length : Int) - 1) ≠ W64 0 := by
  intro h
  have := congrArg (fun w : w64 => uint.Z w) h
  word

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The header's fields from the txn package's ownership (`respHdrOwn`) and a response's
read-only header pointer and revision: the handler's `hdrW` and `hdrRevIn` (first case). -/
theorem hdr_of_own (hf h : Loc) (rv : w64) (R : IProp GF) (hrv : rv ≠ W64 0) :
    hf ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗ txn.respHdrOwn hf ⊢
    hf ↦□ h ∗ hdrW h ∗ hdrRevIn R h rv := by
  iintro ⟨#Hhf, %Hhn, #Hrev, Hown⟩
  iunfold txn.respHdrOwn at Hown
  icases Hown with ⟨%h', #Hhf', %Hhn', %c, %m, %t, %ld, Hc, Hm, Ht, Hl⟩
  icombine Hhf Hhf' gives %Heq
  subst Heq
  iframe Hhf
  isplitl [Hc Hm Ht Hl]
  · iunfold hdrW
    isplitr
    · ipureintro; exact Hhn
    iexists c, m, t, ld
    iframe
  iunfold hdrRevIn
  ileft
  isplitr
  · ipureintro; exact hrv
  iexact Hrev

/-- **`raftKV`'s `Put` conjunct, from `EtcdServer.Put`**. -/
theorem kvPutOk_of_server (hPut : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerReq s E ρ ⊢
      kvPutOk s (srvKVAns s E ρ γr c F d) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvPutOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  have hd : kvDepPre d (.put o) := Hok.2.2
  simp only [srvKVAns]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF⟩
  ihave Hpp := putPermit_of_dep ρ γr d o hd $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hPut s E ρ ci cd r o (opDepQ d) F $$ [Hrd Hard Hcred Hpp] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred Hpp
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit, #Hcok, HQv⟩ |
    ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hstep, ⟨l, rfl⟩, HFx⟩ := Hst
    subst Herr
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    icases Hpo with ⟨#Hresp, -⟩
    ihave #Hresp' := Hresp
    iunfold txn.putResponseIs at Hresp'
    icases Hresp' with ⟨%Hrn, %h, %pk, #Hhf, %Hhn, #Hrev, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hown, %Hlen⟩
    ileft
    isplitr
    · ipureintro; exact ⟨trivial, Hrn⟩
    iexists h, W64 (x.log.length : Int)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h (W64 (x.log.length : Int)) (mvcc.storeReader E.s E.γ)
      (w64_rev_ne_zero _ (by omega) Hlen.2) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    iframe Hrc
    iunfold putAppliedOk
    iframe Hrd
    iunfold putApplied
    iexists hm, x, x', l, skip
    iframe Hcert HMint Hwit Hcok HQv
    isplitr
    · ipureintro; exact ⟨Hstep, rfl, HFx, Hlen.1, Hlen.2⟩
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc
    iunfold putErrOk
    iframe Hrd
    iunfold putErr
    iexact Hfail

theorem kvDeleteOk_of_server (hDel : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerReq s E ρ ⊢
      kvDeleteOk s (srvKVAns s E ρ γr c F d) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvDeleteOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  have hd : kvDepPre d (.deleteRange o) := Hok.2.2
  simp only [srvKVAns]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF⟩
  ihave Hdep := deletePermit_of_dep ρ γr d o hd $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, -, Hcred, Hrd⟩
  subst Hci
  ihave ⟨Hard, Hrc⟩ := srvRdCall_rd s E γr c $$ Hrc
  wp_apply hDel s E ρ ci cd r o (opDepQ d) F $$ [Hrd Hard Hcred Hdep] as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe #; iframe Hrd Hard Hcred Hdep
  ihave Hrc := Hrc $$ Hard
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %rq', %op', %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert, HMint, #Hwit,
    #Hcok, HQv⟩ | ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hwire, Hop', Hnz, Hstep, ⟨l, rfl⟩, HFx⟩ := Hst
    subst Herr
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    icases Hpo with ⟨#Hresp, -⟩
    ihave #Hresp' := Hresp
    iunfold txn.deleteRangeResponseIs at Hresp'
    icases Hresp' with ⟨%Hrn, %h, %sl, %ps, #Hhf, %Hhn, #Hrev, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hown, %Hlen⟩
    ileft
    isplitr
    · ipureintro; exact ⟨trivial, Hrn⟩
    iexists h, W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
      (writeRev_ne_zero _ _ Hlen.1 Hlen.2) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    iframe Hrc
    iunfold deleteAppliedOk
    iframe Hrd
    iunfold deleteApplied
    iexists hm, rq', op', x, x', l, skip
    iframe Hcert HMint Hwit Hcok HQv
    isplitr
    · ipureintro; exact ⟨Hwire, Hop', Hnz, Hstep, rfl, HFx, Hlen.1, Hlen.2⟩
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc
    iunfold deleteErrOk
    iframe Hrd
    iunfold deleteErr
    iexact Hfail

/-- **`raftKV`'s `Range` conjunct, from `EtcdServer.Range`**. -/
theorem kvRangeOk_of_server (hRange : EtcdServer.Range.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      kvRangeOk s (srvKVAns s E ρ γr c F d) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  iunfold kvRangeOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  simp only [srvKVAns]
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF⟩
  ihave #Hdep' := kvDep_of_dep ρ γr d $$ Hdep
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hct, Hcred, Hlt⟩
  subst Hci
  wp_apply hRange s E ρ γr c ci cd r o none false (rangeDepQ γr.kv d) F $$ [Hrc] as %resp %err ⟨Hrc, Hres⟩
  · iframe #; iframe Hrc
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    ipureintro; exact validSortTarget_of_rangeCheck o Hok.1
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, Hok'⟩ | ⟨%Hre, #HaE⟩)
  · obtain ⟨rfl, Hrn⟩ := Herr
    iunfold rangeReadOk at Hok'
    icases Hok' with ⟨%log, #Hcert, #Hcok, %Hlen, Hlin, HQl, #Hres, Hown⟩
    ihave #Hres' := Hres
    iunfold txn.rangeResult at Hres'
    icases Hres' with (⟨-, %ef, -, %He⟩ | ⟨-, #He⟩ | ⟨-, %kvs, %more, #Hresp, -⟩)
    · cases He
    · ihave %Hne := mvcc.errorfIs_ne_nil _ $$ He
      exact absurd rfl Hne
    iunfold txn.rangeResponseIs at Hresp
    icases Hresp with ⟨-, %h, %sl, %ps, #Hhf, %Hhn, #Hrev, -⟩
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, Hrn⟩
    iexists h, W64 ((log.length : Int) - 1)
    ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
      (w64_last_ne_zero log Hlen.1 Hlen.2.1) $$ [$Hown]
    · iframe #; ipureintro; exact Hhn
    iframe Hhf2 Hw Hri
    simp only
    iframe Hrc Hcred Hlt
    iunfold rangeAnsOk
    iexists log
    iframe Hcert Hcok Hres Hlin HQl
    ipureintro; exact ⟨Hlen.1, Hlen.2.1, rfl, Hlen.2.2⟩
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iframe Hrc Hcred Hlt

/-- **`raftKV`'s `Txn` conjunct, from `EtcdServer.Txn`**: the checked request's model (no empty
operation), its read-only gets within the model (`txnGetsOk`: the premise `txnInModel` and the
check's sort targets). -/
theorem kvTxnOk_of_server (hTxn : EtcdServer.Txn.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      kvTxnOk s (srvKVAns s E ρ γr c F d) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  iunfold kvTxnOk
  iintro %ctx %r %cs %ts %es %n !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  obtain ⟨Hck, HivT, HivE, Hin, Hro⟩ := Hok
  obtain ⟨ts', es', hts, hes, hm⟩ := txnModelOf_of_check Hck
  simp only [srvKVAns] at Hin ⊢
  simp only [kvDepPre] at Hro
  icases Hcall with ⟨Hcall, Hrc, Hdep, #HF⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, #Hct, Hcred, Hlt⟩
  subst Hci
  ihave #Hrt := txnReqIs_txnRequestIs r cs ts es ts' es' hts hes $$ Hr
  generalize ht : ({ cmps := cs, thenOps := ts', elseOps := es' } : TxnModel) = t at hm ⊢
  have hg := txnGetsOk_of_check _ _ _ _ _ Hck hm Hin
  have hT := hTxn s E ρ γr c ci cd r t (opDepQ d) (rangeDepQ γr.kv d) none false F
  cases hro : txn.txnReadonly t
  · -- a writing transaction: through raft, as `Put`
    have hdp' : (∃ Q, d = .op1 (.txn t) Q) ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧
        ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es ∧ txn.OpsNoCut t.thenOps ∧
        txn.OpsNoCut t.elseOps := by
      rcases Hro t hm with ⟨h, -⟩ | h
      · rw [hro] at h; cases h
      · exact h
    obtain ⟨hq, hpl, hz, hsT, hsE, hnT, hnE⟩ := hdp'
    have hsh : txn.txnShape t := by
      subst ht
      exact txnShape_of_check n cs ts es ts' es' hts hes Hck HivT HivE ⟨hz.2.1, hz.2.2⟩
        ⟨hsT, hsE⟩ hpl ⟨hnT, hnE⟩
    ihave Hdep := txnPermit_of_dep ρ γr d t ⟨hq, hpl, hz⟩ hsh $$ Hdep
    simp only [hro, Bool.false_eq_true, ↓reduceIte] at hT
    wp_apply hT $$ [Hlt Hcred Hrc Hdep] as %resp %err ⟨Hlt, Hrc, Hres⟩
    · iframe #; iframe Hlt Hcred Hrc
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      iframe Hdep
      ipureintro; exact fun h => h.elim
    iapply HΦ
    iunfold kvAnswer
    icases Hres with (⟨%Herr, Hok'⟩ | ⟨%Hre, #HaE, Hfail⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold txnAppliedOk at Hok'
      simp only [apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
      icases Hok' with ⟨%hm', %rq', %t', %x, %x', %l, %skip, %Hst, ⟨#Hout, %Hnil⟩, Hhdr, #Hcert, HMint, #Hwit,
        #Hcok, HQv⟩
      ihave #Hresp := Hout
      iunfold txn.txnResponseIs at Hresp
      icases Hresp with ⟨-, #Hf⟩
      iunfold txn.txnRespFieldsIs at Hf
      icases Hf with ⟨%h, #Hhf, %Hhn, #Hrev, -⟩
      iunfold apply.appliedHdr at Hhdr
      icases Hhdr with ⟨Hown, %Hlen⟩
      ileft
      isplitr
      · ipureintro; exact ⟨by first | rfl | trivial, Hrn⟩
      iexists h, W64 (mvcc.writeRev x.log
        (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 : Int)
      ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
        (writeRev_ne_zero _ _ Hlen.1 Hlen.2) $$ [$Hown]
      · iframe #; ipureintro; exact Hhn
      iframe Hhf2 Hw Hri
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, Bool.false_eq_true, ↓reduceIte]
      iunfold txnAppliedAns
      iexists hm', rq', t', x, x', l, skip
      isplitr
      · ipureintro; exact ⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, Hst.2.2.2.2, Hlen.1, Hlen.2⟩
      simp only [apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
      iframe Hout Hcert HMint Hwit Hcok HQv
      try (ipureintro; trivial)
    · obtain ⟨-, Hne⟩ := Hre
      iright
      isplitr
      · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, Bool.false_eq_true, ↓reduceIte]
      iexact Hfail
  · -- a read-only transaction: read locally
    simp only [hro, ↓reduceIte] at hT
    ihave #Hdep' := kvDep_of_dep ρ γr d $$ Hdep
    wp_apply hT $$ [Hlt Hcred Hrc] as %resp %err ⟨Hlt, Hrc, Hcred, Hres⟩
    · iframe #; iframe Hlt Hcred Hrc
      isplitr
      · simp only [traceutil.ownTraceOpt]; itrivial
      ipureintro; exact fun _ => hg hro
    iapply HΦ
    iunfold kvAnswer
    icases Hres with (⟨%Herr, Hok'⟩ | ⟨%Hne, #HaE⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold txnReadOk at Hok'
      icases Hok' with ⟨%log, #Hcert, #Hcok, %Hlen, Hlin, HQl, #Hresp, Hown⟩
      ihave #Hresp' := Hresp
      iunfold txn.txnResponseIs at Hresp'
      icases Hresp' with ⟨-, #Hf⟩
      iunfold txn.txnRespFieldsIs at Hf
      icases Hf with ⟨%h, #Hhf, %Hhn, #Hrev, -⟩
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn⟩
      iexists h, W64 ((log.length : Int) - 1)
      ihave ⟨#Hhf2, Hw, Hri⟩ := hdr_of_own _ h _ (mvcc.storeReader E.s E.γ)
        (w64_last_ne_zero log Hlen.1 Hlen.2.1) $$ [$Hown]
      · iframe #; ipureintro; exact Hhn
      iframe Hhf2 Hw Hri
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, ↓reduceIte]
      iframe Hcred
      iunfold txnReadAns
      iexists log
      iframe Hcert Hcok Hresp Hlin HQl
      ipureintro; exact ⟨Hlen.1, Hlen.2.1, rfl, Hlen.2.2⟩
    · iright
      isplitr
      · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
      simp only
      iframe Hrc Hlt
      iexists t
      isplitr
      · ipureintro; exact hm
      simp only [hro, ↓reduceIte]
      iexact Hcred

/-- **`raftKV`'s getters, from the server's** (`KV().Rev()`: `store.Rev` on the bare store with
the store's reader slots, `revR`; `Cluster().ID()`, `MemberID`, `Term`, `Leader`). -/
theorem kvGetOk_of_server (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      kvGetOk s (srvKVAns s E ρ γr c F d) := by
  have hRev := mvcc.store.Rev.spec_frozen hRev
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hmb : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, #Hcl, #Htr, #Hpeers, -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨#Hcid, -, -⟩
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨-, -, #Hkvf, #Hkv, #Hrvf, #Hrv, -, -, -, -, -, -, -, #Hterm, -⟩
  ihave %Hkvok := txn.isKV_ok _ E.s E.γ $$ Hkv
  obtain ⟨kty, kvv, Hkveq⟩ := Hkvok
  ihave ⟨#Hko0, #Hst⟩ := txn.isKV_kvOver _ E.s E.γ $$ Hkv
  ihave #Hko : mvcc.kvOver (interface.mkOk kty kvv) E.s $$ []
  · rw [← Hkveq]; iexact Hko0
  iunfold kvGetOk
  simp only [srvKVAns]
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hKV s w.kv $$ []
    · iframe #
    iapply HΦ
    iexists ⟨kty, kvv⟩
    isplitr
    · ipureintro; exact Hkveq
    iintro !> %Φ' Hrd HΦ'
    imod ownToks_0 (GF := GF) E.γ.revs with Hnone
    imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #Hc0
    iapply mvcc.kvOver_rev_wp kty kvv E.s
    iframe Hko
    wp_apply hRev E.s w.rv E.γ 0 [] $$ [Hrd Hnone] as %rv ⟨Hrd, -, -⟩
    · iframe #; iframe Hrd Hnone
    iapply HΦ'
    iexact Hrd
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hCl s v.cluster $$ []
    · iframe #
    iapply HΦ
    iexists ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty, #v.cluster⟩
    isplitr
    · ipureintro; rfl
    iintro !> %Φ' - HΦ'
    wp_apply hID v.cluster v.cid $$ []
    · iframe #
    iapply HΦ'
    itrivial
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hMID s v.memberID $$ []
    · iframe #
    iapply HΦ
    itrivial
  iunfold raftStatusOk
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply hTerm s $$ []
    · iframe #
    iexact HΦ
  · iintro !> %Φ - HΦ
    wp_apply hLead s $$ []
    · iframe #
      iunfold srvLeadInv
      iunfold srvAtomicU64 at Hlead
      iexact Hlead
    iexact HΦ

/-- **The server's contract `raftKV`, from the server's linked specs** (no premise but the
server's facts: the request path's fields and invariants, `isServerReq`; the read side's,
`isServerRead`), at the parameters `srvKVAns s E ρ γr c`. -/
theorem raftKV_of_server (hPut : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (hDel : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG))
    (hRange : EtcdServer.Range.spec (GF := GF) (hG := hG))
    (hTxn : EtcdServer.Txn.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (d : KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      raftKV s (srvKVAns s E ρ γr c F d) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd⟩
  iunfold raftKV
  isplitr
  · iapply kvRangeOk_of_server hRange s E ρ γr c F d; iframe #
  isplitr
  · iapply kvPutOk_of_server hPut s E ρ γr c F d; iframe #
  isplitr
  · iapply kvDeleteOk_of_server hDel s E ρ γr c F d; iframe #
  isplitr
  · iapply kvTxnOk_of_server hTxn s E ρ γr c F d; iframe #
  iapply kvGetOk_of_server hKV hRev hCl hID hMID hTerm hLead s E ρ γr c F d; iframe #

end proofs


end v3rpc
end EtcdGrove
end Perennial
