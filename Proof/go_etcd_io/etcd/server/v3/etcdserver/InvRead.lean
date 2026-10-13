/-
The request path's read side (`v3_server.go`'s `Range`, the read-only `Txn`, `doSerialize`,
`LinearizableReadNotify`; the getters of the response header): the shared vocabulary of their
specs. Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12); plan:
`notes/decisions.md`, "The request path".

**The server, as a reader sees it** (`isServerRead s E γr`, persistent): the fields the read side
reads besides `isServerReq`'s: the read loop (`read`, its contract `isRead`), the KV (`kv`: the
bare store of the applier's environment `E`, the apply package's standing premise `txn.isKV`;
its `ReadView` for `KV().Rev()`), the lessor (`apply.isApplyLessor`: `CheckTxnAuth` and the
txn package's `checkTxn`), the auth store (`apply.isAuthStore`: `IsRangePermitted`,
`CheckTxnAuth`'s checks, `Revision`), the logger (`lg`, not nil), the configuration's
`WarningApplyDuration`, the term's atomic (`Term`), a certificate of a log of `NewStore`'s two
revisions (`idxCert`: every read is of a log at least that long, so a read's revision is not
`0`), the read loop's server fields (2026-10-13, the request path's unit 4b: the applied and
committed indices' invariants, `srvAppliedInv`/`srvCommittedInv`; the applied index's waiters
`applyWait`, a `WaitTime` for `appliedAtLeast γr`, `isWaitTime`; the notifiers `leaderChanged` and
`firstCommitInTerm`; the `stopping` channel, closed, never sent on), and **the store stays small** (`storeSmall`: every certified log has at most `2 ^ 62`
changes, `txn.LogSmall`, the sort's premise; a premise, as the apply thread's `rangeOk`/`TxnPre`
of its entries).

**A read call's resources** (`srvRdCall s E γr c`, ctx-independent): the store's reader slots
(`mvcc.storeReader`: its `RWMutex`es admit a bounded number of readers), a reader slot of the
logger's lock (`srvLgReader`), a lower bound `c` of the cluster's committed index the caller
knew of (`committedAtLeast`: what a linearizable read's `readIndexOk` is relative to), and a
reader slot of the read loop's lock (`srvReadReader`, 2026-10-13, unit 4a).

**The read side's answers**: a successful `Range` of `o` (`rangeReadOk`: the txn package's
`rangeResult` with no error at a certified log of at least two revisions, read after the read
index if linearizable, and extending the log applied through an index at least the caller's
committed index, `readLogOk`, unit 4b; the response header's id fields owned), a successful
read-only `Txn`
(`txnReadOk`); a successful writing `Txn` (`txnAppliedOk`, as `Put`'s and `DeleteRange`'s: the
apply thread's application of the request the proposed data decode to), its failure
(`txnErrOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeList

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvApplyWaitAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"applyWait" s
abbrev srvLeaderChangedAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"leaderChanged" s
abbrev srvStoppingAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"stopping" s

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The store stays small** (persistent; a premise): every certified log has at most `2 ^ 62`
changes (`txn.LogSmall`: the sort's premise, `sort.Sort`'s bound and the comparators'
non-negative values). -/
def storeSmall (γ : mvcc.StoreNames) : IProp GF :=
  iprop(□ ∀ log : mvcc.Log, mvcc.idxCert γ.idx log -∗ ⌜txn.LogSmall log⌝)

instance storeSmall_persistent (γ : mvcc.StoreNames) : Persistent (storeSmall (GF := GF) γ) := by
  unfold storeSmall; infer_instance

/-- The values of the server's fields the read side reads (besides `ReqFields`). -/
structure ReadFields where
  read : Loc
  kv : GoInterface
  lessor : GoInterface
  auth : GoInterface
  lg : Loc
  wad : w64
  rv : Loc
  aw : GoInterface
  lc : Loc
  fc : Loc
  stopping : Loc

/-- **The server `s` as a reader sees it** at the fields' values `v` (persistent; see the file
header). -/
def srvReadFieldsAt (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v : ReadFields) : IProp GF :=
  iprop(srvReadAddr s ↦□ v.read ∗ isRead v.read γr ∗
    srvKVAddr s ↦□ v.kv ∗ txn.isKV v.kv E.s E.γ ∗
    E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
        #v.rv : GoInterface) ∗
    mvcc.isReadView v.rv E.s E.γ ∗
    srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.γ E.P E.f ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.P E.f ∗
    srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ v.wad ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    storeSmall E.γ ∗
    (∃ log₀ : mvcc.Log, mvcc.idxCert E.γ.idx log₀ ∗ ⌜2 ≤ log₀.length⌝) ∗
    srvAppliedInv s E γr ∗ srvCommittedInv s γr ∗
    srvApplyWaitAddr s ↦□ v.aw ∗ isWaitTime v.aw (appliedAtLeast γr) ∗
    srvLeaderChangedAddr s ↦□ v.lc ∗ srvFirstCommitAddr s ↦□ v.fc ∗
    srvStoppingAddr s ↦□ v.stopping ∗ srvDoneChan v.stopping)

instance srvReadFieldsAt_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (v : ReadFields) : Persistent (srvReadFieldsAt s E γr v) := by
  unfold srvReadFieldsAt; infer_instance

/-- **The server `s`, as a reader sees it** (persistent). -/
def isServerRead (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ v : ReadFields, srvReadFieldsAt s E γr v)

instance isServerRead_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (isServerRead s E γr) := by
  unfold isServerRead; infer_instance

/-- **A reader slot of the server's read loop's lock** (`s.read.mux`, `readReader`; 2026-10-13, the
request path's unit 4a: `LinearizableReadNotify` read-locks it). -/
def srvReadReader (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ rd : Loc, srvReadAddr s ↦□ rd ∗ readReader rd γr)

/-- **The read loop's server resource** `LR` (2026-10-13, the request path's unit 4b): the
`Logger()`'s reader slot of `s.lgMu`, and a reader slot of each notifier the read loop receives
from (`LeaderChanged()`, `FirstCommitInTermNotify()`: `Receive` read-locks it). -/
def srvReadLR (s : Loc) : IProp GF :=
  iprop(srvLgReader s ∗ (∃ n : Loc, srvLeaderChangedAddr s ↦□ n ∗ notifyReader n) ∗
    (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n))

/-- **A read call's resources** (see the file header): the store's reader slots, a reader slot
of `s.lgMu`, the committed index `c` the caller knew of, and (2026-10-13, unit 4a) a reader slot
of the read loop's lock (`srvReadReader`). -/
def srvRdCall (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ committedAtLeast γr c ∗ srvReadReader s γr)

/-- **A linearizable read of `log` after the committed index `c`** (persistent; 2026-10-13, the
request path's unit 4b): the read index (`readIndexOk`: the applied index reached some index at
least `c`), and `log` extends the log applied through some index `ci₀ ≥ c` (`appliedLogAt`: the
apply thread's log right after the entry at `ci₀`, deposited by `setAppliedIndex`; see
`notes/decisions.md`, "The applied index: a certified log per index"). -/
def readLogOk (γr : ReadNames) (c : w64) (log : mvcc.Log) : IProp GF :=
  iprop(readIndexOk γr c ∗ ∃ (ci₀ : w64) (L₀ : mvcc.Log), ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗
    appliedLogAt γr ci₀ L₀ ∗ ⌜L₀ <+: log⌝)

instance readLogOk_persistent (γr : ReadNames) (c : w64) (log : mvcc.Log) :
    Persistent (readLogOk (GF := GF) γr c log) := by
  unfold readLogOk; infer_instance

/-- **A successful `Range` of `o`** with the response `resp`: the txn package's answer with no
error (`rangeResult`: the server's selection of the state at the revision read) at a certified
log `log` of at least `NewStore`'s two revisions (so the header's revision, `log`'s last, is not
`0`), read after the read index if the request is linearizable (`readLogOk γr c log`: the applied
index reached the committed index `c` the caller knew of, and `log` extends the log applied through
an index at least `c`; 2026-10-13, unit 4b: `readIndexOk` until then), the response header's id
fields owned. -/
def rangeReadOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull) (resp : Loc) :
    IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp))

/-- **A successful read-only `Txn` of `t`** (as `rangeReadOk`): the server's run of `t` on the
state after a certified log `log` (`srvRunTxn`: its verdict and results, no change), the
response's header revision `log`'s last, read after the read index unless every get is
serializable (`txnSerializable`; `readLogOk`, as `rangeReadOk`'s), the header's id fields owned. -/
def txnReadOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (t : TxnModel) (resp : Loc) :
    IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗
    (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
    txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))

/-- **A successful writing `Txn` of `t`** (as `Put`'s and `DeleteRange`'s): the request the
proposed data decode to (`rq'`, whose transaction `t'` is `t` unless a range end is `[0]`,
`irrWireOf`) was dispatched by the apply thread at the KV state `x` to `x'` and applied
(`applied l false`), possibly with header-only ranges (`skip`: `SkipRangeExecution`, the apply
thread's `IsRegistered` being "some boolean" in the wait's contract), the response the
transaction's (`txnOutcomeIs` at `x.log`), the header's id fields owned (`appliedHdr`), mvcc's
certificate of the log after. -/
def txnAppliedOk (E : apply.AEnv GF) (t : TxnModel) (resp : Loc) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (t' : TxnModel)
      (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq' ∧ rq'.txn = some t' ∧
      (irrNoZeroEnd (irrTxn t) → t' = t) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)⌝ ∗
    apply.txnOutcomeIs x.log t' skip resp GoInterface.nil (.applied l false) ∗
    apply.appliedHdr x.log (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
    mvcc.idxCert E.γ.idx x'.log)

/-- **A failed writing `Txn` of `t`** (as `Put`'s): the apply thread's error (`appliedErr`), or
the proposal's (made or not; if made, deposited: it may still be applied). -/
def txnErrOk (E : apply.AEnv GF) (ρ : ReqNames) (t : TxnModel) (err : GoInterface) : IProp GF :=
  iprop((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
      ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq'⌝ ∗ appliedErr E rq' err) ∨
    srvMaybeDeposited ρ (irrTxn t))

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]

/-- `readLogOk` holds of every extension of the log. -/
theorem readLogOk_if_mono (b : Bool) (γr : ReadNames) (c : w64) (log log' : mvcc.Log)
    (h : log <+: log') :
    (if b then iprop(True) else readLogOk (GF := GF) γr c log) ⊢
      (if b then iprop(True) else readLogOk γr c log') := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold readLogOk
    iintro ⟨#Hri, %ci₀, %L₀, %Hc, #HL, %Hp⟩
    iframe Hri
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨Hc, Hp.trans h⟩
  · simp only [↓reduceIte]
    iintro -; itrivial

/-- **The linearizable read's log** (`Range`'s and the read-only `Txn`'s, after
`LinearizableReadNotify`): from the read index and the applied index's invariant, a certified log
extending both the reader's `log₀` and the log applied through some index `ci₀ ≥ c`, which
`txn.Range`/`txn.Txn` take as their lower bound (`log₀`). -/
theorem readIndexOk_logR [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (log₀ : mvcc.Log) :
    ⊢ srvAppliedInv s E γr -∗ readIndexOk γr c -∗ mvcc.idxCert E.γ.idx log₀ ={⊤}=∗
      ∃ logR : mvcc.Log, mvcc.idxCert E.γ.idx logR ∗ ⌜log₀ <+: logR⌝ ∗ readLogOk γr c logR := by
  iintro #Hinv #Hri #Hc0
  imod readIndexOk_log s E γr c $$ Hinv Hri with ⟨%ci₀, %L₀, %Hci, #HL, #HcL⟩
  ihave %Hpre := mvcc.idxCert_prefix E.γ.idx log₀ L₀ $$ [Hc0 HcL]
  · iframe Hc0 HcL
  imodintro
  rcases Hpre with h | h
  · iexists L₀
    iframe HcL
    isplitr
    · ipureintro; exact h
    iunfold readLogOk
    iframe Hri
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨Hci, List.prefix_refl _⟩
  · iexists log₀
    iframe Hc0
    isplitr
    · ipureintro; exact List.prefix_refl _
    iunfold readLogOk
    iframe Hri
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨Hci, h⟩

/-- **A `fmt.Errorf` error is one the gRPC layer can take** (`applyErrIs`), given the method-set
fact that `*errors.errorString` is a leaf error type (the server's package facts, `srvErrVars`). -/
theorem applyErrIs_errorf (err : GoInterface)
    (hleaf : ∀ x : Loc, errLeaf ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩) :
    mvcc.errorfIs (GF := GF) err ⊢ applyErrIs err := by
  iunfold mvcc.errorfIs
  iintro ⟨%x, %h, #He⟩
  subst h
  iapply applyErrIs_leaf _ (hleaf x)
  iunfold errMsgOk
  iintro !> %Φ - HΦ
  iapply He
  inext
  iintro %str
  iapply HΦ
  itrivial

end lemmas

end EtcdGrove
end Perennial
