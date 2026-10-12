/-
The server's transactions in the heap (txn unit 3): the transaction `Txn` writes through, the
responses of a transaction, the skeleton `newTxnResp` allocates, the leases a run may attach.
Lean-first; see `TxnRun.lean` (the pure run) and `notes/decisions.md`, "The server's txn", unit 3.

**The transaction** (`txnViewIs tw s γ kind ro`): the `mvcc.TxnWrite`/`ReadView` interface value
`tw` is a transaction of the store behind a `*metricsTxnWrite` (`ro = false`: `store.Read`'s or
`store.Write`'s, `isTxn` of either kind), or (`ro = true`) the read-only wrapper
`NewReadOnlyTxnWrite` makes of a read transaction (`isRoTxnWrite`, of kind `.read log rev`).
`executeRange` runs on any of them; `executeTxn` on a write transaction or the wrapper
(`txnWriteIs`: of the committed log `ilog` with the pending changes `pend`, none for the
wrapper).

**The responses** (`responseOpIs`, `responseOpsIs`, `txnRespFieldsIs`, `txnResponseIs`; moved
from `Requests.lean`, unit 0's, and changed): they mirror `TxnOpResult`. A range's response is the
server's (`RangeModel.lean`): its key-values are the client's `rangeKvsOk` of the selection up to
the lease of a fast keys-only read (`leaseZ`, `issues/etcd-range-keys-only-lease.md`), its count
the result's; or (`skip`, `skipRangeExecution`) header-only: no key-values, `More` false, count
`0`. A put's and a delete's headers and previous key-values are any (`PrevKv` is outside
`TxnOpResult`); a delete has its count; a nested transaction its own outcome and results, with a
header of revision `0` (only the outer response's revision is set).

**The skeleton** (`opSkel`, `opsSkel`, `respsSkel`; `newTxnResp`'s result, `executeTxn`'s
input): every `ResponseOp` with the wrapper of its operation's kind (read-only), the wrapper's
response field `nil` and owned (`executeTxn` stores the response there); a nested transaction's
`TxnResponse` complete but for its operations' responses, its `Succeeded` the verdict at the read
state `s0` (the path).

**Leases** (`leasesOk γl ls`, `leasesKnown γl s`): every lease of `ls` (of the key-values of `s`)
is none or one the lessor granted (`leaseOk`); `checkTxn` establishes it for the leases the path's
puts name (`opsLeases`), and `executeTxn` keeps it for the state (an `IgnoreLease` put writes the
previous key-value's lease).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnRun
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-! ## The transaction -/

/-- **The transaction `tw`** (an `mvcc.TxnWrite` or `mvcc.ReadView`): a transaction of `kind`
behind a `*metricsTxnWrite`, or (`ro`) the read-only wrapper of a read transaction of `kind`. -/
def txnViewIs (tw : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (ro : Bool) :
    IProp GF :=
  if ro then
    iprop(∃ (trw : Loc) (log : mvcc.Log) (rev : w64),
      ⌜tw = interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw ∧ kind = .read log rev⌝ ∗
      mvcc.isRoTxnWrite trw s γ log rev)
  else
    iprop(∃ mw : Loc, ⌜tw = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝ ∗
      mvcc.isTxn mw s γ kind)

/-- The kind of `executeTxn`'s transaction: a write transaction of `ilog` with `pend` pending,
or (`ro`) a read transaction of `ilog` (nothing pending). -/
def KindIs (ro : Bool) (ilog : mvcc.Log) (pend : List mvcc.Change) (kind : mvcc.TxnKind) : Prop :=
  if ro then pend = [] ∧ ∃ rev, kind = .read ilog rev
  else ∃ puts deletes putSize, kind = .write ilog pend puts deletes putSize

/-- **`executeTxn`'s transaction**: a write transaction of the committed log `ilog` with the
pending changes `pend`, or (`ro`) the read-only wrapper of a read transaction of `ilog`. -/
def txnWriteIs (tw : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (ro : Bool) (ilog : mvcc.Log)
    (pend : List mvcc.Change) : IProp GF :=
  iprop(∃ kind : mvcc.TxnKind, txnViewIs tw s γ kind ro ∗ ⌜KindIs ro ilog pend kind⌝)

/-! ## The responses -/

mutual
/-- **The `*pb.ResponseOp` `p` is the response of the operation `op` with result `res`**
(read-only; `skip`: ranges answered header-only). -/
def responseOpIs (skip : Bool) (p : Loc) : TxnOp → TxnOpResult → IProp GF
  | .txn _ ts es, .txn ok rs => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ r ∗
      ⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.TxnResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ (W64 0 : w64) ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" r ↦□ ok ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" r ↦□ sl ∗ sl ↦*□ ps ∗
      match ok with
      | true => responseOpsIs skip ps ts rs
      | false => responseOpsIs skip ps es rs))
  | op, res => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (u : GoInterface) (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□ u ∗
      match op, res with
      | .get o, .range sel n => iprop(
          ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty)
            #w⌝ ∗
          structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ r ∗
          ∃ rev : w64,
            if skip then rangeResponseIs r rev [] false (W64 0)
            else ∃ (kvs : List EtcdKv) (more : Bool),
              rangeResponseIs r rev kvs more (W64 (n : Int)) ∗
              ⌜∃ kvs', rangeKvsOk o sel kvs' ∧ kvs = kvs'.map (leaseZ (fastKeysOnly o))⌝)
      | .put _ _ _, .put | .putKeep _ _, .put | .putIgnVal _ _, .put => iprop(
          ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty)
            #w⌝ ∗
          structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ r ∗
          ∃ (rev : w64) (prev : Option EtcdKv), putResponseIs r rev prev)
      | .delete _, .delete n => iprop(
          ⌜u = interface.mkOk
            (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w⌝ ∗
          structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w
            ↦□ r ∗
          ∃ (rev : w64) (prevs : List EtcdKv), deleteRangeResponseIs r rev n prevs)
      | _, _ => iprop(False)))

/-- The `*pb.ResponseOp`s `ps` are, in order, the responses of `ops` with results `rs`. -/
def responseOpsIs (skip : Bool) : List Loc → List TxnOp → List TxnOpResult → IProp GF
  | [], [], [] => iprop(True)
  | p :: ps, op :: ops, res :: rs => iprop(responseOpIs skip p op res ∗ responseOpsIs skip ps ops rs)
  | _, _, _ => iprop(False)

end

instance responseOpIs_persistent (skip : Bool) (p : Loc) (op : TxnOp) (res : TxnOpResult) :
    Persistent (responseOpIs (GF := GF) skip p op res) := by
  cases op <;> cases res <;> unfold responseOpIs <;> infer_instance

instance responseOpsIs_persistent (skip : Bool) (ps : List Loc) (ops : List TxnOp)
    (rs : List TxnOpResult) : Persistent (responseOpsIs (GF := GF) skip ps ops rs) := by
  induction ops generalizing ps rs with
  | nil => cases ps <;> cases rs <;> unfold responseOpsIs <;> infer_instance
  | cons op ops ih => cases ps <;> cases rs <;> unfold responseOpsIs <;> infer_instance

/-- The `Responses` of the `*pb.TxnResponse` `resp` are those of `ops` with results `rs`. -/
def respsIs (skip : Bool) (resp : Loc) (ops : List TxnOp) (rs : List TxnOpResult) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    responseOpsIs skip ps ops rs)

instance respsIs_persistent (skip : Bool) (resp : Loc) (ops : List TxnOp) (rs : List TxnOpResult) :
    Persistent (respsIs (GF := GF) skip resp ops rs) := by
  unfold respsIs; infer_instance

/-- The fields of the `*pb.TxnResponse` `resp` (read-only): header revision `rev`,
`Succeeded` is `ok`, and its `Responses` are those of the chosen branch's `ops` with results
`rs`. -/
def txnRespFieldsIs (skip : Bool) (resp : Loc) (rev : w64) (ok : Bool) (ops : List TxnOp)
    (rs : List TxnOpResult) : IProp GF :=
  iprop(∃ h : Loc,
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ ok ∗
    respsIs skip resp ops rs)

instance txnRespFieldsIs_persistent (skip : Bool) (resp : Loc) (rev : w64) (ok : Bool)
    (ops : List TxnOp) (rs : List TxnOpResult) :
    Persistent (txnRespFieldsIs (GF := GF) skip resp rev ok ops rs) := by
  unfold txnRespFieldsIs; infer_instance

/-- **The `*pb.TxnResponse` `resp`** of the transaction `t` (not nil, read-only): header
revision `rev`, `Succeeded` is `ok`, and its responses are those of the branch `ok` chooses
with results `rs` (`skip`: ranges header-only). -/
def txnResponseIs (skip : Bool) (resp : Loc) (rev : w64) (t : TxnModel) (ok : Bool)
    (rs : List TxnOpResult) : IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ txnRespFieldsIs skip resp rev ok (t.branch ok) rs)

instance txnResponseIs_persistent (skip : Bool) (resp : Loc) (rev : w64) (t : TxnModel) (ok : Bool)
    (rs : List TxnOpResult) : Persistent (txnResponseIs (GF := GF) skip resp rev t ok rs) := by
  unfold txnResponseIs; infer_instance

/-! ## The skeleton -/

/-- A put's skeleton. -/
def putSkel (p : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ w : Loc,
    structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
      (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w :
        GoInterface) ∗
    structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦ (null : Loc))

mutual
/-- **`newTxnResp`'s `*pb.ResponseOp` `p` for the operation `op`** (nested verdicts at `s0`):
the wrapper of its kind, its response field `nil` and owned; a nested transaction's response
complete but for its operations'. -/
def opSkel (s0 : List EtcdKv) (p : Loc) : TxnOp → IProp GF
  | .txn cs ts es => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ r ∗
      ⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.TxnResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ (W64 0 : w64) ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" r ↦□ (cs.all (cmpHolds s0)) ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" r ↦□ sl ∗ sl ↦*□ ps ∗
      match cs.all (cmpHolds s0) with
      | true => opsSkel s0 ps ts
      | false => opsSkel s0 ps es)
  | .get _ => iprop(⌜p ≠ null⌝ ∗ ∃ w : Loc,
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦ (null : Loc))
  | .put _ _ _ => putSkel p
  | .putKeep _ _ => putSkel p
  | .putIgnVal _ _ => putSkel p
  | .delete _ => iprop(⌜p ≠ null⌝ ∗ ∃ w : Loc,
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w ↦
        (null : Loc))

/-- The skeletons of `ops`, in order. -/
def opsSkel (s0 : List EtcdKv) : List Loc → List TxnOp → IProp GF
  | [], [] => iprop(True)
  | p :: ps, op :: ops => iprop(opSkel s0 p op ∗ opsSkel s0 ps ops)
  | _, _ => iprop(False)

end

/-- The `Responses` of the `*pb.TxnResponse` `resp`: the skeletons of `ops`. -/
def respsSkel (s0 : List EtcdKv) (resp : Loc) (ops : List TxnOp) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    opsSkel s0 ps ops)

/-- **`newTxnResp`'s result** for `t` (verdict `ok`): not nil, its header's revision `0` and
owned (`txn` sets it), `Succeeded` is `ok`, the skeletons of the branch's operations. -/
def txnSkel (s0 : List EtcdKv) (resp : Loc) (ok : Bool) (ops : List TxnOp) : IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ h : Loc,
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ (W64 0 : w64) ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ ok ∗
    respsSkel s0 resp ops)

/-! ## Leases -/

/-- Every lease of `ls` is none or one the lessor granted. -/
def leasesOk (γl : GName) (ls : List w64) : IProp GF :=
  iprop(□ ∀ l : w64, ⌜l ∈ ls⌝ -∗ leaseOk γl l)

instance leasesOk_persistent (γl : GName) (ls : List w64) :
    Persistent (leasesOk (GF := GF) γl ls) := by
  unfold leasesOk; infer_instance

/-- **Every lease of the state `s` is known** (none, or granted). -/
def leasesKnown (γl : GName) (s : List EtcdKv) : IProp GF := leasesOk γl (s.map EtcdKv.lease)

instance leasesKnown_persistent (γl : GName) (s : List EtcdKv) :
    Persistent (leasesKnown (GF := GF) γl s) := by
  unfold leasesKnown; infer_instance

/-! ## `checkTxn`'s errors -/

/-- **One of `checkTxn`'s errors**: `lease.ErrLeaseNotFound`, `errors.ErrKeyNotFound` (a put's
check), mvcc's `ErrFutureRev` or `ErrCompacted` (a range's). -/
def checkErrIs (err : GoInterface) : IProp GF :=
  iprop(errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∨
    errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound err ∨
    (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗
      ⌜err = GoInterface.ok ef⌝) ∨
    (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗
      ⌜err = GoInterface.ok ec⌝))

instance checkErrIs_persistent (err : GoInterface) : Persistent (checkErrIs (GF := GF) err) := by
  unfold checkErrIs; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- The sort's premise from unit 2's (`sortOk`, a small log). -/
theorem sortSmall_of_sortOk (o : OpFull) (log : mvcc.Log) (hok : LogOk log) (r : Nat)
    (h : sortOk o log) : sortSmall o (mvcc.stateAt log r) := by
  intro hs
  exact srvPre_small o _ (stateAt_small log hok.len (h hs) _)

/-- A transaction behind a `*metricsTxnWrite`. -/
theorem txnViewIs_mw (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) :
    txnViewIs (GF := GF) (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) s γ kind
      false ⊣⊢ mvcc.isTxn mw s γ kind := by
  unfold txnViewIs
  simp only [Bool.false_eq_true, ↓reduceIte]
  constructor
  · iintro ⟨%mw', %h, H⟩
    have := mvcc.mkOk_loc_inj _ h
    subst this
    iexact H
  · iintro H
    iexists mw
    iframe H
    ipureintro; rfl

/-- The read-only wrapper of a read transaction. -/
theorem txnViewIs_ro (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) :
    txnViewIs (GF := GF) (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) s γ
      (.read log rev) true ⊣⊢ mvcc.isRoTxnWrite trw s γ log rev := by
  unfold txnViewIs
  simp only [↓reduceIte]
  constructor
  · iintro ⟨%trw', %log', %rev', %h, H⟩
    obtain ⟨h1, h2⟩ := h
    have := mvcc.mkOk_loc_inj _ h1
    subst this
    cases h2
    iexact H
  · iintro H
    iexists trw, log, rev
    iframe H
    ipureintro; exact ⟨rfl, rfl⟩

/-- The read-only wrapper's read transaction: a well-formed log, read at its last revision. -/
theorem isRoTxnWrite_pure (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) :
    mvcc.isRoTxnWrite (GF := GF) trw s γ log rev ⊢
      mvcc.isRoTxnWrite trw s γ log rev ∗ ⌜LogOk log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ := by
  iintro H
  iunfold mvcc.isRoTxnWrite at H
  icases H with ⟨%mw, Hf, Htx⟩
  icases isTxnRead_pure mw s γ log rev $$ Htx with ⟨Htx, %Hp⟩
  isplitl
  · iunfold mvcc.isRoTxnWrite
    iexists mw
    iframe
  · ipureintro; exact Hp

/-- A read transaction at its log's last revision is `KindOk`. -/
theorem kindOk_read (log : mvcc.Log) (rev : w64)
    (h : LogOk log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)) : KindOk (.read log rev) := by
  obtain ⟨hok, hne, hrev⟩ := h
  have hpos := List.length_pos_iff.2 hne
  have hz := lastRev_sint log.length hpos (by have := hok.len; omega)
  refine ⟨hok, ?_, ?_⟩ <;> simp only [mvcc.TxnKind.readRev, mvcc.TxnKind.readLog] <;> rw [hrev, hz] <;> omega

theorem leasesOk_append (γl : GName) (a b : List w64) :
    leasesOk (GF := GF) γl (a ++ b) ⊣⊢ leasesOk γl a ∗ leasesOk γl b := by
  unfold leasesOk
  constructor
  · iintro #H
    isplitl
    · imodintro; iintro %l %hl; iapply H $$ %l; ipureintro; exact List.mem_append_left _ hl
    · imodintro; iintro %l %hl; iapply H $$ %l; ipureintro; exact List.mem_append_right _ hl
  · iintro ⟨#Ha, #Hb⟩
    imodintro
    iintro %l %hl
    rcases List.mem_append.1 hl with h | h
    · iapply Ha $$ %l; ipureintro; exact h
    · iapply Hb $$ %l; ipureintro; exact h

theorem leasesOk_nil (γl : GName) : ⊢ leasesOk (GF := GF) γl [] := by
  unfold leasesOk
  imodintro
  iintro %l %hl
  simp at hl

theorem leasesOk_one (γl : GName) (l : w64) : leaseOk (GF := GF) γl l ⊢ leasesOk γl [l] := by
  unfold leasesOk
  iintro #H
  imodintro
  iintro %l' %hl
  simp only [List.mem_singleton] at hl
  subst hl
  iexact H

/-- A lease of the list. -/
theorem leasesOk_mem (γl : GName) (ls : List w64) (l : w64) (h : l ∈ ls) :
    leasesOk (GF := GF) γl ls ⊢ leaseOk γl l := by
  unfold leasesOk
  iintro #H
  iapply H $$ %l
  ipureintro; exact h

/-- Fewer leases. -/
theorem leasesOk_sub (γl : GName) (ls ls' : List w64) (h : ∀ l ∈ ls', l ∈ ls) :
    leasesOk (GF := GF) γl ls ⊢ leasesOk γl ls' := by
  unfold leasesOk
  iintro #H
  imodintro
  iintro %l %hl
  iapply H $$ %l
  ipureintro; exact h l hl

/-- **The lease a put writes is known**: one its request names (checked), or the previous
key-value's (known with the state). -/
theorem leaseOk_put (γl : GName) (s0 s : List EtcdKv) (o : OpFull) :
    leasesOk (GF := GF) γl (opLeases s0 (putTxnOp o)) ∗ leasesKnown γl s ⊢
      leaseOk γl (putLeaseOf o (mvcc.findKey o.key s)) := by
  iintro ⟨#Hl, #Hk⟩
  rcases putLeaseOf_mem s0 o s with h | ⟨-, h⟩
  · iapply leasesOk_mem γl _ _ h $$ Hl
  · rw [h]
    cases hf : mvcc.findKey o.key s with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      unfold leaseOk; ileft; ipureintro; rfl
    | some v =>
      simp only [Option.map_some, Option.getD_some]
      iunfold leasesKnown at Hk
      iapply leasesOk_mem γl _ _ ?_ $$ Hk
      exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)

/-- A put keeps the state's leases known. -/
theorem leasesKnown_put (γl : GName) (r : w64) (s : List EtcdKv) (k v : GoString) (l : w64) :
    leasesKnown (GF := GF) γl s ∗ leaseOk γl l ⊢ leasesKnown γl (putKv r k v l s) := by
  unfold leasesKnown leasesOk
  iintro ⟨#Hk, #Hl⟩
  imodintro
  iintro %l' %hl'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl'
  rcases putKv_mem hx with h | ⟨w, -, rfl⟩ | rfl
  · iapply Hk $$ %x.lease; ipureintro; exact List.mem_map_of_mem h
  · simp only [bumpKv]; iexact Hl
  · simp only [newKv]; iexact Hl

/-- Fewer key-values keep the leases known. -/
theorem leasesKnown_sub (γl : GName) (s s' : List EtcdKv) (h : ∀ v ∈ s', v ∈ s) :
    leasesKnown (GF := GF) γl s ⊢ leasesKnown γl s' := by
  unfold leasesKnown
  apply leasesOk_sub
  intro l hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact List.mem_map_of_mem (h x hx)

theorem opsSkel_length (s0 : List EtcdKv) :
    ∀ (ps : List Loc) (ops : List TxnOp), opsSkel (GF := GF) s0 ps ops ⊢ ⌜ps.length = ops.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | p :: ps, op :: ops => by
    unfold opsSkel
    iintro ⟨-, H⟩
    ihave %h := opsSkel_length s0 ps ops $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by unfold opsSkel; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold opsSkel; iintro H; iexfalso; iexact H

end lemmas

end txn
end EtcdGrove
end Perennial
