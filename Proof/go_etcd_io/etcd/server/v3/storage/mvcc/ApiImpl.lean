/-
mvcc's candidate API's implementation (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`,
`notes/mvcc-api-proof-plan.md`, stage P4): the names of a store in the abstract mode
(`StoreNames.absQ`), and the predicates the API's vocabulary is defined as.

- **The client's state** (`mvccStateI`): the client's halves of the abstract committed log
  (`γ.abs`, of which `s.revMu`'s resource and the writer's state hold a quarter each:
  `absAt`, `wrAt`) and of the pending revision (`γ.pnd`, the writer's the other half), half the
  compaction revision's authority (the old mode's compaction right), the index's certificate of the
  log, and the committed logs' certificate map (`γ.cok`, the caller's in the old mode too): its
  entries are the notified history's prefixes, so that every log the implementation certifies
  (`certOk`: a read's, a watch event's) is one, by a pure entailment.
- **The store** (`isMvccI`): today's `isStore`, in the abstract mode, a persistent pin of its
  objects (the abstract mode has no `Restore` yet: they are fixed), the readers' tickets in a thread
  pool (`threadPool`: a call deposits its thread token for one), the revision tokens in a pool
  paid by time receipts, and the write-back tokens' receipt-paid supply.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Perennial.Proof.ThreadPool
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RdCode
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The names of a store of the candidate API**: today's store names (in the abstract mode),
the readers' pool's loans, and whether the store has watchers. -/
structure MvccImpl where
  /-- the watchable store's names (`WsNames`; its store's, `st`, for a store without watchers too) -/
  ws : WsNames
  /-- the readers' tickets' thread pool (`threadPool.isThreadPool`) -/
  tl : GName
  watched : Bool
  /-- the watchable store's location (a store with watchers; not read otherwise) -/
  wl : Loc
  /-- the store's location (`isMvccI` pins it: a transaction's store is the names') -/
  sl : Loc
  /-- the store's open token (`ghostVar Unit`, fractional: `mvccOpen`) -/
  op : GName

/-- The store's names. -/
abbrev MvccImpl.st (γ : MvccImpl) : StoreNames := γ.ws.st

/-- **The certificate map is the notified history's**: each entry, at its log's length, is a
prefix of the notified history, not empty. -/
def certMapOk (M : GMap w64 Log) (L : Log) : Prop :=
  ∀ (n : w64) (l : Log), M.lookup n = some l → l ≠ [] ∧ n = W64 (l.length : Int) ∧ l <+: L

/-- A reachable state's compaction revision is at least `-1`. -/
theorem MvccReachable.crev_ge {σ : MvccState} (h : MvccReachable σ) : -1 ≤ σ.crev := by
  induction h with
  | start => simp [mvccStart]
  | notify σ pend _ _ _ ih => simpa [MvccState.notify] using ih
  | commit σ _ ih => simpa [MvccState.commitPending] using ih
  | compact σ r _ _ hlt _ ih => simp only [MvccState.compactTo]; omega

/-- A reachable state's log has the first two revisions. -/
theorem MvccReachable.len_ge {σ : MvccState} (h : MvccReachable σ) : 2 ≤ σ.log.length := by
  induction h with
  | start => simp [mvccStart]
  | notify σ pend _ _ _ ih => simpa [MvccState.notify] using ih
  | commit σ _ ih =>
    simp only [MvccState.commitPending, commitLog]
    split
    · exact ih
    · simp only [List.length_append, List.length_singleton]; omega
  | compact σ r _ _ _ _ ih => simpa [MvccState.compactTo] using ih

/-- The readers' pool's namespace. -/
def tixN : Namespace := mvccN .@ "tix"

/-- The revision tokens' pool's namespace. -/
def revPoolN : Namespace := mvccN .@ "rev"

/-- The number of reader tickets `NewStore` hands out. -/
def nTix (γ : StoreNames) : Nat := nReaders - nJobRd γ.kb

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The client's state is `σ`** (`mvccState`): see the file's header. -/
def mvccStateI (γ : MvccImpl) (σ : MvccState) : IProp GF :=
  iprop(ghostVar γ.st.abs (1 : Qp).half σ.log ∗ ghostVar γ.st.pnd (1 : Qp).half σ.pending ∗
    (if γ.st.cm then crevUB γ.st.idx (1 : Qp).half σ.crev else iprop(⌜σ.crev = -1⌝)) ∗
    idxCert γ.st.idx σ.log ∗
    (∃ M : GMap w64 Log, ghostMapAuth γ.st.cok 1 M ∗ ⌜certMapOk M σ.notifiedLog⌝) ∗
    □ (∀ x, ⌜σ.pending = some x⌝ -∗ certOk γ.st (σ.log ++ [x])) ∗
    (if γ.watched then monoListAuthOwn γ.ws.wlog (1 : Qp).half σ.log else iprop(True)) ∗
    ⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝)

/-- **The revision tokens' pool**: `n` tokens and `a` time receipts, `receiptBound GF ≤ a + n + 1`
(a writer pays a receipt for a token: so the pool never runs dry, `revPool_take`). -/
def revPool (γ : StoreNames) : IProp GF :=
  inv revPoolN iprop(∃ (a n : Nat), ⧗ a ∗ ownToks γ.revs n ∗ ⌜receiptBound GF ≤ a + n + 1⌝)

instance revPool_persistent (γ : StoreNames) : Persistent (revPool (GF := GF) γ) := by
  unfold revPool; infer_instance

open Iris.ProofMode in
/-- **A revision token for a receipt**: the pool's receipts and tokens are more than the bound, so
with one more receipt (fewer than the bound) it has a token. -/
theorem revPool_take (γ : StoreNames) : revPool (GF := GF) γ ∗ ⧗ 1 ⊢ |={⊤}=> revToken γ := by
  iintro ⟨#Hinv, Hr⟩
  unfold revPool
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%a, %n, >Ha, >Hn, >%Hb⟩
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  icases (ownToks_add 1 n' γ.revs).1 $$ Hn with ⟨Hn, H1⟩
  imod Hclose $$ [Ha Hn] with _
  · inext; iexists a + 1, n'; iframe; ipureintro; omega
  imodintro
  unfold revToken; iframe

/-- The watch tokens' pool's namespace. -/
def wtPoolN : Namespace := nroot .@ "mvccWtPool"

/-- **The watch tokens' pool** (a store with watchers: a registration spends one, `watchToks`), as
the revision tokens' (`revPool`): paid by receipts. -/
def wtPool (γ : WsNames) : IProp GF :=
  inv wtPoolN iprop(∃ (a n : Nat), ⧗ a ∗ watchToks γ n ∗ ⌜receiptBound GF ≤ a + n + 1⌝)

instance wtPool_persistent (γ : WsNames) : Persistent (wtPool (GF := GF) γ) := by
  unfold wtPool; infer_instance

/-- The open token's namespace. -/
def mvccOpenN : Namespace := nroot .@ "mvccOpen"

/-- **A copy of the readers' pool**: the store's reader ticket and, on a store with watchers, a reader
slot of the watchable store's lock (`watchReader`'s). -/
def poolX (γ : MvccImpl) : IProp GF :=
  if γ.watched then sync.ownRWMutex (wsMuAddr γ.wl) (watchStoreInv γ.wl γ.ws) else iprop(True)

def poolR (s : Loc) (γ : MvccImpl) : IProp GF := iprop(storeReaderC s γ.st ∗ poolX γ)

/-- **A transaction's loan** from the readers' pool: the pool's loan token, and the part of the
copy the store's transactions do not use (`poolX`: the watchable store's reader slot). -/
def mvccLoan (γ : MvccImpl) : IProp GF := iprop(threadPool.ownThreadLoan γ.tl ∗ poolX γ)

/-- **The store `s` of the names `γ`** (`isMvcc`): see the file's header. -/
def isMvccI (s : Loc) (γ : MvccImpl) : IProp GF :=
  iprop(isStore s γ.st ∗
    ⌜γ.st.absQ = true ∧ γ.st.watchQ = γ.watched ∧ (∃ d, γ.st.kb = some d) ∧
      threadBound GF ≤ 2 ^ 30 ∧ γ.sl = s⌝ ∗
    (∃ o : StoreObjs, curAt γ.st DFrac.discard o) ∗
    threadPool.isThreadPool tixN γ.tl (poolR s γ) ∗ revPool γ.st ∗
    □ (⧗ 1 ={⊤}=∗ storeWT γ.st) ∗ wsFrozenM γ.st ∗
    (if γ.watched then wtPool γ.ws else iprop(True)) ∗
    (if γ.watched then isWatchableStore γ.wl s γ.ws else iprop(True)))

instance isMvccI_persistent (s : Loc) (γ : MvccImpl) : Persistent (isMvccI (GF := GF) s γ) := by
  unfold isMvccI; infer_instance

/-- **The store's backend is `b`** (`mvccBackendIs`): the real backend, of the parameters `BP`,
batch-lock invariant `Pk`, and the store's record of that invariant (`hookP`, `NewStore`'s). -/
def mvccBackendIsI (γ : MvccImpl) (BP : backend.BParams) (Pk : IProp GF) (b : Loc) : IProp GF :=
  iprop(∃ (d : KBReal) (W : IProp GF), ⌜γ.st.kb = some d ∧ d.P = BP ∧ d.be = b⌝ ∗
    backend.isBackend d.γB BP W Pk b ∗ hookP γ.st Pk)

instance mvccBackendIsI_persistent (γ : MvccImpl) (BP : backend.BParams) (Pk : IProp GF) (b : Loc) :
    Persistent (mvccBackendIsI (GF := GF) γ BP Pk b) := by
  unfold mvccBackendIsI; infer_instance

/-- **The watchers were taken care of** (`mvccWatchersOk`): a store without watchers has none;
with watchers, a commit of nothing needs nothing, and nothing else is taken care of outside the
watchable store's own `End` and `Restore` (which do not go through this predicate). -/
def mvccWatchersOkI (γ : MvccImpl) (op : MvccOp) : IProp GF :=
  if γ.watched then
    match op with
    | .commit _ pend => iprop(⌜pend = []⌝)
    | .restore => iprop(False)
  else iprop(True)

instance mvccWatchersOkI_persistent (γ : MvccImpl) (op : MvccOp) :
    Persistent (mvccWatchersOkI (GF := GF) γ op) := by
  unfold mvccWatchersOkI; split
  · split <;> infer_instance
  · infer_instance

/-- **A transaction of the store** (`mvccTxn`, of a store's own transaction, a `*metricsTxnWrite`):
today's read transaction at the state's log, revision and compaction revision, or today's write
transaction at the log the state is, nothing pending; and the reader's loan of the readers' pool
(the caller's thread token is in the pool until `End`). -/
def mvccTxnI (t : GoInterface) (γ : MvccImpl) (trace : Loc) : MTxn → IProp GF
  | .read σ => iprop(∃ s : Loc, ⌜1 ≤ σ.log.length⌝ ∗ isMvccI s γ ∗ mvccLoan γ ∗
      ((∃ mw : Loc, ⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝ ∗
          isTxnRead mw s γ.st trace σ.log (W64 (σ.rev : Int)) σ.crev) ∨
       (∃ trw : Loc, ⌜t = interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw⌝ ∗
          isRoTxnWrite trw s γ.st trace σ.log (W64 (σ.rev : Int)) σ.crev)))
  | .write σ pend => iprop(∃ (mw s : Loc) (puts deletes putSize : w64),
      ⌜σ.pending = none ∧ 1 ≤ σ.log.length ∧ (γ.st.cm = false → σ.crev = -1)⌝ ∗
      isMvccI s γ ∗
      isTxnWrite mw s γ.st trace σ.log pend puts deletes putSize σ.crev ∗
      mvccLoan γ ∗
      (⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝ ∨
       (∃ tw : Loc, ⌜t = interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw ∧
          γ.watched = true⌝ ∗
        tw ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                 s' := γ.wl } : watchableStoreTxnWrite) ∗
        isWatchableStore γ.wl s γ.ws)))

/-- **The watchable store `ws` of the names `γ`** (`isWatchableMvcc`): the store's, with watchers. -/
def isWatchableMvccI (ws : Loc) (γ : MvccImpl) : IProp GF :=
  iprop(⌜γ.watched = true ∧ γ.wl = ws⌝ ∗ ∃ st : Loc, isWatchableStore ws st γ.ws ∗ isMvccI st γ)

instance isWatchableMvccI_persistent (ws : Loc) (γ : MvccImpl) :
    Persistent (isWatchableMvccI (GF := GF) ws γ) := by
  unfold isWatchableMvccI; infer_instance

/-- **A share `q` of the store's open token** (`mvccOpen`): the token, and the invariant that holds
either all of it or the store's closer (the watchable store's, `wsCloserM`: `Close` trades the whole
token for it). -/
def mvccOpenI (γ : MvccImpl) (q : Qp) : IProp GF :=
  iprop(ghostVar γ.op q () ∗
    inv mvccOpenN iprop(ghostVar γ.op 1 () ∨
      (if γ.watched then (∃ c : Int, wsCloserM γ.wl γ.sl γ.st c) else storeCloser γ.sl γ.st)))

/-- **The range deleter `rd`** (`mvccDeleter`): with watchers, the watchable store's `Write` at a
fresh trace (`rdCode`); a store without watchers has none in the abstract mode yet. -/
def mvccDeleterI (rd : GoFunc) (γ : MvccImpl) : IProp GF :=
  if γ.watched then rdCode rd γ.wl else iprop(False)

instance mvccDeleterI_persistent (rd : GoFunc) (γ : MvccImpl) :
    Persistent (mvccDeleterI (GF := GF) rd γ) := by
  unfold mvccDeleterI; split <;> infer_instance

/-- **The store of the names** is the names' location. -/
theorem isMvccI_loc (s : Loc) (γ : MvccImpl) : isMvccI (GF := GF) s γ ⊢ ⌜γ.sl = s⌝ := by
  iintro #Hs
  iunfold isMvccI at Hs
  icases Hs with ⟨-, %Hf, -⟩
  ipureintro; exact Hf.2.2.2.2

/-- **A ticket of the pool**: the store's reader and the loan. -/
theorem mvccBorrow (s : Loc) (γ : MvccImpl) :
    £ 1 ∗ isMvccI (GF := GF) s γ ∗ threadTok ⊢ |={⊤}=> storeReaderC s γ.st ∗ mvccLoan γ := by
  iintro ⟨Hlc, #Hs, Htt⟩
  iunfold isMvccI at Hs
  icases Hs with ⟨-, -, -, #Hpool, -, -, -⟩
  imod threadPool.borrow_lc tixN γ.tl (poolR s γ) ⊤ (by simp) $$ [$Hlc $Hpool $Htt] with ⟨HR, Hl⟩
  iunfold poolR at HR
  icases HR with ⟨Hr, Hx⟩
  imodintro
  iunfold mvccLoan
  iframe Hr Hl Hx

/-- **The ticket back to the pool**, for the thread token. -/
theorem mvccGiveBack (s : Loc) (γ : MvccImpl) :
    isMvccI (GF := GF) s γ ∗ mvccLoan γ ∗ storeReaderC s γ.st ⊢ |={⊤}=> threadTok := by
  iintro ⟨#Hs, Hl, Hr⟩
  iunfold isMvccI at Hs
  icases Hs with ⟨-, -, -, #Hpool, -, -, -⟩
  iunfold mvccLoan at Hl
  icases Hl with ⟨Hl, Hx⟩
  iapply threadPool.giveBack tixN γ.tl (poolR s γ) ⊤ (by simp)
  iframe Hpool Hl
  iunfold poolR
  iframe Hr Hx

/-- **The whole open token gives the closer** (`Close`, later): the invariant holds it, not the
token. -/
theorem mvccOpen_take (γ : MvccImpl) :
    mvccOpenI (GF := GF) γ 1 ⊢ |={⊤}=>
      ▷ (if γ.watched then (∃ c : Int, wsCloserM γ.wl γ.sl γ.st c) else storeCloser γ.sl γ.st) := by
  iintro H
  iunfold mvccOpenI at H
  icases H with ⟨Ht, #Hinv⟩
  iinv Hinv with Hi Hclose
  icases Hi with (>Ht' | Hc)
  · ihave %Hv := ghostVar_valid_2 γ.op _ _ _ _ $$ Ht Ht'
    exfalso
    have h1 : (1 : Rat) + (1 : Qp).val ≤ 1 := Hv.1
    have := (1 : Qp).2
    grind
  imod Hclose $$ [Ht] with _
  · inext; ileft; iexact Ht
  imodintro
  iexact Hc

/-- In the abstract mode, a part of the abstract committed log agrees with a ghost half. -/
theorem absAt_agree (γ : StoreNames) (h : γ.absQ = true) (q1 q2 : Qp) (l1 l2 : Log) :
    absAt (GF := GF) γ q1 l1 ∗ ghostVar γ.abs q2 l2 ⊢
      absAt γ q1 l1 ∗ ghostVar γ.abs q2 l2 ∗ ⌜l1 = l2⌝ := by
  unfold absAt
  simp only [h, ↓reduceIte]
  iintro ⟨H1, H2⟩
  ihave %Hl := ghostVar_agree γ.abs _ _ _ _ $$ H1 H2
  iframe H1 H2
  ipureintro; exact Hl

end defs

end mvcc
end EtcdGrove
end Perennial
