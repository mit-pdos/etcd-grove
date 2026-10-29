/-
**Question 5's Draft: the wiring** (the backend-compaction stage, `notes/backend-cmp-plan.md`,
"Question 5's Draft round"; the user's decisions (i)-(iv), 2026-10-29). Draft statements only,
imported by nothing: each definition or statement here is what an existing one becomes at the switch
(the name with `W` in place of its suffix), written in full so the review reads real Lean. No proof
is switched; the one law here is proved, and nothing here is assumed.

- (i) `store.Compact` borrows the read token from the apply thread's `writerOwn` (`storeRT γ` in its
  pre and in every branch of its post), for `checkPrevCompactionCompleted`'s `ReadTx` (`metaReadTx rt
  RT`: its `RLock` takes the token, its `RUnlock` gives it back).
- (ii) `store.restore` keeps the compaction keys' write right: its post gives back the flag's half
  (`kbMWW`, from the clause `NC -∗ NC ∗ …` its reads used), and `NewStore` deposits it in the batch
  lock's resource (`storeWW`), where every session that writes a compaction key (`SetScheduledCompact`
  in `store.Compact`, the job's `UnsafeSetFinishedCompact`) takes and returns it under the lock. It is
  never handed to a client. (The batch lock, not the compaction right: `store.Compact`'s
  `SetScheduledCompact` runs while the previous job may run `UnsafeSetFinishedCompact`, so the right
  cannot be in the compaction token, which the queue hands from job to job.)
- (iii) mvcc's assumed backend gets the same flag, opaque: `viewFkW γb f`, with `viewNoCmpW γb :=
  viewFkW γb 0` and `kbMWW none γb := ∃ f, viewFkW γb f`; an honest creator of that backend holds both
  (`kbNoCmpW_MW`). `kbMW` takes the bucket's name for it.
- (iv) the real backend supports the compaction (`kbCmpW := True`); the job's budgets (`compactJobRes`)
  travel with the compaction token (`compactTokW`), `NewStore` taking them from its caller; the old
  bridge becomes an instance of the new one (`isKeyBackendG_weaken`'s statement below).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- (iii) **mvcc's assumed backend's compaction-key flag** (opaque, the creator's): the client's
half at `f`, mirroring the real backend's `backend.fkOwn` (`0`: no compaction key). Draft of
`viewFk`. -/
opaque viewFkW (γb : GName) (f : Nat) : IProp GF

/-- (iii) The assumed backend records no compaction: its flag at `0` (draft of `viewNoCmp`, opaque
until now). -/
def viewNoCmpW (γb : GName) : IProp GF := viewFkW γb 0

/-- (iii) Draft of `kbNoCmp` over `viewNoCmpW`. -/
def kbNoCmpW (kb : Option KBReal) (γb : GName) : IProp GF :=
  match kb with
  | none => viewNoCmpW γb
  | some d => bkNoCmp d.γB

/-- (iii) **The compaction keys' write right** (draft of `kbMW`, now also over the bucket's name
`γb`): the client's half of the flag, at any value, for either backend. -/
def kbMWW (kb : Option KBReal) (γb : GName) : IProp GF :=
  match kb with
  | none => iprop(∃ f : Nat, viewFkW γb f)
  | some d => iprop(∃ f : Nat, backend.fkOwn d.γB f)

/-- (ii)/(iii) The no-compaction token is a write right (both backends): what `store.restore` gives
back after its reads. -/
theorem kbNoCmpW_MW (kb : Option KBReal) (γb : GName) :
    kbNoCmpW (GF := GF) kb γb ⊢ kbMWW kb γb := by
  cases kb with
  | none =>
    unfold kbNoCmpW kbMWW viewNoCmpW
    iintro H
    iexists 0
    iexact H
  | some d =>
    unfold kbNoCmpW kbMWW bkNoCmp
    iintro H
    iexists 0
    iexact H

/-- (iv) **The real backend supports the compaction** (draft of `kbCmp`; decision O5 keeps the
parameter, removed in a cleanup). See the plan's question Q5-1: with the old bridge kept for D22's
exact readers, a store over a backend fixed at "nothing deletable" cannot meet `Cmp`; the
alternative is the mode in the instance (`kbCmpM`). -/
def kbCmpW (_kb : Option KBReal) : Prop := True

/-- (Q5-1's alternative, not the approved one) **The compaction mode in the instance**: the real
backend supports the compaction when its creator registered the store's deletable keys (`cm`, a
field of `KBReal` at the switch: the server's `ρ.kv.cmp`). -/
def kbCmpM (kb : Option KBReal) (cm : KBReal → Bool) : Prop :=
  match kb with
  | none => True
  | some d => cm d = true

/-- (ii) **The batch lock's resource with the write right** (draft of `storeW`): the store's lock
resource and the compaction keys' write right, which a session writing a compaction key takes and
gives back under the lock. -/
def storeWW (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(storeW s γ ∗ kbMWW γ.kb γ.bucket)

/-- (iv) **The compaction token with the job's budgets** (draft of `compactTok`): the index
compactor's token at or below `c` and the job's budgets (`compactJobRes`: a reader's token, the
safe-range slot, the write-back supply), handed from job to job through the queue. -/
def compactTokW (γ : StoreNames) (c : Int) : IProp GF :=
  iprop((∃ c' : Int, ⌜c' ≤ c⌝ ∗ idxCompactor γ.idx c') ∗ compactJobRes γ.kb)

/-- (iv) **The store's deletable keys, by the index's names** (draft): `delKey` depends on the
store's names only through the index's (`γ.idx`), which `NewStore`'s caller allocates before the
store exists, so the creator can fix the backend's registration (`backend.dlReg`) to it before
`NewStore` (`NewStore_backend`, `BuildLemmas`). -/
def delKeyI (γi : IdxNames) (k : GoString) : IProp GF :=
  iprop(∃ (c : Int) (log : Log), crevLb γi c ∗ idxCert γi log ∗ ⌜-1 ≤ c ∧ KeyDel log c k ∧ NoDelPutAt log c⌝)

theorem delKey_eq_delKeyI (γ : StoreNames) (k : GoString) :
    delKey (GF := GF) γ k = delKeyI γ.idx k := rfl

/-- (iv) **The registration a compacting store fixes** (draft): the `Key` bucket's keys that the
store's index says compaction may delete. -/
def storeDlReg (γB : backend.BNames) (γi : IdxNames) : IProp GF :=
  backend.dlReg γB (fun nk => iprop(⌜nk.1 = go_etcd_io.etcd.server.v3.storage.schema.keyName⌝ ∗
    delKeyI γi nk.2))

/-- (iv) **The old bridge, an instance of the new** (the statement of the law it needs; proved at
the switch): a contract with compaction (`Cmp := True`, the safe-range slot `SR`/`SRh`) whose
deletable keys are none (`□ ∀ k, Del k -∗ False`: the backend's `dlNoDel` with `bkDel`) is one with
any `Del'`, no compaction, and trivial slots. -/
def isKeyBackendG_weaken.stmt : Prop :=
  ∀ (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp' : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (SR SRh MW : IProp GF),
    ¬ Cmp' →
    isKeyBackendG b View RT WT NC PutOk Del W Wi Dep True P HF Req Rb Bt SR SRh MW ∗
      □ (∀ k, Del k -∗ False) ⊢
    isKeyBackendG b View RT WT NC PutOk Del' W Wi Dep Cmp' P HF Req Rb Bt iprop(True) iprop(True) MW

/-- (iv) **The store's deletable keys through the backend's registration** (the statement of the
law the switch needs; review round 1's F7: under `▷` of the saved predicate's agreement, as `◇`
since `delKey` is timeless): a contract over `Del` is one over any `Del'` equivalent to it. -/
def isKeyBackendG_congrDel.stmt : Prop :=
  ∀ (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (SR SRh MW : IProp GF),
    isKeyBackendG b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW ∗
      □ (∀ k, Del k ∗-∗ ◇ Del' k) ⊢
    isKeyBackendG b View RT WT NC PutOk Del' W Wi Dep Cmp P HF Req Rb Bt SR SRh MW

end draft

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- (i) **Draft of `store.Compact.spec`**: as today, and the read token `storeRT γ` (borrowed from
the apply thread's `writerOwn`) in the pre and given back in every branch of the post. -/
abbrev store.Compact.specW : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : Log) (te : Bool),
  trace ≠ null → storeCmp γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      isStore s γ ∗ storeStop s γ ∗ compactRight γ c ∗ storeRT γ ∗
      idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ NoDelPutAt log (sint.Z rev)⌝ ∗
      hookIs γ P f ∗
      csContract P f Pre Q Post ∗ traceutil.ownTrace trace te }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗ storeRT γ ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ compactRight γ (sint.Z rev) ∗
        crevLb γ.idx (sint.Z rev) ∗ Post ∗ compactChan ch (compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        compactRight γ c ∗ Pre ∗ compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : Log, idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        compactRight γ c ∗ Pre)) }}

/-- (ii)/(iv) **Draft of `NewStore.spec`**: as today, with the no-compaction token of either backend
(`kbNoCmpW`, the assumed backend's now its flag at `0`), the contract's write right named per
backend (`storeBackend`'s `MW := kbMWW γ.kb γ.bucket`, at the switch), and the compaction job's
budgets (`compactJobRes kb`: all `True` for the assumed backend), which the store keeps with its
compaction token (`compactTokW`, in `storeCloser`'s queue). The post is today's. -/
abbrev NewStore.specW : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (wq : Bool) (γi : IdxNames) (γok : GName),
  batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ → storeBackend b s γ P) ∗
      kbView kb γb 1 (∅ : Bucket) ∗ kbNoCmpW kb γb ∗ kbRegRight kb ∗ kbWT kb ∗ kbWT kb ∗
      compactJobRes kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), kbRT kb) ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : StoreNames,
      ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = kb ∧ γ.watchQ = wq ∧ γ.idx = γi ∧ γ.cok = γok⌝ ∗
      isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 Log) ∗
      hookInit γ P f ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        storeReaderC s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) ∗ idxCert γ.idx [[], []] ∗
      (if wq then logQ γ [[], []] else iprop(True)) ∗ storeCloser s γ ∗
      fieldShare s γ (1 : Qp).half.half ∗ wsDep γ ∗ writerFrag γ ∗
      crevUB γ.idx (1 : Qp).half (-1) ∗ retiredAt γ 0 }}

end specs

end mvcc
end EtcdGrove
end Perennial
