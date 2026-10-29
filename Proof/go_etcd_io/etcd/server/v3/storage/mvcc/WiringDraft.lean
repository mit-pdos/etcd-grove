/-
**Question 5's Draft: the wiring** (the backend-compaction stage, `notes/backend-cmp-plan.md`,
"Question 5's Draft round" and "Question 5's Draft, repaired after review round 14"; the user's
decisions (i)-(iv), their answers Q5-1/Q5-2, and, after round 14, F2 and the deferral of the server's
side to M2). Draft statements only, imported by nothing: each definition or statement here is what an
existing one becomes at the switch (the name with `W` in place of its suffix), written in full so the
review reads real Lean. No proof is switched; the one law here is proved, the switch laws are stated
as `Prop`s, and nothing here is assumed.

- (i) `store.Compact` borrows the read token from the apply thread's `writerOwn` (`storeRT γ` in its
  pre and every branch of its post). Its write-back tokens (F5) come from a persistent supply in the
  store's physical facts (`physOk`, `kbWTSupplyM`), not from its caller.
- (ii) The compaction keys' write right stays in the store (F1, decided by the agent): `store.restore`
  gives the flag's half back, and `NewStore` then allocates an invariant holding the right or a lock
  key (`mwInvW`); the key (`mwKeyW`) sits in the batch lock's resource (`writerRes`) from before
  `NewStore`'s first `Unlock`. A session writing a compaction key holds the lock, so the key: it swaps
  the key for the right (`mwSwapW`), writes, and swaps back before `Unlock`. Both are gated by the
  mode: a store that never compacts has neither.
- (iii) mvcc's assumed backend gets the same flag, opaque: `viewFkW γb f`.
- (iv) The compaction mode is in the instance (Q5-1): `kbCmpM kb cm` (`KBReal.cm` at the switch). The
  job's budgets (`compactJobResM`: a reader's token taken from the store's own pool (F2), the
  safe-range slot from the backend's creation (Q5-2)) travel with the compaction token (`compactTokW`)
  and are `True` when the store does not compact (F3). The old bridge is the new one weakened under
  `dlNoDel`, at any slots and right (F7). The server stays `cm := false`: its side (R2-7,
  `NewServer.spec`) is M2's.
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

/-- (iv) **The compaction mode in the instance** (Q5-1, the user's): the real backend supports the
compaction when its creator chose it (`cm`, a field of `KBReal` at the switch: M2's `ρ.kv.cmp`; `false`
for D22's received backends, "no restore in compaction mode"); mvcc's assumed backend always.
Draft of `kbCmp`. -/
def kbCmpM (kb : Option KBReal) (cm : KBReal → Bool) : Prop :=
  match kb with
  | none => True
  | some d => cm d = true

/-- (iv) The mode is decidable (it gates resources below). -/
instance kbCmpM_dec (kb : Option KBReal) (cm : KBReal → Bool) : Decidable (kbCmpM kb cm) := by
  unfold kbCmpM; cases kb <;> infer_instance

/-- (ii) F1: **the write right's lock key** (exclusive; a new physical name at the switch, `mk`,
allocated by `NewStore`, or by `store.Restore` for its new names): in the batch lock's resource. -/
def mwKeyW (γmk : GName) : IProp GF := ghostVar γmk 1 ()

/-- (ii) F1: **the batch lock's resource with the key** (draft of `writerRes`'s new conjunct): the key
when the store compacts, else nothing. Deposited with the rest of `writerRes` at `NewStore`'s first
`Unlock`, before `restore`. -/
def mwSlotW (γ : StoreNames) (cm : KBReal → Bool) (γmk : GName) : IProp GF :=
  if kbCmpM γ.kb cm then mwKeyW γmk else iprop(True)

abbrev mwN : Namespace := nroot.@"mvcc_mw"

/-- (ii) F1: **the write right's invariant** (persistent, in `isStore` at the switch, allocated by
`NewStore` after `restore` gives the right back): the right, or the key (a session holding the batch
lock has swapped them). -/
def mwInvW (γ : StoreNames) (γmk : GName) : IProp GF :=
  inv mwN iprop(kbMWW γ.kb γ.bucket ∨ mwKeyW γmk)

/-- (ii) F1: **a lock holder's swap** (what `SetScheduledCompact`'s and the job's sessions use): the
batch lock's resource `W` gives the right, and the right gives `W` back. -/
def mwSwapW (W MW : IProp GF) : IProp GF :=
  iprop(□ (W ={⊤}=∗ MW ∗ (MW ={⊤}=∗ W)))

/-- (ii) F1: the law the switch proves (stated here): with the invariant, a resource holding the key
swaps (the key is exclusive, so the invariant holds the right while a holder has the key). -/
def mwSwap_of_inv.stmt : Prop :=
  ∀ (γ : StoreNames) (γmk : GName) (R : IProp GF),
    mwInvW γ γmk ⊢ mwSwapW iprop(mwKeyW γmk ∗ R) (kbMWW γ.kb γ.bucket)

/-- (iv) F2/F3/F5: **the compaction job's budgets, by the mode** (draft of `compactJobRes`): for a
compacting real backend, a reader's token (taken out of the store's own pool: F2, the user's) and the
safe-range slot (from the backend's creation: Q5-2); nothing otherwise. The write-back supply is no
longer here (F5: persistent, `kbWTSupplyM` in the store's physical facts). -/
def compactJobResM (kb : Option KBReal) (cm : KBReal → Bool) : IProp GF :=
  if kbCmpM kb cm then iprop(kbRT kb ∗ kbSR kb) else iprop(True)

/-- (iv) F5: **the write-back supply, by the mode** (persistent; in `physOk` at the switch, where both
`store.Compact` and the job pay their `LockInsideApply`/`LockOutsideApply` and `ForceCommit` from the
receipts of their own steps). -/
def kbWTSupplyM (kb : Option KBReal) (cm : KBReal → Bool) : IProp GF :=
  if kbCmpM kb cm then kbWTSupply kb else iprop(True)

/-- (iv) F3: the slot `NewStore` takes from its caller, by the mode (the reader token comes from the
pool it already takes: F2). -/
def kbSRM (kb : Option KBReal) (cm : KBReal → Bool) : IProp GF :=
  if kbCmpM kb cm then kbSR kb else iprop(True)

/-- (iv) F2: the readers `NewStore` keeps back for the job: one when the store compacts over the real
backend, none otherwise (mvcc's assumed backend's `kbRT` is `True`, so none is needed there). -/
def nJobRd (kb : Option KBReal) (cm : KBReal → Bool) : Nat :=
  match kb with
  | none => 0
  | some d => if cm d then 1 else 0

/-- (iv) **The compaction token with the job's budgets** (draft of `compactTok`): the index
compactor's token at or below `c` and the job's budgets by the mode, handed from job to job through
the queue. -/
def compactTokW (γ : StoreNames) (cm : KBReal → Bool) (c : Int) : IProp GF :=
  iprop((∃ c' : Int, ⌜c' ≤ c⌝ ∗ idxCompactor γ.idx c') ∗ compactJobResM γ.kb cm)

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
the switch): a contract with compaction (`Cmp := True`, the safe-range slot `SR`/`SRh`, the right
`MW`) whose deletable keys are none (`□ ∀ k, Del k -∗ False`: the backend's `dlNoDel` with `bkDel`) is
one with any `Del'`, no compaction, and any slots and right (F7: they occur only under `⌜Cmp⌝`, so a
non-compacting real store's `kbSR`, `srSlot`, fits). -/
def isKeyBackendG_weaken.stmt : Prop :=
  ∀ (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp' : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (SR SRh MW SR' SRh' MW' : IProp GF),
    ¬ Cmp' →
    isKeyBackendG b View RT WT NC PutOk Del W Wi Dep True P HF Req Rb Bt SR SRh MW ∗
      □ (∀ k, Del k -∗ False) ⊢
    isKeyBackendG b View RT WT NC PutOk Del' W Wi Dep Cmp' P HF Req Rb Bt SR' SRh' MW'

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
the apply thread's `writerOwn`) in the pre and given back in every branch of the post. Its write-back
tokens (F5) come from `kbWTSupplyM` in `isStore`'s physical facts, so the pre has no `storeWT`. -/
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

/-- (ii)/(iv) **Draft of `NewStore.spec`** (repaired after round 14): as today, with the
no-compaction token of either backend (`kbNoCmpW`), the backend contract only at the index's names it
was registered for (F4: `γ.idx = γi`), and, by the mode (F3; `cm` is `KBReal.cm` at the switch), the
safe-range slot (`kbSRM`, from the backend's creation: Q5-2) and the write-back supply (`kbWTSupplyM`,
persistent: F5). The job's reader token comes from the pool `NewStore` already takes (F2, the user's):
the post gives back `nJobRd kb cm` fewer readers (one for a compacting real store, else none). -/
abbrev NewStore.specW (cm : KBReal → Bool) : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (wq : Bool) (γi : IdxNames) (γok : GName),
  batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        storeBackend b s γ P) ∗
      kbView kb γb 1 (∅ : Bucket) ∗ kbNoCmpW kb γb ∗ kbRegRight kb ∗ kbWT kb ∗ kbWT kb ∗
      kbSRM kb cm ∗ □ kbWTSupplyM kb cm ∗
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
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - nJobRd kb cm) (),
        storeReaderC s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) ∗ idxCert γ.idx [[], []] ∗
      (if wq then logQ γ [[], []] else iprop(True)) ∗ storeCloser s γ ∗
      fieldShare s γ (1 : Qp).half.half ∗ wsDep γ ∗ writerFrag γ ∗
      crevUB γ.idx (1 : Qp).half (-1) ∗ retiredAt γ 0 }}

/-- R9-3/F6: **Draft of `SetScheduledCompact.spec`**, over the fully general batch transaction
(`batchTxSpecG`: the read and write tokens, the put condition and the right all the caller's; the
compaction's clauses on, `Cmp := True`), with the swap of the lock's resource for the right
(`mwSwapW`, F1). `SetFinishedCompact.specW` is the same with its own function (no caller in the
server; for uniformity). -/
abbrev SetScheduledCompact.specW : Prop :=
  ∀ (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (MW : IProp GF) (f : val) (value : w64)
    (Pre Q Post : IProp GF),
  0 ≤ sint.Z value →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      batchTxSpecG bt View RT WT PutOk Del W Dep True Locked P HF Rb MW ∗ mwSwapW W MW ∗
      RT ∗ WT ∗ HF f ∗ Pre ∗
      □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗ (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact))
      (Val #(GoInterface.ok bt))) (Val #value))
  {{ RET #(); RT ∗ Post }}

end specs

end mvcc
end EtcdGrove
end Perennial
