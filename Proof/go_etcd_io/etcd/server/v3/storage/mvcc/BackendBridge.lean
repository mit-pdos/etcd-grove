/-
**The backend meets mvcc** (unit 4, part 2): mvcc's contract of its backend's `Key` bucket
(`isKeyBackendG`, `InvStore.lean`) from the backend's own proved contract (`isBackend`,
`backend/InvBackend.lean`, and the public specs `Spec/.../storage/backend/*.lean`), for a
backend whose parameters `P` have schema's buckets and whose hook's buckets are all but `Key`
(`bridgeParams`). Lean-first; `notes/decisions.md`, "The backend meets mvcc (unit 4)".

**The instance.**
- The view: `bkView γ q m` (`InvStore.lean`), the backend's clients' view (`bView γ q vd`) whose
  `Key` bucket is `m` (`keyView`: off the hook's buckets, the view is the `Key` bucket).
- The reader's token: `bkRTx γ P b`, a reader's slot of the backend (`rdTok`) and a share of the
  backend open (`bOpen`); the session's token: a write-back's budget (`wbTok`).
- The puts' condition (`keyPutOk`, `InvStore.lean`): at most `2^56` per session, a key of
  `1..MaxKeySize` bytes above every key of the bucket and of the session's puts (the safe-range
  discipline the backend now requires of `Key`'s `UnsafeSeqPut`); no bound on the value (an
  oversized one is fatal in the backend: `issues/etcd-backend-put-value-too-large-fatal.md`).
- The lock's tokens: `bkLocked γ P b l`, the batch lock held in a session whose write buffer's
  `Key` bucket is the puts `l` (no delete pending), with a write-back's budget for its `Unlock`;
  `bkLockedO γ P b n`, `NewStore`'s session after `n` bucket creations (nothing the readers see
  changed).
- The range read of the `Key` bucket (`keyRangeReadSpec`, the watchable store's
  `rangeEvents`): the backend's `UnsafeRange` returns bbolt's range then the read buffer's
  (`rtRange`), which is the bucket's range only if the read buffer's keys are above bbolt's
  (`keySafe`: the "safe range bucket" discipline, keys never overwritten, put in increasing
  order). The order is the backend's invariant (`safeRv`, `rtHeld_safe`: unit 5); the size (the
  range's limit is `2^63 - 1` entries) is the premise `keySized`. A `ConcurrentReadTx` promises
  no range (its cached read buffer can repeat a committed key:
  `issues/etcd-backend-read-buffer-cache-stale-after-commit.md`).
- Unit 5: `storeBackend_of_backend` gives the contract `NewStore` takes for every store of a
  real instance (`KBReal`), with the late-bound lock resource `lateW`.
- The compaction's clauses (2026-10-13, the merge with mvcc's unit 5a): the snapshots are exact
  (`snapThin` with nothing missing), the batch transaction's point read finds its key (the
  `Del` disjunct unused); the job's `LockOutsideApply` gives the lock's resource with the
  deposit witness `True` (the lock holds the late-bound `W` from the backend's creation:
  `bt_lockOutJ`); `Size`/`SizeInUse` are the backend's (`bk_size`, `bk_sizeInUse`). The rest,
  `UnsafeDelete` of the `Key` bucket, the limited range under the lock, the `Meta` keys' put and
  read, the safe-range-delete lock, are the contract's only where the backend supports the
  compaction (`Cmp`), which it does not: its model forbids deleting from a safe-range bucket
  (`batchTxBuffered.UnsafeDelete`'s premise `P.SB bi.name = false`, the invariant's `safeSt`), an
  `Unlock` that changes what readers see needs the clients' whole view, which the compaction job
  (under the batch lock alone) does not hold, and the `Meta` bucket is the hook's, of which reads
  promise nothing (`notes/decisions.md`, "The compaction over the real backend").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BatchLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ConcurrentReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Size
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SizeInUse
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockInsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeSeqPut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeDelete
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode backend

/-! ## The parameters -/

/-- schema's `Key` bucket, as the backend names it (`bucket{id: 1, name: "key",
safeRangeBucket: true}`). -/
def keyBI : BucketInfo := ⟨W64 1, go_etcd_io.etcd.server.v3.storage.schema.keyName, true⟩

/-- schema's `Meta` bucket. -/
def metaBI : BucketInfo := ⟨W64 2, go_etcd_io.etcd.server.v3.storage.schema.metaName, false⟩

/-- The backend's parameters for mvcc: its table has schema's `Key` and `Meta` buckets, and the
hook's buckets (those whose contents the readers' view `vData` leaves out) are all but `Key`
(the lessor, auth, membership and the consistent index write the others: their reads promise
nothing here); neither `Key` nor `Meta` is a tracked bucket (`RB`, D22, 2026-10-23: the store
writes them without the tracked buckets' half). -/
def bridgeParams (P : BParams) : Prop :=
  P.has keyBI ∧ P.has metaBI ∧
    (∀ n, P.HB n = decide (n ≠ go_etcd_io.etcd.server.v3.storage.schema.keyName)) ∧
    (∀ n, P.SB n = decide (n = go_etcd_io.etcd.server.v3.storage.schema.keyName)) ∧
    P.RB go_etcd_io.etcd.server.v3.storage.schema.keyName = false ∧
    P.RB go_etcd_io.etcd.server.v3.storage.schema.metaName = false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- A reader's token at the share `qo`: a reader's slot of the backend, and the share `qo` of
the backend open (given back at its `RUnlock`). -/
def bkRT (γ : BNames) (P : BParams) (b : Loc) (qo : Qp) : IProp GF :=
  iprop(rdTok γ P b ∗ bOpen γ qo)

/-- A reader's token (the contract's: the reader's share `rdOpen` of the backend open; `kbRT` of a
real instance). (D22 receiver epochs, S8d, W7, 2026-10-25: a fixed share, until then some share, so
that every reader's token and the constructors' half reassemble the whole open token for the old
backend's `Close`, `bOpen_one_shares`.) -/
def bkRTx (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(rdTok γ P b ∗ bOpen γ rdOpen)

theorem bkRT_x (γ : BNames) (P : BParams) (b : Loc) :
    bkRT (GF := GF) γ P b rdOpen ⊢ bkRTx γ P b := by
  unfold bkRT bkRTx
  iintro ⟨H1, H2⟩
  iframe H1 H2

/-- A session holding the puts `l` in the `Key` bucket: no delete pending, the write buffer's
`Key` bucket the puts, one more pending operation a put at most (from the free lock's), at most
`2^56` puts, out of the hook's window. -/
def sessPuts (P : BParams) (st : BSess) (l : Puts) : Prop :=
  st.ndel = W64 0 ∧ sint.Z st.pend < sint.Z P.limit + l.length ∧
    (bkOf st.W.bks (W64 1) = l ∧ l.length ≤ 2 ^ 56 ∧ st.cnt.hw = false)

/-- The batch lock held in a session holding the puts `l`, with a write-back's budget. -/
def bkLockedAt (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (l : Puts) : IProp GF :=
  iprop(batchLocked γ P b st ∗ wbTok γ ∗ ⌜sessPuts P st l⌝)

/-- The batch lock held with the puts `l`. -/
def bkLocked (γ : BNames) (P : BParams) (b : Loc) (l : Puts) : IProp GF :=
  iprop(∃ st : BSess, bkLockedAt γ P b st l)

/-- **The batch lock held after a delete from a hook's bucket** in a session holding the puts `l`
(the lessor's from `Lease`, `bt_leaseDel`; leases T3, 2026-10-25), with a write-back's budget:
what only `Unlock` takes (`bt_unlockD`). -/
def bkLockedD (γ : BNames) (P : BParams) (b : Loc) (l : Puts) : IProp GF :=
  iprop(∃ (st0 : BSess) (bi : BucketInfo) (k : GoString), batchLocked γ P b (st0.del bi k) ∗
    wbTok γ ∗ ⌜sessPuts P st0 l ∧ sessWf P st0 ∧ P.HB bi.name = true⌝)

/-- `NewStore`'s session after `n` bucket creations: no delete pending, `n` more operations
than at the free lock (at most two), nothing the readers see changed, out of the hook's window,
a write-back's budget. -/
def bkLockedO (γ : BNames) (P : BParams) (b : Loc) (n : Nat) : IProp GF :=
  iprop(∃ st : BSess, batchLocked γ P b st ∗ wbTok γ ∗
    ⌜st.ndel = W64 0 ∧ sint.Z st.pend < sint.Z P.limit + n ∧ viewSame P st ∧ n ≤ 2 ∧
      st.cnt.hw = false⌝)

end defs

/-! ## Pure lemmas -/

/-- The puts applied to a bucket, looked up: the last put of the key, else the bucket's. -/
theorem foldl_insert_lookup (l : Puts) (m : Bucket) (k : GoString) :
    (l.foldl (fun m p => GMap.insert p.1 p.2 m) m).lookup k = (lastVal l k).or (m.lookup k) := by
  induction l generalizing m with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons, ih, lastVal_cons, GMap.lookup_insert_eq_iff]
    cases lastVal l k <;> by_cases h : e.1 = k <;> simp [h]

/-- With the bridge's parameters, the `Key` bucket is not the hook's. -/
theorem key_not_HB {P : BParams} (hP : bridgeParams P) :
    P.HB go_etcd_io.etcd.server.v3.storage.schema.keyName = false := by
  rw [hP.2.2.1]; simp

/-- With the bridge's parameters, a bucket of the table off the hook's is `Key`. -/
theorem nonHB_key {P : BParams} (hP : bridgeParams P) {n : GoString} {i : w64}
    (hn : P.BT.lookup n = some i) (hb : P.HB n = false) : i = W64 1 := by
  rw [hP.2.2.1] at hb
  simp only [decide_eq_false_iff_not, Decidable.not_not] at hb
  subst hb
  have := hP.1
  unfold BParams.has keyBI at this
  rw [this] at hn
  exact (Option.some.inj hn).symm

/-- The readers' view of `rv` is `m` off the hook's buckets: the `Key` bucket's entries are
`m`'s. -/
theorem vOf_key {P : BParams} (hP : bridgeParams P) {rv : RView} {m : Bucket}
    (h : keyView (vData P rv) m) (k : GoString) :
    vOf P rv go_etcd_io.etcd.server.v3.storage.schema.keyName k = m.lookup k := by
  have := h go_etcd_io.etcd.server.v3.storage.schema.keyName k
  simp only [↓reduceIte] at this
  rw [← this]
  show vOf P rv _ k = (if P.HB _ then none else vOf P rv _ k)
  rw [key_not_HB hP]; rfl

/-- The writer's contents off the hook's buckets, of a session holding the puts `l` over a
view `m`: `m` with the puts applied. -/
theorem sData_puts {P : BParams} (hP : bridgeParams P) {st : BSess} {l : Puts} {m : Bucket}
    (hst : sessWf P st) (hs : sessPuts P st l) (hv : keyView (vData P (st.C, st.R)) m) :
    keyView (sData P st.S) (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) := by
  intro n k
  have hag := hst.2.2.2.2.2.2.2.2.2.1 hs.1
  show (if P.HB (n, k).1 then none else vOf P (st.S, ⟨∅, W64 0⟩) (n, k).1 (n, k).2) = _
  rw [vOf_emptyR]
  by_cases hn : n = go_etcd_io.etcd.server.v3.storage.schema.keyName
  · subst hn
    simp only [key_not_HB hP, Bool.false_eq_true, ↓reduceIte]
    rw [hag _ (key_not_HB hP) k, foldl_insert_lookup, ← vOf_key hP hv k]
    unfold ovB
    have hk := hP.1
    unfold BParams.has keyBI at hk
    simp only at hk
    rw [hk, Option.bind_some, hs.2.2.1]
    rfl
  · simp only [hn, ↓reduceIte, hP.2.2.1]
    simp [hn]

/-- A session with no puts in the `Key` bucket changed nothing the readers see. -/
theorem viewSame_noPuts {P : BParams} (hP : bridgeParams P) {st : BSess} (hst : sessWf P st)
    (hs : sessPuts P st []) : viewSame P st := by
  have hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = [] := by
    intro n i hn hb
    rw [nonHB_key hP hn hb]
    exact hs.2.2.1
  exact ⟨vData_free P st hst hs.1 hW, hW⟩

/-- A free state holds no puts. -/
theorem sessPuts_free {P : BParams} (hP : bridgeParams P) {st : BSess} (h : freeOk P st) :
    sessPuts P st [] := by
  refine ⟨h.2.2.1, by simpa using h.2.1, ?_, by simp, h.2.2.2.2⟩
  have hk := hP.1
  unfold BParams.has keyBI at hk
  exact h.2.2.2.1 _ _ hk (key_not_HB hP)

/-- A session with puts leaves room for a commit's hook. -/
theorem sessPuts_room {P : BParams} (hPw : P.Wf) {st : BSess} {l : Puts} (hs : sessPuts P st l) :
    sint.Z st.pend + P.hookMax < 2 ^ 58 := by
  obtain ⟨-, hp, -, hl, -⟩ := hs
  have h1 := hPw.2.2.1
  have h2 := hPw.2.2.2.1
  omega

/-- The `Key` bucket has no hook's own key. -/
theorem key_not_hk {P : BParams} (hP : bridgeParams P) (k : GoString) : P.hk keyBI.name k = false := by
  unfold BParams.hk
  rw [show keyBI.name = go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl, key_not_HB hP]

/-- A put of the `Key` bucket. -/
theorem sessPuts_put {P : BParams} (hPw : P.Wf) {st : BSess} {l : Puts}
    {k v : GoString} (hs : sessPuts P st l) (hl : l.length < 2 ^ 56) :
    sessPuts P (st.put keyBI k v true) (l ++ [(k, v)]) ∧ sint.Z st.pend + 1 < 2 ^ 58 := by
  obtain ⟨hd, hp, hw, -, hhw⟩ := hs
  have hlim := hPw.2.2.1
  have hb : sint.Z st.pend + 1 < 2 ^ 58 := by omega
  refine ⟨⟨hd, ?_, ?_, by simp only [List.length_append, List.length_singleton]; omega, hhw⟩, hb⟩
  · show sint.Z (st.pend + W64 1) < _
    simp only [List.length_append, List.length_singleton]
    have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    push_cast
    omega
  · show bkOf (wbAdd st.W.bks (W64 1) (k, v)) (W64 1) = _
    unfold wbAdd
    unfold bkOf at hw ⊢
    simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.getD_some]
    rw [hw]

/-- A session with puts leaves room for one more operation and a commit's hook. -/
theorem sessPuts_del_room {P : BParams} (hPw : P.Wf) {st : BSess} {l : Puts}
    (hs : sessPuts P st l) (hwf : sessWf P st) :
    sint.Z st.pend + 1 < 2 ^ 58 ∧ sint.Z (st.pend + W64 1) + P.hookMax < 2 ^ 58 := by
  obtain ⟨-, hp, -, hl, -⟩ := hs
  have h1 := hPw.2.2.1
  have h2 := hPw.2.2.2.1
  have h0 : 0 ≤ sint.Z st.pend := hwf.2.2.2.2.1
  have h3 : sint.Z st.pend < 2 ^ 58 := hwf.2.2.2.2.2.1
  have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  omega

/-- A delete from a hook's bucket leaves the writer's contents off the hook's buckets. -/
theorem sData_del_HB {P : BParams} {S : Data} {n k : GoString} (h : P.HB n = true) :
    sData P (S.insert n ((bktOf S n).delete k)) = sData P S := by
  unfold sData
  apply vData_eq_of_agree
  rw [vOf_emptyR, vOf_emptyR]
  intro n' hn' k'
  have : n ≠ n' := fun e => by subst e; rw [h] at hn'; cases hn'
  unfold dget
  rw [GMap.lookup_insert_ne _ _ this]

/-- A delete from a hook's bucket changes nothing the readers see. -/
theorem viewSame_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString}
    (hb : P.HB bi.name = true) (h : viewSame P st) : viewSame P (st.del bi k) := by
  refine ⟨?_, h.2⟩
  show vData P (st.C, st.R) = sData P (st.S.insert bi.name ((bktOf st.S bi.name).delete k))
  rw [sData_del_HB hb]
  exact h.1

/-- A change of a tracked bucket is the tracked buckets' (`rbData`). -/
theorem rbData_insert_tracked {P : BParams} {S : Data} {n : GoString} (b : BktData)
    (h : P.RB n = true) : rbData P (S.insert n b) = (rbData P S).insert n b := by
  apply GMap.ext
  intro n'
  rw [rbData_lookup]
  by_cases hn : n = n'
  · subst hn
    simp only [h, ↓reduceIte, GMap.lookup_insert_eq_iff]
  · rw [GMap.lookup_insert_ne _ _ hn, GMap.lookup_insert_ne _ _ hn, rbData_lookup]

/-- A delete from a tracked bucket, on the tracked buckets (`rbDel`). -/
theorem rbData_del {P : BParams} {S : Data} {n k : GoString} (h : P.RB n = true) :
    rbData P (S.insert n ((bktOf S n).delete k)) = rbDel (rbData P S) n k := by
  rw [rbData_insert_tracked _ h]
  unfold rbDel bktOf
  rw [rbData_lookup]
  simp only [h, ↓reduceIte]

/-! ## The buckets -/

section buckets
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- A bucket value of `bucket.go` is a `Bucket` (`bucket`'s methods). -/
theorem bucketIs_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (b : GoInterface) (id : w64) (name : GoString) (safe : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      go_etcd_io.etcd.server.v3.storage.schema.bucketIs b id name safe ⊢
      isBucket b ⟨id, name, safe⟩ := by
  iintro ⟨#Hpkg, #Hb⟩
  iunfold go_etcd_io.etcd.server.v3.storage.schema.bucketIs at Hb
  icases Hb with ⟨%s, %Hb, #Hs⟩
  subst Hb
  iunfold isBucket
  iexists ⟨go_etcd_io.etcd.server.v3.storage.schema.bucket.ty,
    #({ id' := id, name' := s, safeRangeBucket' := safe } :
      go_etcd_io.etcd.server.v3.storage.schema.bucket)⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply (hID _)
    iapply HΦ; itrivial
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply (hName _)
    iapply HΦ; iexact Hs
  · iintro !> %Φ !> - HΦ
    wp_apply (hSafe _)
    iapply HΦ; itrivial

/-- schema's `Key` bucket is the `Bucket` `keyBI`. -/
theorem key_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ⊢ isBucket b keyBI := by
  unfold keyBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, ⟨%b0, #Hk0, #Hb0⟩, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

/-- schema's `Meta` bucket is the `Bucket` `metaBI`. -/
theorem meta_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ⊢ isBucket b metaBI := by
  unfold metaBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%b0, #Hk0, #Hb0⟩, -, -, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

/-- schema's `Lease` bucket is the `Bucket` `leaseBI` (leases T3, 2026-10-25). -/
theorem lease_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b ⊢ isBucket b leaseBI := by
  unfold leaseBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

end buckets

/-! ## The slices a read returns -/

section slices
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- A single key's read, its slices made read-only: mvcc's `keyVals`. -/
theorem kvsOutRd_keyVals (rtx : Loc) (keys vals : GoSlice) (m : Bucket) (k : GoString) :
    kvsOutRd (GF := GF) rtx keys vals (match m.lookup k with | some v => [(k, v)] | none => []) ⊢
      |==> keyVals (rdB rtx) keys vals m k := by
  unfold keyVals
  cases hm : m.lookup k with
  | none =>
    dsimp only
    iintro H
    iunfold kvsOutRd at H
    icases H with ⟨%ks, %vs, Hk, -, Hv, -, #Hrk, #Hrv⟩
    ihave %Hlk := rdSlices_length rtx ks _ $$ Hrk
    ihave %Hlv := rdSlices_length rtx vs _ $$ Hrv
    simp only [List.map_nil, List.length_nil, List.length_eq_zero_iff] at Hlk Hlv
    subst Hlk Hlv
    imod ownSlice_persist $$ Hk with #Hk
    imod ownSlice_persist $$ Hv with #Hv
    imodintro
    iframe Hk Hv
  | some v =>
    dsimp only
    iintro H
    iunfold kvsOutRd at H
    icases H with ⟨%ks, %vs, Hk, -, Hv, -, #Hrk, #Hrv⟩
    ihave %Hlk := rdSlices_length rtx ks _ $$ Hrk
    ihave %Hlv := rdSlices_length rtx vs _ $$ Hrv
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at Hlk Hlv
    obtain ⟨ksl, rfl⟩ := List.length_eq_one_iff.1 Hlk
    obtain ⟨vsl, rfl⟩ := List.length_eq_one_iff.1 Hlv
    iunfold rdSlices at Hrk Hrv
    icases Hrk with ⟨-, #Hrk⟩
    icases Hrv with ⟨-, #Hrv⟩
    irevert Hrk Hrv
    simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left]
    iintro #Hrk #Hrv
    ihave #Hrk1 := BigSepL.bigSepL_singleton.1 $$ Hrk
    ihave #Hrv1 := BigSepL.bigSepL_singleton.1 $$ Hrv
    imod ownSlice_persist $$ Hk with #Hk
    imod ownSlice_persist $$ Hv with #Hv
    imodintro
    iexists ksl, vsl
    iframe Hk Hv Hrk1 Hrv1

end slices

/-! ## The readers -/

/-- The "safe range bucket" discipline on a readers' state, for the `Key` bucket: the read
buffer's keys are above bbolt's (no key both in bbolt's data and in the read buffer, which the
backend's range would return twice), and the bucket is not enormous (the range's limit is
`2^63 - 1`). What a range of the `Key` bucket needs (`rtRange_safe`). -/
def keySafe (rv : RView) : Prop :=
  (∀ (kc vc : GoString) (e : Ent),
    (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).lookup kc = some vc →
    e ∈ bkOf rv.2.bks (W64 1) → strLt kc e.1) ∧
  (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).size +
    (bkOf rv.2.bks (W64 1)).length < 2 ^ 62

/-- The safe-range state of the `Key` bucket, from the backend's invariant (`safeRv`) and the
size. -/
theorem keySafe_of {P : BParams} (hP : bridgeParams P) {rv : RView} (h : safeRv P rv)
    (hsz : (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).size +
      (bkOf rv.2.bks (W64 1)).length < 2 ^ 62) : keySafe rv := by
  refine ⟨fun kc vc e hc he => ?_, hsz⟩
  have hk := hP.1
  unfold BParams.has keyBI at hk
  exact h _ _ hk (by rw [hP.2.2.2.1]; simp) kc vc e hc he

section readers
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The premise of the range read**: the shared read transaction's states hold fewer than
`2^62` entries of the `Key` bucket (bbolt's and the read buffer's). The range read's limit is
`2^63 - 1` entries, and nothing bounds a bucket's size: bbolt's contract has no bound, nor has
the store's log (each revision may have up to `2^63` changes). The order half of the safe-range
discipline is the backend's invariant now (`rtHeld_safe`: the read buffer's `Key` entries above
bbolt's, 2026-10-13, unit 5); this premise is only the size (2026-10-13; it replaces the unit-4
premise `rangeSafe`, which also assumed the order). -/
def keySized (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(□ ∀ (rtx : Loc) (rv : RView), rtHeld γ P b rtx rv -∗ rtHeld γ P b rtx rv ∗
    ⌜(bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).size +
      (bkOf rv.2.bks (W64 1)).length < 2 ^ 62⌝)

instance keySized_persistent (γ : BNames) (P : BParams) (b : Loc) :
    Persistent (keySized (GF := GF) γ P b) := by
  unfold keySized; infer_instance

/-- A concurrent read transaction's token: its state, the way back to the reader's slot, and
the backend open. -/
def crtTok (γ : BNames) (P : BParams) (b crt rtx : Loc) (rv : RView) (qo : Qp) : IProp GF :=
  iprop(crtSnap γ P b crt rtx rv ∗ (crTok γ b -∗ rdTok γ P b) ∗ bOpen γ qo)

/-- The shared read transaction's token: held, and the backend open. -/
def rtTok (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (qo : Qp) : IProp GF :=
  iprop(rtHeld γ P b rtx rv ∗ bOpen γ qo)

/-- A concurrent read transaction's state is well formed. -/
theorem crtSnap_wf (γ : BNames) (P : BParams) (b crt rtx : Loc) (rv : RView) :
    crtSnap (GF := GF) γ P b crt rtx rv ⊢ crtSnap γ P b crt rtx rv ∗ ⌜rv.2.Wf⌝ := by
  iintro Hc
  iunfold crtSnap at Hc
  icases Hc with ⟨%m, %Pb, %cm, %tm, %wg, %γw, %γo, %γt, %k, %q, %rt, #Hrt, #Htm, Hrb, #Hrtx,
    #Hcm, #Htm', #Hwg, Hown, #Hg, Hsh, #Hsnap, #Hintv, #Hwgi, %Hwf⟩
  isplitl
  · iunfold crtSnap
    iexists m, Pb, cm, tm, wg, γw, γo, γt, k, q, rt
    iframe; iframe #
    ipureintro; exact Hwf
  · ipureintro; exact Hwf.1

/-- The held shared read transaction's state is well formed. -/
theorem rtHeld_wf (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) :
    rtHeld (GF := GF) γ P b rtx rv ⊢ rtHeld γ P b rtx rv ∗ ⌜rv.2.Wf⌝ := by
  unfold rtHeld rtResAt rtRest rtCore
  iintro ⟨%rt, %rd, %H, #Hrt, Hrl, ⟨%m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs,
    Hcur, Hcln, Hhist, Hrtxf, Hwgf, %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩, %Hrtx, Hcr⟩
  isplitl
  · iexists rt, rd, H
    iframe; iframe #
    ipureintro; exact ⟨⟨Hok, Hf⟩, Hrtx⟩
  · ipureintro; exact Hf.1

/-- A concurrent read transaction's single-key read of the `Key` bucket (mvcc's
`keyRangeSpec`). -/
theorem crt_keyRange (hUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b crt rtx : Loc)
    (rv : RView) (qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
      keyRangeSpec ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty, #crt⟩
        m (rdB rtx) (crtTok γ P b crt rtx rv qo) := by
  iintro ⟨#Hpkg, #Hsch⟩
  iunfold keyRangeSpec
  iintro %bk %key %k %dq !> %Φ ⟨#HK, Ht, Hkey⟩ HΦ
  iunfold crtTok at Ht
  icases Ht with ⟨Hsnap, Hback, Ho⟩
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  icases crtSnap_wf γ P b crt rtx rv $$ Hsnap with ⟨Hsnap, %Hwf⟩
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b crt rtx rv bk keyBI key slice.nil k [] dq DFrac.discard (W64 0)
      (by simp) (Or.inr rfl) hP.1) $$ [$Hsnap $Hbk $Hkey $Hnil] as %ks %vs ⟨Hsnap, Hkey, -, Hout⟩
  irevert Hout
  rw [rtRange_single P rv keyBI k (W64 0) hP.1 Hwf, show keyBI.name =
    go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl, vOf_key hP hv]
  iintro Hout
  imod kvsOutRd_keyVals rtx ks vs m k $$ Hout with #Hkv
  imodintro
  iapply HΦ
  iframe Hkey Hkv
  iunfold crtTok
  iframe

/-- `readTx.UnsafeRange` at `rtHeld` (its share of bbolt's transaction, `rtHeld_eq`). -/
theorem rtUR_held (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt rtx : Loc) (rv : RView) (qo : Qp)
    (bk : GoInterface) (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString)
    (dk de : DFrac) (limit : w64) (h1 : endKey = slice.nil ↔ eb = [])
    (h2 : sint.Z (rangeLimit eb limit) ≤ 1 ∨ bi.safe = true) (h3 : P.has bi) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ rtHeld γ P b rtx rv ∗ bOpen γ qo ∗
        isBucket bk bi ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
      (App (App (App (App (Val (rt @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty @!! go!"UnsafeRange"))
        (Val #bk)) (Val #key)) (Val #endKey)) (Val #limit))
    {{ (keys vals : GoSlice), RET (PairV #keys #vals); rtHeld γ P b rtx rv ∗ bOpen γ qo ∗
        key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗ kvsOutRd rtx keys vals (rtRange rv bi kb eb limit) }} := by
  have h := hUR γ P W Pk b rt rtx rv sync.rfrac.half qo bk bi key endKey kb eb dk de limit h1 h2 h3
  rw [← rtHeld_eq] at h
  exact h

/-- The held shared read transaction's single-key read of the `Key` bucket. -/
theorem rt_keyRange (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      keyRangeSpec ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv qo) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt⟩
  iunfold keyRangeSpec
  iintro %bk %key %k %dq !> %Φ ⟨#HK, Ht, Hkey⟩ HΦ
  iunfold rtTok at Ht
  icases Ht with ⟨Hh, Ho⟩
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  icases rtHeld_wf γ P b rtx rv $$ Hh with ⟨Hh, %Hwf⟩
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (rtUR_held hUR γ P W Pk b rt rtx rv qo bk keyBI key slice.nil k [] dq DFrac.discard (W64 0)
      (by simp) (Or.inr rfl) hP.1) $$ [$Hb $Hrt $Hh $Ho $Hbk $Hkey $Hnil]
      as %ks %vs ⟨Hh, Ho, Hkey, -, Hout⟩
  irevert Hout
  rw [rtRange_single P rv keyBI k (W64 0) hP.1 Hwf, show keyBI.name =
    go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl, vOf_key hP hv]
  iintro Hout
  imod kvsOutRd_keyVals rtx ks vs m k $$ Hout with #Hkv
  imodintro
  iapply HΦ
  iframe Hkey Hkv
  iunfold rtTok
  iframe

end readers

/-! ## The range of a safe bucket -/

section range
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The entries of a key-sorted list with a key in `[klo, khi)`, as `Range` and the cursor
loop take them (the first not below `klo`, while below `khi`). -/
def window (es : List Ent) (klo khi : GoString) : List Ent :=
  (es.dropWhile (fun e => decide (strLt e.1 klo))).takeWhile (fun e => decide (strLt e.1 khi))

theorem window_sublist (es : List Ent) (klo khi : GoString) : (window es klo khi).Sublist es :=
  (List.takeWhile_sublist _).trans (List.dropWhile_sublist _)

theorem not_strLt_iff_le (a b : GoString) : ¬ strLt a b ↔ go.GoStringLe b a := by
  constructor
  · intro h
    rcases strLt_total h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · intro h h'
    rcases h with h | h
    · subst h; exact go.goStringLt_irrefl _ h'
    · exact go.goStringLt_asymm h h'

theorem mem_takeWhile_sorted {es : List Ent} (hs : entsSorted es) (khi : GoString) (e : Ent) :
    e ∈ es.takeWhile (fun e => decide (strLt e.1 khi)) ↔ e ∈ es ∧ strLt e.1 khi := by
  induction es with
  | nil => simp
  | cons a t ih =>
    have ht : entsSorted t := (List.pairwise_cons.1 hs).2
    have hall : ∀ y ∈ t, strLt a.1 y.1 := (List.pairwise_cons.1 hs).1
    rw [List.takeWhile_cons]
    by_cases hq : strLt a.1 khi
    · simp only [decide_eq_true hq, ↓reduceIte, List.mem_cons, ih ht]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hq⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    · simp only [decide_eq_false hq, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, false_iff,
        not_and, List.mem_cons]
      rintro (rfl | h1) h2
      · exact hq h2
      · have := hall e h1
        rcases strLt_total hq with h3 | h3
        · rw [h3] at this; exact go.goStringLt_asymm this h2
        · exact go.goStringLt_asymm (go.goStringLt_trans h3 this) h2

theorem mem_dropWhile_sorted {es : List Ent} (hs : entsSorted es) (klo : GoString) (e : Ent) :
    e ∈ es.dropWhile (fun e => decide (strLt e.1 klo)) ↔ e ∈ es ∧ ¬ strLt e.1 klo := by
  induction es with
  | nil => simp
  | cons a t ih =>
    have ht : entsSorted t := (List.pairwise_cons.1 hs).2
    have hall : ∀ y ∈ t, strLt a.1 y.1 := (List.pairwise_cons.1 hs).1
    rw [List.dropWhile_cons]
    by_cases hp : strLt a.1 klo
    · simp only [decide_eq_true hp, ↓reduceIte, ih ht, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact absurd hp h2
        · exact ⟨h1, h2⟩
    · simp only [decide_eq_false hp, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (rfl | h1)
        · exact ⟨Or.inl rfl, hp⟩
        · refine ⟨Or.inr h1, fun h2 => ?_⟩
          have := hall e h1
          rcases strLt_total hp with h3 | h3
          · rw [← h3] at h2; exact go.goStringLt_asymm this h2
          · exact go.goStringLt_asymm (go.goStringLt_trans h3 this) h2
      · rintro ⟨h1, -⟩; exact h1

/-- The window of a sorted list: its entries with a key in `[klo, khi)`. -/
theorem mem_window {es : List Ent} (hs : entsSorted es) (klo khi : GoString) (e : Ent) :
    e ∈ window es klo khi ↔ e ∈ es ∧ go.GoStringLe klo e.1 ∧ strLt e.1 khi := by
  unfold window
  rw [mem_takeWhile_sorted (hs.sublist (List.dropWhile_sublist _)), mem_dropWhile_sorted hs,
    not_strLt_iff_le, and_assoc]

/-- `bbRange` of a range (an end key) is the window, at most `limit`. -/
theorem bbRange_window (es : List Ent) (klo khi : GoString) (lim : w64) (hne : khi ≠ []) :
    bbRange es klo khi lim = (window es klo khi).take (sint.Z lim).toNat := by
  unfold bbRange window
  split
  · rename_i h; rw [h]; simp
  · rename_i e rest h
    rw [h, if_neg hne]

/-- The cursor's range (an end key) is the window, at most `limit` (all if `limit ≤ 0`). -/
theorem cursorRange_window (es : List Ent) (klo khi : GoString) (lim : w64) (hne : khi ≠ []) :
    cursorRange es klo khi lim = (window es klo khi).take
      (if sint.Z lim ≤ 0 then 2 ^ 63 - 1 else (sint.Z lim).toNat) := by
  unfold cursorRange window seekIdx
  simp only [hne, ↓reduceIte]
  have hd : ∀ l : List Ent, l.drop (l.takeWhile (fun e => decide (strLt e.1 klo))).length =
      l.dropWhile (fun e => decide (strLt e.1 klo)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [List.takeWhile_cons, List.dropWhile_cons]
      split <;> simp [ih]
  rw [hd es]

/-- In a sorted list, the newest value of a key is its value. -/
theorem lastVal_sorted {es : List Ent} (hs : entsSorted es) (k v : GoString) :
    lastVal es k = some v ↔ (k, v) ∈ es := by
  induction es with
  | nil => simp [lastVal]
  | cons a t ih =>
    have ht : entsSorted t := (List.pairwise_cons.1 hs).2
    have hall : ∀ y ∈ t, strLt a.1 y.1 := (List.pairwise_cons.1 hs).1
    rw [lastVal_cons, List.mem_cons]
    by_cases ha : a.1 = k
    · have hnone : lastVal t k = none := by
        apply lastVal_eq_none
        intro e he hek
        have := hall e he
        rw [hek, ha] at this
        exact go.goStringLt_irrefl _ this
      rw [hnone, Option.none_or, if_pos ha]
      constructor
      · intro h; left; obtain ⟨a1, a2⟩ := a; simp only at ha; subst ha; cases h; rfl
      · rintro (h | h)
        · rw [← h]
        · have := hall _ h
          simp only at this; rw [ha] at this; exact absurd this (go.goStringLt_irrefl _)
    · rw [if_neg ha, Option.or_none, ih ht]
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · rw [← h] at ha; exact absurd rfl ha
        · exact h

theorem mem_bktEnts (m : BktData) (e : Ent) : e ∈ bktEnts m ↔ m.lookup e.1 = some e.2 := by
  unfold bktEnts
  rw [(List.mergeSort_perm m.toList entLe).mem_iff]
  exact GMap.mem_toList m e.1 e.2

theorem bktEnts_length (m : BktData) : (bktEnts m).length = m.size := by
  unfold bktEnts GMap.size
  exact List.length_mergeSort _

theorem dget_bktOf (D : Data) (n k : GoString) : dget D n k = (bktOf D n).lookup k := by
  unfold dget bktOf
  cases D.lookup n <;> rfl

/-- Two sorted windows, the first's keys below the second's, of a bucket whose entries are the
second list's over the first's: the bucket's range. -/
theorem windows_range (Cs Rs : List Ent) (C : BktData) (m : Bucket) (klo khi : GoString)
    (hCs : ∀ e, e ∈ Cs ↔ C.lookup e.1 = some e.2) (hCsort : entsSorted Cs)
    (hRsort : entsSorted Rs) (hm : ∀ k, m.lookup k = (lastVal Rs k).or (C.lookup k))
    (hsafe : ∀ (kc vc : GoString) (e : Ent), C.lookup kc = some vc → e ∈ Rs → strLt kc e.1) :
    window Cs klo khi ++ window Rs klo khi = bucketRange m klo khi := by
  symm
  apply (bucketRange_eq_iff m klo khi _).2
  have hcross : ∀ a ∈ window Cs klo khi, ∀ b ∈ window Rs klo khi, strLt a.1 b.1 := by
    intro a ha b hb
    have ha' := (hCs a).1 ((window_sublist _ _ _).subset ha)
    exact hsafe a.1 a.2 b ha' ((window_sublist _ _ _).subset hb)
  constructor
  · rw [List.map_append, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.pairwise_map.2 (hCsort.sublist (window_sublist _ _ _))
    · exact List.pairwise_map.2 (hRsort.sublist (window_sublist _ _ _))
    · intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      exact hcross a' ha' b' hb'
  · intro k v
    rw [List.mem_append, mem_window hCsort, mem_window hRsort, hm, hCs]
    simp only
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨?_, h2, h3⟩
        have : lastVal Rs k = none := by
          apply lastVal_eq_none
          intro e he hek
          have := hsafe k v e h1 he
          rw [hek] at this
          exact go.goStringLt_irrefl _ this
        rw [this, Option.none_or, h1]
      · refine ⟨?_, h2, h3⟩
        rw [(lastVal_sorted hRsort k v).2 h1, Option.some_or]
    · rintro ⟨h1, h2, h3⟩
      cases hl : lastVal Rs k with
      | some v' =>
        rw [hl, Option.some_or] at h1
        cases h1
        exact Or.inr ⟨(lastVal_sorted hRsort k _).1 hl, h2, h3⟩
      | none =>
        rw [hl, Option.none_or] at h1
        exact Or.inl ⟨h1, h2, h3⟩

/-- **A limited range of a safe `Key` bucket** in a readers' state is a sublist of the bucket's
range: a prefix of bbolt's window, then a prefix of the read buffer's (the restore plan's R4b). -/
theorem rtRange_sublist {P : BParams} (hP : bridgeParams P) {rv : RView} (hR : rv.2.Wf)
    (hs : keySafe rv) {m : Bucket} (hv : keyView (vData P rv) m) (klo khi : GoString)
    (hne : khi ≠ []) (lim : w64) :
    (rtRange rv keyBI klo khi lim).Sublist (bucketRange m klo khi) := by
  have hk := hP.1
  unfold BParams.has keyBI at hk
  simp only at hk
  have hRsort : entsSorted (bkOf rv.2.bks (W64 1)) := by
    unfold bkOf
    cases h : rv.2.bks.lookup (W64 1) with
    | none => exact entsSorted_nil
    | some es => exact hR _ es h
  have hm : ∀ k, m.lookup k = (lastVal (bkOf rv.2.bks (W64 1)) k).or
      ((bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).lookup k) := by
    intro k
    rw [← vOf_key hP hv k]
    unfold vOf ovB
    rw [hk, Option.bind_some, dget_bktOf]
  have hwin := windows_range (bktEnts (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName))
    (bkOf rv.2.bks (W64 1)) (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName) m klo khi
    (mem_bktEnts _) (bktEnts_sorted _) hRsort hm hs.1
  rw [← hwin]
  unfold rtRange
  simp only [show keyBI.id = W64 1 from rfl,
    show keyBI.name = go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl]
  rw [bbRange_window _ _ _ _ hne]
  split
  · exact (List.take_sublist _ _).trans (List.sublist_append_right _ _)
  · rw [cursorRange_window _ _ _ _ hne]
    exact (List.take_sublist _ _).append (List.take_sublist _ _)

/-- **A limited range of a `Key` bucket over a clean read buffer** (nothing off the hook's
buckets, `rbClean`) is the range's first `limit` entries: bbolt's window alone (the restore
plan's R5a; with entries in the buffer it is not, `issues/etcd-unsafe-range-limit-buffer.md`). -/
theorem rtRange_clean {P : BParams} (hP : bridgeParams P) {rv : RView} (hR : rv.2.Wf)
    (hs : keySafe rv) {m : Bucket} (hv : keyView (vData P rv) m) (hcl : rbClean P rv.2)
    (klo khi : GoString) (hne : khi ≠ []) (lim : w64) (hlim : 0 < sint.Z lim) :
    rtRange rv keyBI klo khi lim = (bucketRange m klo khi).take (sint.Z lim).toNat := by
  have hk := hP.1
  unfold BParams.has keyBI at hk
  simp only at hk
  have hb0 : bkOf rv.2.bks (W64 1) = [] := hcl _ _ hk (key_not_HB hP)
  have hm : ∀ k, m.lookup k = (lastVal (bkOf rv.2.bks (W64 1)) k).or
      ((bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).lookup k) := by
    intro k
    rw [← vOf_key hP hv k]
    unfold vOf ovB
    rw [hk, Option.bind_some, dget_bktOf]
  have hwin := windows_range (bktEnts (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName))
    (bkOf rv.2.bks (W64 1)) (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName) m klo khi
    (mem_bktEnts _) (bktEnts_sorted _) (by rw [hb0]; exact entsSorted_nil) hm hs.1
  rw [hb0] at hwin
  have hw0 : window ([] : List Ent) klo khi = [] := by unfold window; rfl
  rw [hw0, List.append_nil] at hwin
  rw [← hwin]
  unfold rtRange rangeLimit
  simp only [show keyBI.id = W64 1 from rfl,
    show keyBI.name = go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl, hne,
    ↓reduceIte, show ¬ sint.Z lim ≤ 0 from by omega, hb0]
  have hbb : bbRange ([] : List Ent) klo khi lim = [] := by unfold bbRange; rfl
  rw [hbb]
  simp only [List.length_nil, List.append_nil]
  rw [if_neg (by omega), cursorRange_window _ _ _ _ hne]
  have hl0 : lim - W64 (0 : Nat) = lim := by word
  rw [hl0, if_neg (by omega)]

/-- **A range of a safe `Key` bucket** in a readers' state is the bucket's range: bbolt's
window then the read buffer's, the latter's keys above the former's. -/
theorem rtRange_safe {P : BParams} (hP : bridgeParams P) {rv : RView} (hR : rv.2.Wf)
    (hs : keySafe rv) {m : Bucket} (hv : keyView (vData P rv) m) (klo khi : GoString)
    (hne : khi ≠ []) :
    rtRange rv keyBI klo khi (W64 0) = bucketRange m klo khi := by
  have hk := hP.1
  unfold BParams.has keyBI at hk
  simp only at hk
  have hRsort : entsSorted (bkOf rv.2.bks (W64 1)) := by
    unfold bkOf
    cases h : rv.2.bks.lookup (W64 1) with
    | none => exact entsSorted_nil
    | some es => exact hR _ es h
  have hm : ∀ k, m.lookup k = (lastVal (bkOf rv.2.bks (W64 1)) k).or
      ((bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName).lookup k) := by
    intro k
    rw [← vOf_key hP hv k]
    unfold vOf ovB
    rw [hk, Option.bind_some, dget_bktOf]
  have hwin := windows_range (bktEnts (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName))
    (bkOf rv.2.bks (W64 1)) (bktOf rv.1 go_etcd_io.etcd.server.v3.storage.schema.keyName) m klo khi
    (mem_bktEnts _) (bktEnts_sorted _) hRsort hm hs.1
  have hlen := hs.2
  rw [← bktEnts_length] at hlen
  have hwR := (window_sublist (bkOf rv.2.bks (W64 1)) klo khi).length_le
  have hwC := (window_sublist (bktEnts (bktOf rv.1
    go_etcd_io.etcd.server.v3.storage.schema.keyName)) klo khi).length_le
  have hlim : rangeLimit khi (W64 0) = W64 (2 ^ 63 - 1) := by
    unfold rangeLimit; simp [hne]
  have hlimZ : sint.Z (W64 (2 ^ 63 - 1)) = 2 ^ 63 - 1 := by rfl
  unfold rtRange
  simp only [hlim, show keyBI.id = W64 1 from rfl,
    show keyBI.name = go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl]
  rw [bbRange_window _ _ _ _ hne, hlimZ]
  rw [List.take_of_length_le (by
    have : ((2 : Int) ^ 63 - 1).toNat = 2 ^ 63 - 1 := rfl
    rw [this]; omega)]
  rw [if_neg (by omega), cursorRange_window _ _ _ _ hne]
  have hz : sint.Z (W64 (2 ^ 63 - 1) - W64 ((window (bkOf rv.2.bks (W64 1)) klo khi).length)) =
      2 ^ 63 - 1 - (window (bkOf rv.2.bks (W64 1)) klo khi).length := by
    have : ((window (bkOf rv.2.bks (W64 1)) klo khi).length : Int) < 2 ^ 62 := by omega
    word
  rw [hz, if_neg (by omega), List.take_of_length_le (by omega)]
  exact hwin

end range

/-! ## The slices of a range read -/

section rangeSlices
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The zipped read slices of the keys and the values, by index. -/
theorem zip_pairs (rtx : Loc) : ∀ (l : List Ent) (ks vs : List GoSlice),
    ks.length = l.length → vs.length = l.length →
    ([∗list] x ∈ ks.zip (l.map Prod.fst), rdB (GF := GF) rtx x.1 x.2) ∗
      ([∗list] x ∈ vs.zip (l.map Prod.snd), rdB rtx x.1 x.2) ⊢
      [∗list] i ↦ p ∈ l, ∃ ksl vsl : GoSlice, ⌜ks[i]? = some ksl ∧ vs[i]? = some vsl⌝ ∗
        □ rdB rtx ksl p.1 ∗ □ rdB rtx vsl p.2 := by
  intro l
  induction l with
  | nil =>
    intro ks vs _ _
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons p l ih =>
    intro ks vs hk hv
    cases ks with
    | nil => simp at hk
    | cons k0 ks =>
      cases vs with
      | nil => simp at hv
      | cons v0 vs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hk hv
        simp only [List.map_cons, List.zip_cons_cons]
        iintro ⟨#Hk, #Hv⟩
        icases BigSepL.bigSepL_cons.1 $$ Hk with ⟨#Hk0, #Hk⟩
        icases BigSepL.bigSepL_cons.1 $$ Hv with ⟨#Hv0, #Hv⟩
        iapply BigSepL.bigSepL_cons.2
        isplitl []
        · iexists k0, v0
          isplitl []
          · ipureintro; exact ⟨rfl, rfl⟩
          iframe Hk0 Hv0
        ihave #Hrest := (ih ks vs hk hv) $$ [$Hk $Hv]
        have hmono := BigSepL.bigSepL_mono (PROP := IProp GF) (l := l)
          (Φ := fun i (p : Ent) => iprop(∃ ksl vsl : GoSlice, ⌜ks[i]? = some ksl ∧ vs[i]? = some vsl⌝ ∗
            □ rdB rtx ksl p.1 ∗ □ rdB rtx vsl p.2))
          (Ψ := fun i (p : Ent) => iprop(∃ ksl vsl : GoSlice,
            ⌜(k0 :: ks)[i + 1]? = some ksl ∧ (v0 :: vs)[i + 1]? = some vsl⌝ ∗
            □ rdB rtx ksl p.1 ∗ □ rdB rtx vsl p.2))
          (fun {i x} _ => by
            iintro ⟨%ksl, %vsl, %Hi, #H1, #H2⟩
            iexists ksl, vsl
            iframe H1 H2
            ipureintro; exact Hi)
        iapply hmono $$ Hrest

/-- A range read, its slices made read-only: mvcc's `pairVals`. -/
theorem kvsOutRd_pairVals (rtx : Loc) (keys vals : GoSlice) (res : List Ent) :
    kvsOutRd (GF := GF) rtx keys vals res ⊢ |==> pairVals (rdB rtx) keys vals res := by
  iintro H
  iunfold kvsOutRd at H
  icases H with ⟨%ks, %vs, Hk, -, Hv, -, #Hrk, #Hrv⟩
  ihave %Hlk := rdSlices_length rtx ks _ $$ Hrk
  ihave %Hlv := rdSlices_length rtx vs _ $$ Hrv
  simp only [List.length_map] at Hlk Hlv
  iunfold rdSlices at Hrk Hrv
  icases Hrk with ⟨-, #Hrk⟩
  icases Hrv with ⟨-, #Hrv⟩
  imod ownSlice_persist $$ Hk with #Hk
  imod ownSlice_persist $$ Hv with #Hv
  imodintro
  iunfold pairVals
  iexists ks, vs
  iframe Hk Hv
  isplitl []
  · ipureintro; exact ⟨Hlk, Hlv⟩
  iapply zip_pairs rtx res ks vs Hlk Hlv $$ [$Hrk $Hrv]

end rangeSlices

/-! ## The read transactions as mvcc's snapshots -/

section snaps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- A non-empty end key is not the nil slice. -/
theorem endKey_nil_iff (hi : GoSlice) (khi : GoString) (dq : DFrac) (hne : khi ≠ []) :
    (hi ↦*{dq} khi : IProp GF) ⊢ ⌜hi = slice.nil ↔ khi = []⌝ := by
  iintro Hhi
  ihave %Hlen := ownSlice_len _ _ _ $$ Hhi
  ipureintro
  constructor
  · intro h
    subst h
    have : khi.length = 0 := by rw [Hlen.1]; rfl
    exact absurd (List.length_eq_zero_iff.1 this) hne
  · intro h; exact absurd h hne

/-- The held shared read transaction's range read of a safe `Key` bucket. -/
theorem rt_rangeRead (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ keySized γ P b ⊢
      keyRangeReadSpec ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv qo) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hsafe⟩
  iunfold keyRangeReadSpec
  iintro %bk %lo %hi %klo %khi %dqlo %dqhi !> %Φ ⟨#HK, Ht, Hlo, Hhi, %Hne⟩ HΦ
  iunfold rtTok at Ht
  icases Ht with ⟨Hh, Ho⟩
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  icases rtHeld_wf γ P b rtx rv $$ Hh with ⟨Hh, %Hwf⟩
  icases rtHeld_safe γ P b rtx rv $$ Hh with ⟨Hh, %Hsf⟩
  iunfold keySized at Hsafe
  icases Hsafe $$ %rtx %rv Hh with ⟨Hh, %Hsz⟩
  have Hks := keySafe_of hP Hsf Hsz
  ihave %Hiff := endKey_nil_iff hi khi dqhi Hne $$ Hhi
  iapply wp_fupd
  wp_apply (rtUR_held hUR γ P W Pk b rt rtx rv qo bk keyBI lo hi klo khi dqlo dqhi (W64 0) Hiff
      (Or.inr rfl) hP.1) $$ [$Hb $Hrt $Hh $Ho $Hbk $Hlo $Hhi] as %ks %vs ⟨Hh, Ho, Hlo, Hhi, Hout⟩
  irevert Hout
  rw [rtRange_safe hP Hwf Hks hv klo khi Hne]
  iintro Hout
  imod kvsOutRd_pairVals rtx ks vs _ $$ Hout with #Hkv
  imodintro
  iapply HΦ
  iframe Hlo Hhi
  iunfold rangeVals
  iframe Hkv
  iunfold rtTok
  iframe

/-- The held shared read transaction's limited range read of a safe `Key` bucket (R4b). -/
theorem rt_rangeLim (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) (cl : Bool)
    (hcl : cl = true → rbClean P rv.2) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ keySized γ P b ⊢
      keyRangeLimSpec ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv qo) cl := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hsafe⟩
  iunfold keyRangeLimSpec
  iintro %bk %lo %hi %klo %khi %dqlo %dqhi %lim !> %Φ ⟨#HK, Ht, Hlo, Hhi, %Hne⟩ HΦ
  iunfold rtTok at Ht
  icases Ht with ⟨Hh, Ho⟩
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  icases rtHeld_wf γ P b rtx rv $$ Hh with ⟨Hh, %Hwf⟩
  icases rtHeld_safe γ P b rtx rv $$ Hh with ⟨Hh, %Hsf⟩
  iunfold keySized at Hsafe
  icases Hsafe $$ %rtx %rv Hh with ⟨Hh, %Hsz⟩
  have Hks := keySafe_of hP Hsf Hsz
  ihave %Hiff := endKey_nil_iff hi khi dqhi Hne $$ Hhi
  iapply wp_fupd
  wp_apply (rtUR_held hUR γ P W Pk b rt rtx rv qo bk keyBI lo hi klo khi dqlo dqhi lim Hiff
      (Or.inr rfl) hP.1) $$ [$Hb $Hrt $Hh $Ho $Hbk $Hlo $Hhi] as %ks %vs ⟨Hh, Ho, Hlo, Hhi, Hout⟩
  imod kvsOutRd_pairVals rtx ks vs _ $$ Hout with #Hkv
  imodintro
  iapply HΦ
  iframe Hlo Hhi
  iunfold rtTok
  iframe Hh Ho
  iexists _
  iframe Hkv
  ipureintro
  exact ⟨rtRange_sublist hP Hwf Hks hv klo khi Hne lim,
    fun hc hl => rtRange_clean hP Hwf Hks hv (hcl hc) klo khi Hne lim hl⟩


/-- `rtHeldF_lend` at a quarter of `readTx.mu`'s reader share. -/
theorem rtHeld_lendQ (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (qo : Qp) :
    rtHeld (GF := GF) γ P b rtx rv ∗ bOpen γ qo ⊢
      rtHeldF γ P b rtx rv sync.rfrac.half.half ∗ bOpen γ qo ∗ txLive rtx sync.rfrac.half.half := by
  have h := rtHeldF_lend (GF := GF) γ P b rtx rv qo sync.rfrac.half.half sync.rfrac.half.half
  rw [Qp.half_add_half] at h
  exact h

/-- `rtHeldF_return` at a quarter. -/
theorem rtHeld_returnQ (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) :
    rtHeldF (GF := GF) γ P b rtx rv sync.rfrac.half.half ∗ txLive rtx sync.rfrac.half.half ⊢
      rtHeld γ P b rtx rv := by
  have h := rtHeldF_return (GF := GF) γ P b rtx rv sync.rfrac.half.half sync.rfrac.half.half
  rw [Qp.half_add_half] at h
  exact h

/-- The held shared read transaction's limited range read with a share `p` of bbolt's
transaction (the restore plan's R5b: what the part that ranges keeps when the other is lent),
the readers' state's facts known (at the lend). -/
theorem rt_rangeLimF (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (p qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) (cl : Bool)
    (hcl : cl = true → rbClean P rv.2) (Hwf : rv.2.Wf) (Hks : keySafe rv) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      keyRangeLimSpec ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) iprop(rtHeldF γ P b rtx rv p ∗ bOpen γ qo) cl := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt⟩
  iunfold keyRangeLimSpec
  iintro %bk %lo %hi %klo %khi %dqlo %dqhi %lim !> %Φ ⟨#HK, ⟨Hh, Ho⟩, Hlo, Hhi, %Hne⟩ HΦ
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  ihave %Hiff := endKey_nil_iff hi khi dqhi Hne $$ Hhi
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b rt rtx rv p qo bk keyBI lo hi klo khi dqlo dqhi lim Hiff
      (Or.inr rfl) hP.1) $$ [$Hb $Hrt $Hh $Ho $Hbk $Hlo $Hhi] as %ks %vs ⟨Hh, Ho, Hlo, Hhi, Hout⟩
  imod kvsOutRd_pairVals rtx ks vs _ $$ Hout with #Hkv
  imodintro
  iapply HΦ
  iframe Hlo Hhi Hh Ho
  iexists _
  iframe Hkv
  ipureintro
  exact ⟨rtRange_sublist hP Hwf Hks hv klo khi Hne lim,
    fun hc hl => rtRange_clean hP Hwf Hks hv (hcl hc) klo khi Hne lim hl⟩

end snaps

/-! ## The read transactions -/

section readTxs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- A concurrent read transaction, locked (it always is), over the `Key` bucket `m`. -/
theorem crt_locked (hRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b crt rtx : Loc)
    (rv : RView) (m : Bucket) (hv : keyView (vData P rv) m) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
      keyReadLocked (bkRTx γ P b) false
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty, #crt⟩
        m (rdB rtx) (crtTok γ P b crt rtx rv rdOpen) := by
  iintro ⟨#Hpkg, #Hsch⟩
  iunfold keyReadLocked
  simp only [Bool.false_eq_true, ↓reduceIte]
  isplitr
  · iintro !> %Φ !> Ht HΦ
    iunfold crtTok at Ht
    icases Ht with ⟨Hsnap, Hback, Ho⟩
    wp_apply (hRU γ P W Pk b crt rtx rv) $$ [$Hsnap] as Hcr
    iapply HΦ
    iapply bkRT_x γ P b
    iunfold bkRT
    ihave Hrd := Hback $$ Hcr
    iframe Hrd Ho
  isplitr
  · iintro !>
    iapply crt_keyRange hUR hID hName hSafe hP γ W Pk b crt rtx rv rdOpen m hv $$ [$Hpkg $Hsch]
  isplitr
  · itrivial
  iunfold rdCap
  iintro !> %s %v #HRd Ht
  iunfold crtTok at Ht
  icases Ht with ⟨Hsnap, Hback, Ho⟩
  icases crtSnap_read γ P b crt rtx rv s v $$ [$Hsnap $HRd] with ⟨%dq, Hs, Hcl⟩
  iexists dq
  iframe Hs
  iintro Hs
  ihave Hsnap := Hcl $$ Hs
  iunfold crtTok
  iframe

/-- The held shared read transaction, over the `Key` bucket `m`. -/
theorem rt_locked (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (m : Bucket) (hv : keyView (vData P rv) m) (cl : Bool := false)
    (hcl : cl = true → rbClean P rv.2 := by simp) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ keySized γ P b ⊢
      keyReadLocked (bkRTx γ P b) true
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv rdOpen) cl := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hsafe⟩
  iunfold keyReadLocked
  simp only [↓reduceIte]
  isplitr
  · iintro !> %Φ !> Ht HΦ
    iunfold rtTok at Ht
    icases Ht with ⟨Hh, Ho⟩
    wp_apply (hRU γ P W Pk b rt rtx rv) $$ [$Hb $Hrt $Hh] as Hrd
    iapply HΦ
    iapply bkRT_x γ P b
    iunfold bkRT
    iframe Hrd Ho
  isplitr
  · iintro !>
    iapply rt_keyRange hUR hID hName hSafe hP γ W Pk b rt rtx rv rdOpen m hv $$ [$Hpkg $Hsch $Hb $Hrt]
  isplitr
  · isplitr
    · iintro !>
      iapply rt_rangeRead hUR hID hName hSafe hP γ W Pk b rt rtx rv rdOpen m hv
        $$ [$Hpkg $Hsch $Hb $Hrt $Hsafe]
    isplitr
    · iintro !>
      iapply rt_rangeLim hUR hID hName hSafe hP γ W Pk b rt rtx rv rdOpen m hv cl hcl
        $$ [$Hpkg $Hsch $Hb $Hrt $Hsafe]
    iintro !>
    iunfold rdSplit
    iintro Ht
    iunfold rtTok at Ht
    icases Ht with ⟨Hh, Ho⟩
    icases rtHeld_wf γ P b rtx rv $$ Hh with ⟨Hh, %Hwf⟩
    icases rtHeld_safe γ P b rtx rv $$ Hh with ⟨Hh, %Hsf⟩
    iunfold keySized at Hsafe
    icases Hsafe $$ %rtx %rv Hh with ⟨Hh, %Hsz⟩
    have Hks := keySafe_of hP Hsf Hsz
    icases rtHeld_lendQ γ P b rtx rv rdOpen $$ [$Hh $Ho] with ⟨Hh, Ho, Hl⟩
    iexists iprop(rtHeldF γ P b rtx rv sync.rfrac.half.half ∗ bOpen γ rdOpen),
      iprop(txLive rtx sync.rfrac.half.half)
    iframe Hh Ho Hl
    isplitr
    · iunfold rdCap
      iintro !> %s %v #HRd ⟨Hh, Ho⟩
      icases rtHeldF_read γ P b rtx rv _ rdOpen s v $$ [$Hh $Ho $HRd] with ⟨%dq, Hs, Hcl⟩
      iexists dq
      iframe Hs
      iintro Hs
      iapply Hcl $$ Hs
    isplitr
    · iunfold rdCap
      iintro !> %s %v #HRd Hl
      iunfold rdB at HRd
      icases HRd with (#Hs | #Hs)
      · iexists DFrac.discard
        iframe #
        iintro _
        iexact Hl
      icases txBytes_acc rtx s v _ $$ [$Hs $Hl] with ⟨%dq, Hsl, Hback⟩
      iexists dq
      iframe Hsl
      iexact Hback
    isplitr
    · iintro !>
      iapply rt_rangeLimF hUR hID hName hSafe hP γ W Pk b rt rtx rv _ rdOpen m hv cl hcl Hwf Hks
        $$ [$Hpkg $Hsch $Hb $Hrt]
    iintro ⟨Hh, Ho⟩ Hl
    iunfold rtTok
    iframe Ho
    iapply rtHeld_returnQ γ P b rtx rv $$ [$Hh $Hl]
  iunfold rdCap
  iintro !> %s %v #HRd Ht
  iunfold rtTok at Ht
  icases Ht with ⟨Hh, Ho⟩
  icases rtHeld_read γ P b rtx rv rdOpen s v $$ [$Hh $Ho $HRd] with ⟨%dq, Hs, Hcl⟩
  iexists dq
  iframe Hs
  iintro Hs
  ihave Hh := Hcl $$ Hs
  iunfold rtTok
  iframe

/-- **`ConcurrentReadTx()`** as mvcc's contract states it. -/
theorem bridge_crt (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc)
    (Del : GoString → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ⊢
      □ (∀ (q : Qp) (m : Bucket),
        {{ bkView γ q m ∗ bkRTx γ P b }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ConcurrentReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkView γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnap (bkView γ) (bkRTx γ P b) Del false rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb⟩ !> %q %m %Φ !> ⟨Hv, Hrt⟩ HΦ
  iunfold bkView at Hv
  icases Hv with ⟨%vd, Hv, %Hvd⟩
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  wp_apply (hCRT γ P W Pk b q rdOpen vd) $$ [$Hb $Hrd $Hv $Ho]
    as %crt %rtx %rv ⟨Hsnap, %Hrv, Hback, Hv, Ho⟩
  subst Hrv
  iapply HΦ
  isplitl [Hv]
  · iunfold bkView
    iexists (vData P rv)
    iframe Hv
    ipureintro; exact Hvd
  iexists (crtTok γ P b crt rtx rv rdOpen)
  isplitl [Hsnap Hback Ho]
  · iunfold crtTok; iframe
  iunfold keyReadSnap
  iintro !> %q' %Φ' !> ⟨HL, Hv'⟩ HΦ'
  wp_apply (hRL crt)
  iapply HΦ'
  iframe Hv'
  iexists m, (rdB rtx), (crtTok γ P b crt rtx rv rdOpen)
  iframe HL
  isplitr
  · iapply crt_locked hRU hUR hID hName hSafe hP γ W Pk b crt rtx rv m Hvd $$ [$Hpkg $Hsch]
  iapply snapThin_refl

/-- **`ReadTx()`** as mvcc's contract states it: the shared read transaction, whose `RLock`
finds the readers' state of the caller's view then (`rtHeld_view`). -/
theorem bridge_rt (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc)
    (Del : GoString → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ keySized γ P b ⊢
      □ (∀ (q : Qp) (m : Bucket),
        {{ bkView γ q m ∗ bkRTx γ P b }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkView γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnap (bkView γ) (bkRTx γ P b) Del true rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ !> %q %m %Φ !> ⟨Hv, Hrt⟩ HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrtf
  iapply HΦ
  iframe Hv
  iexists (bkRTx γ P b)
  iframe Hrt
  iunfold keyReadSnap
  iintro !> %q' %Φ' !> ⟨HL, Hv'⟩ HΦ'
  iunfold bkRTx at HL
  icases HL with ⟨Hrd, Ho⟩
  wp_apply (hRL γ P W Pk b rt rdOpen) $$ [$Hb $Hrtf $Hrd $Ho] as ⟨%rtx, %rv, Hh, Ho⟩
  iunfold bkView at Hv'
  icases Hv' with ⟨%vd, Hv', %Hvd⟩
  ihave %Hrv := rtHeld_view γ P b rtx rv q' vd $$ [$Hh $Hv']
  subst Hrv
  iapply HΦ'
  isplitl [Hv']
  · iunfold bkView
    iexists (vData P rv)
    iframe Hv'
    ipureintro; exact Hvd
  iexists m, (rdB rtx), (rtTok γ P b rtx rv rdOpen)
  isplitl [Hh Ho]
  · iunfold rtTok; iframe
  isplitr
  · iapply rt_locked hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m Hvd
      $$ [$Hpkg $Hsch $Hb $Hrtf $Hsafe]
  iapply snapThin_refl

/-- **`ReadTx()` over a clean view** (the restore plan's R5a): from a share of the clients' view
with the read buffer known clean, the read transaction's snapshot is the bucket itself, with the
limited range's prefix clause (`rtHeld_clean`, `rtRange_clean`). -/
theorem bridge_rt_clean (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ keySized γ P b ⊢
      □ (∀ (q : Qp) (m : Bucket),
        {{ bkViewC γ q m ∗ bkRTx γ P b }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkViewC γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnapC (bkViewC γ) (bkRTx γ P b) rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ !> %q %m %Φ !> ⟨Hv, Hrt⟩ HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrtf
  iapply HΦ
  iframe Hv
  iexists (bkRTx γ P b)
  iframe Hrt
  iunfold keyReadSnapC
  iintro !> %q' %Φ' !> ⟨HL, Hv'⟩ HΦ'
  iunfold bkRTx at HL
  icases HL with ⟨Hrd, Ho⟩
  wp_apply (hRL γ P W Pk b rt rdOpen) $$ [$Hb $Hrtf $Hrd $Ho] as ⟨%rtx, %rv, Hh, Ho⟩
  iunfold bkViewC at Hv'
  icases Hv' with ⟨%vd, Hv', %Hvd⟩
  icases rtHeld_clean γ P b rtx rv q' vd $$ [$Hh $Hv'] with ⟨Hh, Hv', %Hcl⟩
  obtain ⟨Hcl, Hrv⟩ := Hcl
  subst Hrv
  iapply HΦ'
  isplitl [Hv']
  · iunfold bkViewC
    iexists (vData P rv)
    iframe Hv'
    ipureintro; exact Hvd
  iexists (rdB rtx), (rtTok γ P b rtx rv rdOpen)
  isplitl [Hh Ho]
  · iunfold rtTok; iframe
  iapply rt_locked hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m Hvd true (fun _ => Hcl)
    $$ [$Hpkg $Hsch $Hb $Hrtf $Hsafe]

end readTxs

/-! ## The batch transaction -/

section batch
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The writer's contents' `Key` bucket, from its view. -/
theorem bktOf_of_sData {P : BParams} (hP : bridgeParams P) {S : Data} {m : Bucket}
    (h : keyView (sData P S) m) (k : GoString) :
    (bktOf S go_etcd_io.etcd.server.v3.storage.schema.keyName).lookup k = m.lookup k := by
  have := h go_etcd_io.etcd.server.v3.storage.schema.keyName k
  simp only [↓reduceIte] at this
  rw [← this]
  show _ = (if P.HB _ then none else vOf P (S, ⟨∅, W64 0⟩) _ k)
  rw [key_not_HB hP, vOf_emptyR, dget_bktOf]
  rfl

/-- A bucket's creation changes nothing the readers see. -/
theorem viewSame_create {P : BParams} {st : BSess} (bi : BucketInfo) (h : viewSame P st) :
    viewSame P (st.create bi) := by
  refine ⟨?_, h.2⟩
  show vData P (st.C, st.R) = sData P (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S)
  rw [h.1]
  unfold sData
  apply vData_eq_of_agree
  rw [vOf_emptyR, vOf_emptyR, dget_create]
  intro _ _ _; rfl

/-- The clients' view agrees with the batch lock's. -/
theorem batchLocked_view (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (q : Qp)
    (vd : VData) :
    batchLocked (GF := GF) γ P b st ∗ bView γ q vd ⊢
      batchLocked γ P b st ∗ bView γ q vd ∗ ⌜vd = vData P (st.C, st.R)⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt bView bViewC
  iintro ⟨⟨%t, %db, #Ht, Hmu, Hph, ⟨Hv, Hrest⟩, %Hwf⟩, ⟨%c, Hbv, Hc, Hl⟩⟩
  icombine Hv Hbv gives %Hag
  isplitl [Hmu Hph Hv Hrest]
  · iexists t, db
    iframe; iframe #
    ipureintro; exact Hwf
  isplitl [Hbv Hc Hl]
  · iexists c; iframe
  ipureintro; exact Hag.2.symm

/-- The batch lock's state is well formed. -/
theorem batchLocked_wf (γ : BNames) (P : BParams) (b : Loc) (st : BSess) :
    batchLocked (GF := GF) γ P b st ⊢ batchLocked γ P b st ∗ ⌜sessWf P st⌝ := by
  unfold batchLocked batchLockedAt
  iintro ⟨%t, %db, #Ht, Hmu, Hph, Hg, %Hwf⟩
  isplitl
  · iexists t, db
    iframe; iframe #
    ipureintro; exact Hwf
  ipureintro; exact Hwf

/-- The batch transaction's `LockInsideApply()`, as mvcc's contract states it. -/
theorem bt_lockIn (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ (Pre Q : IProp GF) (fv : val),
        {{ Pre ∗ bkRTx γ P b ∗ wbTok γ ∗ bkHookIs γ fv ∗
            □ ({{ Pk ∗ Pre }} (App (Val fv) (Val #())) {{ RET #(); Q }}) }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"LockInsideApply" #t))
            (Val #()))
        {{ RET #(); bkLocked γ P b [] ∗ W ∗ Q ∗ bkRTx γ P b }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %Pre %Q %fv %Φ !> ⟨Hpre, Hrt, Hwb, #Hhf, #Htr⟩ HΦ
  iunfold bkHookIs at Hhf
  icases Hhf with ⟨%f, ⟨%Hfv, %hf⟩, #Hhk⟩
  subst Hfv
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  wp_apply (hLI γ P W Pk b t rdOpen DFrac.discard f Pre Q) $$ [$Hb $Ht $Ho $Hhk $Hpre]
    as ⟨%st, Hl, %Hfree, HW, HQ, Ho, -⟩
  · iright
    iframe Htr
    ipureintro; exact hf
  iapply HΦ
  iframe HW HQ
  isplitl [Hl Hwb]
  · iunfold bkLocked
    iexists st
    iunfold bkLockedAt
    iframe
    ipureintro; exact sessPuts_free hP Hfree
  iunfold bkRTx
  iframe Hrd
  iexact Ho

/-- The batch transaction's `UnsafeSeqPut(schema.Key, k, v)`, as mvcc's contract states it. -/
theorem bt_seqPut (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ (l : Puts) (q : Qp) (m : Bucket) (bk : GoInterface) (key val : GoSlice) (k v : GoString),
        {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ bk ∗ bkLocked γ P b l ∗
            bkView γ q m ∗ key ↦*□ k ∗ val ↦*□ v ∗ ⌜keyPutOk m l k v⌝ }}
          (App (App (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"UnsafeSeqPut" #t))
            (Val #bk)) (Val #key)) (Val #val))
        {{ RET #(); bkLocked γ P b (l ++ [(k, v)]) ∗ bkView γ q m }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩ !> %l %q %m %bk %key %val %k %v %Φ !>
    ⟨#HK, Hl, Hvw, #Hk, #Hv, %Hok⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold bkLocked at Hl
  icases Hl with ⟨%st, Hl⟩
  iunfold bkLockedAt at Hl
  icases Hl with ⟨Hl, Hwb, %Hs⟩
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  icases batchLocked_wf γ P b st $$ Hl with ⟨Hl, %Hwf⟩
  iunfold bkView at Hvw
  icases Hvw with ⟨%vd, Hvw, %Hvd⟩
  icases batchLocked_view γ P b st q vd $$ [$Hl $Hvw] with ⟨Hl, Hvw, %Hag⟩
  subst Hag
  obtain ⟨hl, hk0, hk1, hbm, hord⟩ := Hok
  obtain ⟨hs', hpend⟩ := sessPuts_put HPw Hs hl
  have hW : ∀ e ∈ bkOf st.W.bks keyBI.id, strLt e.1 k := by
    rw [show keyBI.id = W64 1 from rfl, Hs.2.2.1]; exact hord
  have hS := sData_puts hP Hwf Hs Hvd
  have hSB : P.SB keyBI.name = true → ∀ kc vc,
      (bktOf st.S keyBI.name).lookup kc = some vc → strLt kc k := by
    intro _ kc vc hc
    rw [show keyBI.name = go_etcd_io.etcd.server.v3.storage.schema.keyName from rfl,
      bktOf_of_sData hP hS, foldl_insert_lookup] at hc
    cases hlv : lastVal l kc with
    | some v' =>
      obtain ⟨e, he, hek⟩ := lastVal_isSome_mem (l := l) (k := kc) (by rw [hlv]; rfl)
      rw [← hek]; exact hord e he
    | none =>
      rw [hlv, Option.none_or] at hc
      exact hbm kc vc hc
  wp_apply (hSP γ P W Pk b t st bk keyBI key val k v hP.1 hk0 hk1 hW hpend (key_not_hk hP k)
    hP.2.2.2.2.1 hSB)
    $$ [$Hb $Ht $Hl $Hbk $Hk $Hv] as Hl
  iapply HΦ
  isplitr [Hvw]
  · iunfold bkLocked
    iexists (st.put keyBI k v true)
    iunfold bkLockedAt
    iframe
    ipureintro; exact hs'
  iunfold bkView
  iexists (vData P (st.C, st.R))
  iframe Hvw
  ipureintro; exact Hvd

/-- The batch transaction's `Unlock()` after a session with no puts. -/
theorem bt_unlock0 (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ ({{ bkLocked γ P b [] ∗ W ∗ Pk }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"Unlock" #t)) (Val #()))
        {{ RET #(); True }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %Φ !> ⟨Hl, HW, HPk⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold bkLocked at Hl
  icases Hl with ⟨%st, Hl⟩
  iunfold bkLockedAt at Hl
  icases Hl with ⟨Hl, Hwb, %Hs⟩
  icases batchLocked_wf γ P b st $$ Hl with ⟨Hl, %Hwf⟩
  wp_apply (hUL γ P W Pk b t st iprop(True) Hs.2.2.2.2 (sessPuts_room HPw Hs)) $$ [$Hb $Ht $Hl $Hwb HW HPk]
  · ileft
    iframe HW HPk
    ipureintro; exact viewSame_noPuts hP Hwf Hs
  iapply HΦ; itrivial

/-- The batch transaction's `Unlock()` after a session with the puts `l`: written back into the
view. -/
theorem bt_unlock (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ (l : Puts) (m : Bucket) (Q : IProp GF),
        {{ bkLocked γ P b l ∗ bkView γ 1 m ∗
            (bkView γ 1 (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) -∗ W ∗ Q) ∗ Pk }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"Unlock" #t)) (Val #()))
        {{ RET #(); Q }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %l %m %Q %Φ !> ⟨Hl, Hv, Hwand, HPk⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold bkLocked at Hl
  icases Hl with ⟨%st, Hl⟩
  iunfold bkLockedAt at Hl
  icases Hl with ⟨Hl, Hwb, %Hs⟩
  icases batchLocked_wf γ P b st $$ Hl with ⟨Hl, %Hwf⟩
  iunfold bkView at Hv
  icases Hv with ⟨%vd, Hv, %Hvd⟩
  icases batchLocked_view γ P b st 1 vd $$ [$Hl $Hv] with ⟨Hl, Hv, %Hag⟩
  subst Hag
  -- (`wp_apply` aborts here without a message: the triple applied by hand)
  iapply (hUL γ P W Pk b t st Q Hs.2.2.2.2 (sessPuts_room HPw Hs)) $$ %Φ [Hl Hwb Hv HPk Hwand] HΦ
  iframe Hpkg Hb Ht Hl Hwb
  iright
  iexists (vData P (st.C, st.R))
  iframe Hv HPk
  iintro Hbv
  iapply Hwand
  iunfold bkView
  iexists (sData P st.S)
  iframe Hbv
  ipureintro; exact sData_puts hP Hwf Hs Hvd

/-- **The batch transaction's `Unlock()` after the lessor's delete** (`bkLockedD`; leases T3,
2026-10-25), as `bt_unlock0` and `bt_unlock`: the delete is in a hook's bucket, so the session
still changed nothing the readers see but its puts. -/
theorem bt_unlockD (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) (l : Puts) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      unlockAt ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty,
        #t⟩ (bkView γ) W Pk (bkLockedD γ P b l) l := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold unlockAt
  isplitr
  · iintro !> %Φ !> ⟨Hl, %Hn, HW, HPk⟩ HΦ
    subst Hn
    iunfold bkLockedD at Hl
    icases Hl with ⟨%st0, %bi, %k, Hl, Hwb, %Hs⟩
    obtain ⟨hs, hwf, hb⟩ := Hs
    obtain ⟨-, hroom⟩ := sessPuts_del_room HPw hs hwf
    wp_apply (hUL γ P W Pk b t (st0.del bi k) iprop(True) hs.2.2.2.2 hroom)
      $$ [$Hb $Ht $Hl $Hwb HW HPk]
    · ileft
      iframe HW HPk
      ipureintro; exact viewSame_del hb (viewSame_noPuts hP hwf hs)
    iapply HΦ; itrivial
  · iintro !> %m %Q %Φ !> ⟨Hl, Hv, Hwand, HPk⟩ HΦ
    iunfold bkLockedD at Hl
    icases Hl with ⟨%st0, %bi, %k, Hl, Hwb, %Hs⟩
    obtain ⟨hs, hwf, hb⟩ := Hs
    obtain ⟨-, hroom⟩ := sessPuts_del_room HPw hs hwf
    iunfold bkView at Hv
    icases Hv with ⟨%vd, Hv, %Hvd⟩
    icases batchLocked_view γ P b (st0.del bi k) 1 vd $$ [$Hl $Hv] with ⟨Hl, Hv, %Hag⟩
    subst Hag
    iapply (hUL γ P W Pk b t (st0.del bi k) Q hs.2.2.2.2 hroom) $$ %Φ [Hl Hwb Hv HPk Hwand] HΦ
    iframe Hpkg Hb Ht Hl Hwb
    iright
    iexists (vData P ((st0.del bi k).C, (st0.del bi k).R))
    iframe Hv HPk
    iintro Hbv
    iapply Hwand
    iunfold bkView
    iexists (sData P (st0.del bi k).S)
    iframe Hbv
    ipureintro
    show keyView (sData P (st0.S.insert bi.name ((bktOf st0.S bi.name).delete k))) _
    rw [sData_del_HB hb]
    exact sData_puts hP hwf hs Hvd

/-- **The lessor's delete from `Lease` under the batch lock** (leases T3, 2026-10-25), as mvcc's
contract states it (`batchTxSpecG`'s last clause), with the client half of the tracked buckets
and the parameters letting the lessor delete from `Lease` (`leaseParams`) as the right `Rb`: the
backend's `UnsafeDelete` of a non-safe-range, tracked bucket, its key not a hook's own; the lock
token then `bkLockedD`. -/
theorem bt_leaseDel (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ (l : Puts) (bk : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac)
          (r : GMap GoString BktData),
        {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ bk ∗ bkLocked γ P b l ∗
            key ↦*{dq} k ∗ iprop(rbOwn γ r ∗ ⌜leaseParams P⌝) }}
          (App (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"UnsafeDelete" #t))
            (Val #bk)) (Val #key))
        {{ RET #(); (∃ U : IProp GF, U ∗ unlockAt ⟨go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty, #t⟩ (bkView γ) W Pk U l) ∗
            key ↦*{dq} k ∗ iprop(rbOwn γ (rbDel r leaseName k) ∗ ⌜leaseParams P⌝) }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩ !> %l %bk %key %k %dq %r %Φ !> ⟨#HL, Hl, Hkey, Hrb, %HLp⟩ HΦ
  obtain ⟨hhas, hrb, hhk⟩ := HLp
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold bkLocked at Hl
  icases Hl with ⟨%st, Hl⟩
  iunfold bkLockedAt at Hl
  icases Hl with ⟨Hl, Hwb, %Hs⟩
  icases batchLocked_wf γ P b st $$ Hl with ⟨Hl, %Hwf⟩
  icases batchLocked_rb γ P b st r $$ [$Hl $Hrb] with ⟨Hl, Hrb, %Hr⟩
  subst Hr
  ihave #Hbk := lease_isBucket hID hName hSafe bk $$ [$Hsch $HL]
  obtain ⟨hroom, -⟩ := sessPuts_del_room HPw Hs Hwf
  have hSB : P.SB leaseBI.name = false := by rw [hP.2.2.2.1]; decide
  have hHB : P.HB leaseBI.name = true := by rw [hP.2.2.1]; decide
  have hrp : rbPut (GF := GF) γ P leaseBI.name st.S = rbOwn γ (rbData P st.S) := by
    unfold rbPut; rw [show leaseBI.name = leaseName from rfl, hrb]; rfl
  have hrp' : rbPut (GF := GF) γ P leaseName
      (st.S.insert leaseName ((bktOf st.S leaseName).delete k)) =
      rbOwn γ (rbDel (rbData P st.S) leaseName k) := by
    unfold rbPut; rw [hrb]
    simp only [↓reduceIte]
    rw [rbData_del hrb]
  rw [← hrp]
  wp_apply (hDel γ P W Pk b t st bk leaseBI key k dq hhas hroom hSB (hhk k))
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hrb] as ⟨Hl, Hkey, Hrb⟩
  ihave Hrb : rbOwn γ (rbDel (rbData P st.S) leaseName k) $$ [Hrb]
  · rw [← hrp']; iexact Hrb
  iapply HΦ
  isplitl [Hl Hwb]
  · iexists (bkLockedD γ P b l)
    isplitl [Hl Hwb]
    · iunfold bkLockedD
      iexists st, leaseBI, k
      iframe
      ipureintro; exact ⟨Hs, Hwf, hHB⟩
    iapply bt_unlockD hUL hP γ W Pk b t l $$ [$Hpkg $Hb $Ht]
  iframe Hkey Hrb
  ipureintro; exact ⟨hhas, hrb, hhk⟩

end batch

/-! ## The batch transaction, continued: its reads and `NewStore`'s calls -/

section batch2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The batch transaction's `UnsafeRange(schema.Key, k, nil, 0)` under the lock: the bucket
with the session's puts, its slices readable under the lock at the session's state. -/
theorem bt_range (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc)
    (Del : GoString → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ (l : Puts) (q : Qp) (m : Bucket) (bk : GoInterface) (key : GoSlice) (k : GoString)
          (dq : DFrac),
        {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ bk ∗ bkLocked γ P b l ∗
            bkView γ q m ∗ key ↦*{dq} k }}
          (App (App (App (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"UnsafeRange" #t))
            (Val #bk)) (Val #key)) (Val #(slice.nil))) (Val #(W64 0)))
        {{ (ks vs : GoSlice), RET (PairV #ks #vs); ∃ (Rd : GoSlice → GoString → IProp GF)
            (T : IProp GF), T ∗ (T -∗ bkLocked γ P b l) ∗ rdCap Rd T ∗ bkView γ q m ∗
            key ↦*{dq} k ∗ (keyVals Rd ks vs (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) k ∨
              (Del k ∗ ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice))) }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩ !> %l %q %m %bk %key %k %dq %Φ !> ⟨#HK, Hl, Hv, Hkey⟩ HΦ
  iunfold bkLocked at Hl
  icases Hl with ⟨%st, Hl⟩
  iunfold bkLockedAt at Hl
  icases Hl with ⟨Hl, Hwb, %Hs⟩
  icases batchLocked_wf γ P b st $$ Hl with ⟨Hl, %Hwf⟩
  iunfold bkView at Hv
  icases Hv with ⟨%vd, Hv, %Hvd⟩
  icases batchLocked_view γ P b st q vd $$ [$Hl $Hv] with ⟨Hl, Hv, %Hag⟩
  subst Hag
  ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b t st bk keyBI key slice.nil k [] dq DFrac.discard (W64 0) (by simp))
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hnil] as %ks %vs ⟨Hl, Hkey, -, Hout, #Hcap⟩
  have hS := sData_puts hP Hwf Hs Hvd
  irevert Hout
  rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts]
  erw [bktOf_of_sData hP hS]
  iintro Hout
  imod kvsOutRd_keyVals st.tx ks vs _ k $$ Hout with #Hkv
  imodintro
  iapply HΦ
  iexists (rdB st.tx), (bkLockedAt γ P b st l)
  iframe Hkey
  isplitl [Hl Hwb]
  · iunfold bkLockedAt
    iframe
    ipureintro; exact Hs
  isplitr
  · iintro HT
    iunfold bkLocked
    iexists st
    iexact HT
  isplitr
  · iunfold rdCap
    iintro !> %s %v #HRd HT
    iunfold bkLockedAt at HT
    icases HT with ⟨Hl, Hwb, %Hs'⟩
    ihave Hc := Hcap $$ %s %v %st HRd Hl
    ihave Hc2 := Hc $$ []
    · ipureintro; rfl
    icases Hc2 with ⟨%dq', Hsl, Hcl⟩
    iexists dq'
    iframe Hsl
    iintro Hsl
    ihave Hl := Hcl $$ Hsl
    iunfold bkLockedAt
    iframe
    ipureintro; exact Hs'
  isplitl [Hv]
  · iunfold bkView
    iexists (vData P (st.C, st.R))
    iframe Hv
    ipureintro; exact Hvd
  ileft; iexact Hkv

/-- The batch transaction's `LockOutsideApply()` (`NewStore`'s): the lock, its resource `W`
dropped (`NewStore`'s first `Unlock` deposits its own). -/
theorem bt_lockOut (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ ({{ bkRTx γ P b ∗ wbTok γ }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"LockOutsideApply" #t))
            (Val #()))
        {{ RET #(); bkLockedO γ P b 0 ∗ W ∗ Pk ∗ bkRTx γ P b }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %Φ !> ⟨Hrt, Hwb⟩ HΦ
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  wp_apply (hLO γ P W Pk b t rdOpen) $$ [$Hb $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  iapply HΦ
  iframe HW HPk
  isplitl [Hl Hwb]
  · iunfold bkLockedO
    iexists st
    iframe
    ipureintro
    exact ⟨Hfree.2.2.1, by simpa using Hfree.2.1, viewSame_of_freeOk Hfree, by omega,
      Hfree.2.2.2.2⟩
  iunfold bkRTx
  iframe Hrd
  iexact Ho

/-- The batch transaction's `LockOutsideApply()` after `NewStore` (the compaction job's): the
lock, a session holding no puts, with the lock's resource `W` (the backend's lock holds the
late-bound `W` from its creation: the deposit witness is `True`). -/
theorem bt_lockOutJ (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ ({{ iprop(True) ∗ bkRTx γ P b ∗ wbTok γ }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"LockOutsideApply" #t))
            (Val #()))
        {{ RET #(); bkLocked γ P b [] ∗ W ∗ Pk ∗ bkRTx γ P b }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %Φ !> ⟨-, Hrt, Hwb⟩ HΦ
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  wp_apply (hLO γ P W Pk b t rdOpen) $$ [$Hb $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  iapply HΦ
  iframe HW HPk
  isplitl [Hl Hwb]
  · iunfold bkLocked
    iexists st
    iunfold bkLockedAt
    iframe
    ipureintro; exact sessPuts_free hP Hfree
  iunfold bkRTx
  iframe Hrd
  iexact Ho

/-- The backend's `Size()`: some number. -/
theorem bk_size (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ⊢
      □ ({{ True }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"Size" #b)) (Val #()))
        {{ (n : w64), RET #n; True }}) := by
  iintro ⟨#Hpkg, #Hb⟩ !> %Φ !> - HΦ
  wp_apply (hSz γ P W Pk b) $$ [$Hb] as %n -
  iapply HΦ; itrivial

/-- The backend's `SizeInUse()`: some number. -/
theorem bk_sizeInUse (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ⊢
      □ ({{ True }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"SizeInUse" #b)) (Val #()))
        {{ (n : w64), RET #n; True }}) := by
  iintro ⟨#Hpkg, #Hb⟩ !> %Φ !> - HΦ
  wp_apply (hSzU γ P W Pk b) $$ [$Hb] as %n -
  iapply HΦ; itrivial

/-- The batch transaction's `UnsafeCreateBucket(b)` of schema's `Key` or `Meta` bucket in
`NewStore`'s session. -/
theorem bt_create (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ (n : Nat) (bk : GoInterface),
        {{ bkLockedO γ P b n ∗ ⌜n < 2⌝ ∗
            (globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ bk ∨
              globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ bk) }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"UnsafeCreateBucket" #t))
            (Val #bk))
        {{ RET #(); bkLockedO γ P b (n + 1) }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩ !> %n %bk %Φ !> ⟨Hl, %Hn, #HKM⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold bkLockedO at Hl
  icases Hl with ⟨%st, Hl, Hwb, %Hs⟩
  obtain ⟨hd, hp, hvs, -, hhw⟩ := Hs
  have hlim := HPw.2.2.1
  have hpend : sint.Z st.pend + 1 < 2 ^ 58 := by omega
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hpost : ∀ bi : BucketInfo, (st.create bi).ndel = W64 0 ∧
      sint.Z (st.create bi).pend < sint.Z P.limit + ((n + 1 : Nat) : Int) ∧
      viewSame P (st.create bi) ∧ n + 1 ≤ 2 ∧ (st.create bi).cnt.hw = false := by
    intro bi
    refine ⟨hd, ?_, viewSame_create bi hvs, by omega, hhw⟩
    show sint.Z (st.pend + W64 1) < _
    push_cast; omega
  icases HKM with (#HK | #HM)
  · ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
    ihave Hrb := rbPut_other (GF := GF) γ P keyBI.name st.S hP.2.2.2.2.1
    wp_apply (hCB γ P W Pk b t st bk keyBI hP.1 (by decide) (by decide) hpend)
      $$ [$Hb $Ht $Hl $Hbk $Hrb] as ⟨Hl, -⟩
    iapply HΦ
    iunfold bkLockedO
    iexists (st.create keyBI)
    iframe
    ipureintro; exact hpost keyBI
  · ihave #Hbk := meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
    ihave Hrb := rbPut_other (GF := GF) γ P metaBI.name st.S hP.2.2.2.2.2
    wp_apply (hCB γ P W Pk b t st bk metaBI hP.2.1 (by decide) (by decide) hpend)
      $$ [$Hb $Ht $Hl $Hbk $Hrb] as ⟨Hl, -⟩
    iapply HΦ
    iunfold bkLockedO
    iexists (st.create metaBI)
    iframe
    ipureintro; exact hpost metaBI

/-- The batch transaction's `Unlock()` in `NewStore`'s session: nothing the readers see
changed; the lock's resources deposited. -/
theorem bt_unlockO (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      □ (∀ n : Nat,
        {{ bkLockedO γ P b n ∗ W ∗ Pk }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"Unlock" #t)) (Val #()))
        {{ RET #(); □ (True : IProp GF) }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %n %Φ !> ⟨Hl, HW, HPk⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  iunfold bkLockedO at Hl
  icases Hl with ⟨%st, Hl, Hwb, %Hs⟩
  have hroom : sint.Z st.pend + P.hookMax < 2 ^ 58 := by
    have h1 := HPw.2.2.1
    have h2 := HPw.2.2.2.1
    have h3 := Hs.2.1
    have h4 := Hs.2.2.2.1
    omega
  iapply (hUL γ P W Pk b t st iprop(□ (True : IProp GF)) Hs.2.2.2.2 hroom) $$ %Φ [Hl Hwb HW HPk] HΦ
  iframe Hpkg Hb Ht Hl Hwb
  ileft
  iframe HW HPk
  ipureintro; exact ⟨Hs.2.2.1, trivial⟩

/-- The backend's `ForceCommit()`, as mvcc's contract states it. -/
theorem bk_forceCommit (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ⊢
      □ (∀ (X Y : IProp GF), {{ bkRTx γ P b ∗ wbTok γ ∗ X ∗ bkReq γ P b X Y }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ForceCommit" #b)) (Val #()))
        {{ RET #(); bkRTx γ P b ∗ Y }}) := by
  iintro ⟨#Hpkg, #Hb⟩ !> %X %Y %Φ !> ⟨Hrt, Hwb, HX, #Hrq⟩ HΦ
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  iunfold bkReq at Hrq
  icases Hrq with (#Hw | ⟨%W', %Pk', #Hb', #Hcr⟩)
  · -- a plain wand
    ihave #Hcr : commitReq γ P Pk b X Y $$ []
    · unfold commitReq
      ileft
      iintro !> HX'
      iapply Hw $$ HX'
    wp_apply (hFC γ P W Pk b rdOpen X Y) $$ [$Hb $Ho $Hwb $HX] as ⟨Ho, HY⟩
    · iframe #
    iapply HΦ
    iunfold bkRTx
    iframe Hrd HY
    iexact Ho
  · -- a request the backend's hooks serve
    wp_apply (hFC γ P W' Pk' b rdOpen X Y) $$ [$Hb' $Ho $Hwb $HX] as ⟨Ho, HY⟩
    · iframe #
    iapply HΦ
    iunfold bkRTx
    iframe Hrd HY
    iexact Ho

end batch2

/-! ## The bridge -/

section main
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The bridge** (units 4 and 5; the compaction's clauses, the merge with mvcc's unit 5a): the
backend `b` (`isBackend`), with mvcc's parameters (`bridgeParams`: schema's buckets, the hook's
buckets all but `Key`, `Key` the safe-range bucket) is a backend of mvcc's contract
(`isKeyBackendG`) over the `Key` bucket: the view `bkView γ`, the reader's token `bkRTx γ P b`
(a reader's slot and a share of the backend open), the session's token `wbTok γ` (a
write-back's budget), the puts' condition `keyPutOk` (the key above the bucket's and the
session's keys), any deletable keys `Del` (its snapshots are exact), the lock's resource `W`
(its initial resource too), the deposit witness `True`, a compaction condition `Cmp` that does
not hold (the backend does not support mvcc's compaction: the module docstring), and the hooks'
resource `Pk` as mvcc's lock resource and invariant, and the hook: `LockInsideApply` runs the hook
its caller knows is set for good (`bkHookIs γ f`: `plHookRO γ f`, not nil; unit N4, D14b: the
etcd server sets it once, after creating the store and the lessor, so the contract takes the
fact at the call rather than at the backend's creation). The range read of the
`Key` bucket (the watchable store's, through `ReadTx`) rests on the premise `keySized` (fewer
than `2^62` entries); a `ConcurrentReadTx` promises no range. -/
theorem isKeyBackendG_of_backend
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc)
    (Del : GoString → IProp GF) (Cmp : Prop) (hC : ¬ Cmp) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ keySized γ P b ⊢
      isKeyBackendG
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b)
        (bkView γ) (bkRTx γ P b) (wbTok γ) keyPutOk Del W W iprop(True) Cmp Pk (bkHookIs γ)
        (bkReq γ P b) (fun r => iprop(rbOwn γ r ∗ ⌜leaseParams P⌝))
        (bkBt b) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩
  iunfold isKeyBackendG
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #b⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply bridge_crt hCRT hcRL hcRU hcUR hID hName hSafe hP γ W Pk b Del
      $$ [$Hpkg $Hsch $Hb]
  isplitr
  · iapply bridge_rt hRT hrRL hrRU hrUR hID hName hSafe hP γ W Pk b Del
      $$ [$Hpkg $Hsch $Hb $Hsafe]
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply (hBT γ P W Pk b) $$ [$Hb] as %t #Ht
    iapply HΦ
    iunfold isBatchTxG
    iexists (bkLocked γ P b), (bkLockedO γ P b)
    isplitl []
    · iunfold batchTxSpecG
      isplitr
      · iapply bt_lockIn hLI hP γ W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iapply bt_seqPut hSP hID hName hSafe hP γ W Pk b t $$ [$Hpkg $Hsch $Hb $Ht]
      isplitr
      · iapply bt_unlock0 hUL hP γ W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iapply bt_unlock hUL hP γ W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iapply bt_range hbUR hID hName hSafe hP γ W Pk b t Del $$ [$Hpkg $Hsch $Hb $Ht]
      isplitr
      · iapply bt_lockOutJ hLO hP γ W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iintro !> %hc; exact (hC hc).elim
      isplitr
      · iintro !> %hc; exact (hC hc).elim
      isplitr
      · iintro !> %hc; exact (hC hc).elim
      iapply bt_leaseDel hDel hUL hID hName hSafe hP γ W Pk b t $$ [$Hpkg $Hsch $Hb $Ht]
    isplitr
    · iunfold batchTxInitSpec
      isplitr
      · iapply bt_lockOut hLO γ P W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iapply bt_create hCB hID hName hSafe hP γ W Pk b t $$ [$Hpkg $Hsch $Hb $Ht]
      iapply bt_unlockO hUL γ P W Pk b t $$ [$Hpkg $Hb $Ht]
    -- the read-only `batchTx` field, which `BatchTx()` returns
    iunfold bkBt
    iintro !>
    iexists t
    iframe Ht
    isplitr
    · ipureintro; rfl
    iintro !> %Φ' !> - HΦ'
    wp_apply (hBT γ P W Pk b) $$ [$Hb] as %t' #Ht'
    iapply HΦ' $$ Ht'
  isplitr
  · iapply bk_forceCommit hFC γ P W Pk b $$ [$Hpkg $Hb]
  isplitr
  · iapply bk_size hSz γ P W Pk b $$ [$Hpkg $Hb]
  isplitr
  · iapply bk_sizeInUse hSzU γ P W Pk b $$ [$Hpkg $Hb]
  iintro !> %hc; exact (hC hc).elim

/-- **The store's backend contract with the witness `True`, of the real backend** (D22 receiver
epochs, S6; `storeBackendT`: what `store.Restore` takes of its new backend). As
`storeBackend_of_backend`, which it gives (`storeBackend_of_T`): a backend made for the real
instance `d` (its ghost names `d.γB`, parameters `d.P` with schema's buckets, location `d.be`,
and the late-bound lock resource `lateW d.gx`) gives, for every store `(s, γ)` of that
instance, the contract `NewStore` takes (`mvcc.NewStore.spec`'s premise, `storeBackend`: the
deposit witness `True`; the instance does not support the compaction, `storeCmp`). -/
theorem storeBackendT_of_backend
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ⊢
      ∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d⌝ →
        storeBackendT
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) s γ Pk := by
  iintro #H %s %γ %hγ
  obtain ⟨-, hk⟩ := hγ
  have hv : bucketView (GF := GF) γ = bkView d.γB := by
    funext q m; unfold bucketView kbView; rw [hk]
  have hrt : storeRT (GF := GF) γ = bkRTx d.γB d.P d.be := by
    unfold storeRT kbRT bkRTx; rw [hk]
  have hwt : storeWT (GF := GF) γ = wbTok d.γB := by
    unfold storeWT kbWT; rw [hk]
  have hpo : storePutOk γ = keyPutOk := by
    unfold storePutOk kbPutOk; rw [hk]
  have hw : storeW (GF := GF) s γ = lateW d.gx := by
    unfold storeW; rw [hk]
  have hhf : hookFn (GF := GF) γ = bkHookIs d.γB := by
    funext g; unfold hookFn kbHookIs; rw [hk]
  have hc : ¬ storeCmp γ := by
    unfold storeCmp kbCmp; rw [hk]; simp
  have hrq : storeReq (GF := GF) γ = bkReq d.γB d.P d.be := by
    unfold storeReq kbReq; rw [hk]
  have hrb : storeRb (GF := GF) γ = fun r => iprop(rbOwn d.γB r ∗ ⌜leaseParams d.P⌝) := by
    unfold storeRb kbRb; rw [hk]
  have hbt : storeBt (GF := GF) γ = bkBt d.be := by
    unfold storeBt kbBt; rw [hk]
  iunfold storeBackendT
  rw [hv, hrt, hwt, hpo, hw, hhf, hrq, hrb, hbt, hk]
  simp only [kbWi]
  iapply isKeyBackendG_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO
    hSP hUL hbUR hCB hDel hID hName hSafe hP d.γB (lateW d.gx) Pk d.be (delKey γ) _ hc $$ H


/-- **The clean-view `ReadTx` of the real backend** (the restore plan's R5a; `keyCleanRead`: what
`store.restore` takes of a backend holding data), for every store `(s, γ)` of the real instance
`d`, over the store's clean view `bucketViewC γ`. -/
theorem keyCleanRead_of_backend
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ⊢
      ∀ (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d⌝ →
        keyCleanRead
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) (bucketViewC γ) (storeRT γ) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ %γ %hγ
  obtain ⟨-, hk⟩ := hγ
  have hv : bucketViewC (GF := GF) γ = bkViewC d.γB := by
    funext q m; unfold bucketViewC kbViewC; rw [hk]
  have hrt : storeRT (GF := GF) γ = bkRTx d.γB d.P d.be := by
    unfold storeRT kbRT bkRTx; rw [hk]
  rw [hv, hrt]
  iunfold keyCleanRead
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #d.be⟩
  isplitr
  · ipureintro; rfl
  iapply bridge_rt_clean hRT hrRL hrRU hrUR hID hName hSafe hP d.γB (lateW d.gx) Pk d.be
    $$ [$Hpkg $Hsch $Hb $Hsafe]

/-- **The store's backend contract, of the real backend** (unit 5): a backend made for the real
instance `d` (its ghost names `d.γB`, parameters `d.P` with schema's buckets, location `d.be`,
and the late-bound lock resource `lateW d.gx`) gives, for every store `(s, γ)` of that
instance, the contract `NewStore` takes (`mvcc.NewStore.spec`'s premise, `storeBackend`: the
deposit witness `True`; the instance does not support the compaction, `storeCmp`). -/
theorem storeBackend_of_backend
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ⊢
      ∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d⌝ →
        storeBackend
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) s γ Pk := by
  iintro #H %s %γ %hγ
  ihave #HT := (storeBackendT_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI
    hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP Pk γb) $$ H %s %γ %hγ
  iunfold storeBackendT at HT
  iunfold storeBackend
  iexists iprop(True)
  iexact HT

end main

end mvcc
end EtcdGrove
end Perennial
