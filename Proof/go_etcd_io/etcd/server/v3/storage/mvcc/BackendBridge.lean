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
nothing here). -/
def bridgeParams (P : BParams) : Prop :=
  P.has keyBI ∧ P.has metaBI ∧
    (∀ n, P.HB n = decide (n ≠ go_etcd_io.etcd.server.v3.storage.schema.keyName)) ∧
    ∀ n, P.SB n = decide (n = go_etcd_io.etcd.server.v3.storage.schema.keyName)

/-- A real instance's parameters are the bridge's when its table has schema's buckets. -/
theorem bridgeParams_of (d : KBReal) (hk : d.BT.lookup keyBI.name = some keyBI.id)
    (hm : d.BT.lookup metaBI.name = some metaBI.id) : bridgeParams d.P :=
  ⟨hk, hm, fun _ => rfl, fun _ => rfl⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- A reader's token at the share `qo`: a reader's slot of the backend, and the share `qo` of
the backend open (given back at its `RUnlock`). -/
def bkRT (γ : BNames) (P : BParams) (b : Loc) (qo : Qp) : IProp GF :=
  iprop(rdTok γ P b ∗ bOpen γ qo)

/-- A reader's token (the contract's: some share of the backend open; `kbRT` of a real
instance). -/
def bkRTx (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(rdTok γ P b ∗ ∃ q : Qp, bOpen γ q)

theorem bkRT_x (γ : BNames) (P : BParams) (b : Loc) (qo : Qp) :
    bkRT (GF := GF) γ P b qo ⊢ bkRTx γ P b := by
  unfold bkRT bkRTx
  iintro ⟨H1, H2⟩
  iframe H1
  iexists qo
  iexact H2

/-- A session holding the puts `l` in the `Key` bucket: no delete pending, the write buffer's
`Key` bucket the puts, one more pending operation a put at most (from the free lock's). -/
def sessPuts (P : BParams) (st : BSess) (l : Puts) : Prop :=
  st.ndel = W64 0 ∧ sint.Z st.pend < sint.Z P.limit + l.length ∧ bkOf st.W.bks (W64 1) = l

/-- The batch lock held in a session holding the puts `l`, with a write-back's budget. -/
def bkLockedAt (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (l : Puts) : IProp GF :=
  iprop(batchLocked γ P b st ∗ wbTok γ ∗ ⌜sessPuts P st l⌝)

/-- The batch lock held with the puts `l`. -/
def bkLocked (γ : BNames) (P : BParams) (b : Loc) (l : Puts) : IProp GF :=
  iprop(∃ st : BSess, bkLockedAt γ P b st l)

/-- `NewStore`'s session after `n` bucket creations: no delete pending, `n` more operations
than at the free lock, nothing the readers see changed, a write-back's budget. -/
def bkLockedO (γ : BNames) (P : BParams) (b : Loc) (n : Nat) : IProp GF :=
  iprop(∃ st : BSess, batchLocked γ P b st ∗ wbTok γ ∗
    ⌜st.ndel = W64 0 ∧ sint.Z st.pend < sint.Z P.limit + n ∧ viewSame P st⌝)

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
    rw [hk, Option.bind_some, hs.2.2]
    rfl
  · simp only [hn, ↓reduceIte, hP.2.2.1]
    simp [hn]

/-- A session with no puts in the `Key` bucket changed nothing the readers see. -/
theorem viewSame_noPuts {P : BParams} (hP : bridgeParams P) {st : BSess} (hst : sessWf P st)
    (hs : sessPuts P st []) : viewSame P st := by
  have hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = [] := by
    intro n i hn hb
    rw [nonHB_key hP hn hb]
    exact hs.2.2
  exact ⟨vData_free P st hst hs.1 hW, hW⟩

/-- A free state holds no puts. -/
theorem sessPuts_free {P : BParams} (hP : bridgeParams P) {st : BSess} (h : freeOk P st) :
    sessPuts P st [] := by
  refine ⟨h.2.2.1, by simpa using h.2.1, ?_⟩
  have hk := hP.1
  unfold BParams.has keyBI at hk
  exact h.2.2.2 _ _ hk (key_not_HB hP)

/-- A put of the `Key` bucket. -/
theorem sessPuts_put {P : BParams} (hPw : P.Wf) {st : BSess} {l : Puts}
    {k v : GoString} (hs : sessPuts P st l) (hl : l.length < 2 ^ 56) :
    sessPuts P (st.put keyBI k v true) (l ++ [(k, v)]) ∧ sint.Z st.pend + 1 < 2 ^ 58 := by
  obtain ⟨hd, hp, hw⟩ := hs
  have hlim := hPw.2.2.1
  have hb : sint.Z st.pend + 1 < 2 ^ 58 := by omega
  refine ⟨⟨hd, ?_, ?_⟩, hb⟩
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

/-! ## The buckets -/

section buckets
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  icases Hsi with ⟨-, -, -, ⟨%b0, #Hk0, #Hb0⟩⟩
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

end buckets

/-! ## The slices a read returns -/

section slices
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  exact h _ _ hk (by rw [hP.2.2.2]; simp) kc vc e hc he

section readers
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    Hcur, Hhist, Hrtxf, Hwgf, %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩, %Hrtx, Hcr⟩
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
  wp_apply (hUR γ P W Pk b rt rtx rv qo bk keyBI key slice.nil k [] dq DFrac.discard (W64 0)
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    · subst h; exact adt.strLt_irrefl _ h'
    · exact adt.strLt_asymm h h'

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
        · rw [h3] at this; exact adt.strLt_asymm this h2
        · exact adt.strLt_asymm (adt.strLt_trans h3 this) h2

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
          · rw [← h3] at h2; exact adt.strLt_asymm this h2
          · exact adt.strLt_asymm (adt.strLt_trans h3 this) h2
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
        exact adt.strLt_irrefl _ this
      rw [hnone, Option.none_or, if_pos ha]
      constructor
      · intro h; left; obtain ⟨a1, a2⟩ := a; simp only at ha; subst ha; cases h; rfl
      · rintro (h | h)
        · rw [← h]
        · have := hall _ h
          simp only at this; rw [ha] at this; exact absurd this (adt.strLt_irrefl _)
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
          exact adt.strLt_irrefl _ this
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  wp_apply (hUR γ P W Pk b rt rtx rv qo bk keyBI lo hi klo khi dqlo dqhi (W64 0) Hiff
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

end snaps

/-! ## The read transactions -/

section readTxs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    (rv : RView) (qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
      keyReadLocked (bkRTx γ P b) false
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty, #crt⟩
        m (rdB rtx) (crtTok γ P b crt rtx rv qo) := by
  iintro ⟨#Hpkg, #Hsch⟩
  iunfold keyReadLocked
  simp only [Bool.false_eq_true, ↓reduceIte]
  isplitr
  · iintro !> %Φ !> Ht HΦ
    iunfold crtTok at Ht
    icases Ht with ⟨Hsnap, Hback, Ho⟩
    wp_apply (hRU γ P W Pk b crt rtx rv) $$ [$Hsnap] as Hcr
    iapply HΦ
    iapply bkRT_x γ P b qo
    iunfold bkRT
    ihave Hrd := Hback $$ Hcr
    iframe Hrd Ho
  isplitr
  · iintro !>
    iapply crt_keyRange hUR hID hName hSafe hP γ W Pk b crt rtx rv qo m hv $$ [$Hpkg $Hsch]
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
    (rv : RView) (qo : Qp) (m : Bucket) (hv : keyView (vData P rv) m) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ keySized γ P b ⊢
      keyReadLocked (bkRTx γ P b) true
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv qo) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hsafe⟩
  iunfold keyReadLocked
  simp only [↓reduceIte]
  isplitr
  · iintro !> %Φ !> Ht HΦ
    iunfold rtTok at Ht
    icases Ht with ⟨Hh, Ho⟩
    wp_apply (hRU γ P W Pk b rt rtx rv) $$ [$Hb $Hrt $Hh] as Hrd
    iapply HΦ
    iapply bkRT_x γ P b qo
    iunfold bkRT
    iframe Hrd Ho
  isplitr
  · iintro !>
    iapply rt_keyRange hUR hID hName hSafe hP γ W Pk b rt rtx rv qo m hv $$ [$Hpkg $Hsch $Hb $Hrt]
  isplitr
  · iintro !>
    iapply rt_rangeRead hUR hID hName hSafe hP γ W Pk b rt rtx rv qo m hv
      $$ [$Hpkg $Hsch $Hb $Hrt $Hsafe]
  iunfold rdCap
  iintro !> %s %v #HRd Ht
  iunfold rtTok at Ht
  icases Ht with ⟨Hh, Ho⟩
  icases rtHeld_read γ P b rtx rv qo s v $$ [$Hh $Ho $HRd] with ⟨%dq, Hs, Hcl⟩
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
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ⊢
      □ (∀ (q : Qp) (m : Bucket),
        {{ bkView γ q m ∗ bkRTx γ P b }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ConcurrentReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkView γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnap (bkView γ) (bkRTx γ P b) false rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb⟩ !> %q %m %Φ !> ⟨Hv, Hrt⟩ HΦ
  iunfold bkView at Hv
  icases Hv with ⟨%vd, Hv, %Hvd⟩
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, %qo, Ho⟩
  wp_apply (hCRT γ P W Pk b q qo vd) $$ [$Hb $Hrd $Hv $Ho]
    as %crt %rtx %rv ⟨Hsnap, %Hrv, Hback, Hv, Ho⟩
  subst Hrv
  iapply HΦ
  isplitl [Hv]
  · iunfold bkView
    iexists (vData P rv)
    iframe Hv
    ipureintro; exact Hvd
  iexists (crtTok γ P b crt rtx rv qo)
  isplitl [Hsnap Hback Ho]
  · iunfold crtTok; iframe
  iunfold keyReadSnap
  iintro !> %q' %Φ' !> ⟨HL, Hv'⟩ HΦ'
  wp_apply (hRL crt)
  iapply HΦ'
  iframe Hv'
  iexists (rdB rtx), (crtTok γ P b crt rtx rv qo)
  iframe HL
  iapply crt_locked hRU hUR hID hName hSafe hP γ W Pk b crt rtx rv qo m Hvd $$ [$Hpkg $Hsch]

/-- **`ReadTx()`** as mvcc's contract states it: the shared read transaction, whose `RLock`
finds the readers' state of the caller's view then (`rtHeld_view`). -/
theorem bridge_rt (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
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
        {{ bkView γ q m ∗ bkRTx γ P b }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkView γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnap (bkView γ) (bkRTx γ P b) true rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ !> %q %m %Φ !> ⟨Hv, Hrt⟩ HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrtf
  iapply HΦ
  iframe Hv
  iexists (bkRTx γ P b)
  iframe Hrt
  iunfold keyReadSnap
  iintro !> %q' %Φ' !> ⟨HL, Hv'⟩ HΦ'
  iunfold bkRTx at HL
  icases HL with ⟨Hrd, %qo, Ho⟩
  wp_apply (hRL γ P W Pk b rt qo) $$ [$Hb $Hrtf $Hrd $Ho] as ⟨%rtx, %rv, Hh, Ho⟩
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
  iexists (rdB rtx), (rtTok γ P b rtx rv qo)
  isplitl [Hh Ho]
  · iunfold rtTok; iframe
  iapply rt_locked hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv qo m Hvd
    $$ [$Hpkg $Hsch $Hb $Hrtf $Hsafe]

end readTxs

/-! ## The batch transaction -/

section batch
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  unfold batchLocked batchLockedAt batchGhost batchGhostAt bView
  iintro ⟨⟨%t, %db, #Ht, Hmu, Hph, ⟨Hv, Hrest⟩, %Hwf⟩, ⟨Hbv, Hc⟩⟩
  icombine Hv Hbv gives %Hag
  isplitl [Hmu Hph Hv Hrest]
  · iexists t, db
    iframe; iframe #
    ipureintro; exact Hwf
  isplitl [Hbv Hc]
  · iframe
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
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc)
    (f : GoFunc) (hf : f ≠ func.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ plHookRO γ f ⊢
      □ (∀ (Pre Q : IProp GF),
        {{ Pre ∗ bkRTx γ P b ∗ wbTok γ ∗
            □ ({{ Pk ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}) }}
          (App (Val #(methods (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"LockInsideApply" #t))
            (Val #()))
        {{ RET #(); bkLocked γ P b [] ∗ W ∗ Q ∗ bkRTx γ P b }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht, #Hhk⟩ !> %Pre %Q %Φ !> ⟨Hpre, Hrt, Hwb, #Htr⟩ HΦ
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, %qo, Ho⟩
  wp_apply (hLI γ P W Pk b t qo DFrac.discard f Pre Q) $$ [$Hb $Ht $Ho $Hhk $Hpre]
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
  iexists qo
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
    rw [show keyBI.id = W64 1 from rfl, Hs.2.2]; exact hord
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
  wp_apply (hSP γ P W Pk b t st bk keyBI key val k v hP.1 hk0 hk1 hW hpend hSB)
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
  iunfold bkLocked at Hl
  icases Hl with ⟨%st, Hl⟩
  iunfold bkLockedAt at Hl
  icases Hl with ⟨Hl, Hwb, %Hs⟩
  icases batchLocked_wf γ P b st $$ Hl with ⟨Hl, %Hwf⟩
  wp_apply (hUL γ P W Pk b t st iprop(True)) $$ [$Hb $Ht $Hl $Hwb HW HPk]
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
  iapply (hUL γ P W Pk b t st Q) $$ %Φ [Hl Hwb Hv HPk Hwand] HΦ
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

end batch

/-! ## The batch transaction, continued: its reads and `NewStore`'s calls -/

section batch2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b t : Loc) :
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
            key ↦*{dq} k ∗ keyVals Rd ks vs (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) k }}) := by
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
  iframe Hkey Hkv
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
  iunfold bkView
  iexists (vData P (st.C, st.R))
  iframe Hv
  ipureintro; exact Hvd

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
  icases Hrt with ⟨Hrd, %qo, Ho⟩
  wp_apply (hLO γ P W Pk b t qo) $$ [$Hb $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  iapply HΦ
  iframe HW HPk
  isplitl [Hl Hwb]
  · iunfold bkLockedO
    iexists st
    iframe
    ipureintro
    exact ⟨Hfree.2.2.1, by simpa using Hfree.2.1, viewSame_of_freeOk Hfree⟩
  iunfold bkRTx
  iframe Hrd
  iexists qo
  iexact Ho

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
  obtain ⟨hd, hp, hvs⟩ := Hs
  have hlim := HPw.2.2.1
  have hpend : sint.Z st.pend + 1 < 2 ^ 58 := by omega
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hpost : ∀ bi : BucketInfo, (st.create bi).ndel = W64 0 ∧
      sint.Z (st.create bi).pend < sint.Z P.limit + ((n + 1 : Nat) : Int) ∧
      viewSame P (st.create bi) := by
    intro bi
    refine ⟨hd, ?_, viewSame_create bi hvs⟩
    show sint.Z (st.pend + W64 1) < _
    push_cast; omega
  icases HKM with (#HK | #HM)
  · ihave #Hbk := key_isBucket hID hName hSafe bk $$ [$Hsch $HK]
    wp_apply (hCB γ P W Pk b t st bk keyBI hP.1 (by decide) (by decide) hpend)
      $$ [$Hb $Ht $Hl $Hbk] as Hl
    iapply HΦ
    iunfold bkLockedO
    iexists (st.create keyBI)
    iframe
    ipureintro; exact hpost keyBI
  · ihave #Hbk := meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
    wp_apply (hCB γ P W Pk b t st bk metaBI hP.2.1 (by decide) (by decide) hpend)
      $$ [$Hb $Ht $Hl $Hbk] as Hl
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
        {{ RET #(); True }}) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ !> %n %Φ !> ⟨Hl, HW, HPk⟩ HΦ
  iunfold bkLockedO at Hl
  icases Hl with ⟨%st, Hl, Hwb, %Hs⟩
  iapply (hUL γ P W Pk b t st iprop(True)) $$ %Φ [Hl Hwb HW HPk] HΦ
  iframe Hpkg Hb Ht Hl Hwb
  ileft
  iframe HW HPk
  ipureintro; exact Hs.2.2

/-- The backend's `ForceCommit()`, as mvcc's contract states it. -/
theorem bk_forceCommit (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ⊢
      □ ({{ bkRTx γ P b ∗ wbTok γ }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ForceCommit" #b)) (Val #()))
        {{ RET #(); bkRTx γ P b }}) := by
  iintro ⟨#Hpkg, #Hb⟩ !> %Φ !> ⟨Hrt, Hwb⟩ HΦ
  iunfold bkRTx at Hrt
  icases Hrt with ⟨Hrd, %qo, Ho⟩
  wp_apply (hFC γ P W Pk b qo) $$ [$Hb $Ho $Hwb] as Ho
  iapply HΦ
  iunfold bkRTx
  iframe Hrd
  iexists qo
  iexact Ho

end batch2

/-! ## The bridge -/

section main
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The bridge** (units 4 and 5): the backend `b` (`isBackend`), with mvcc's parameters
(`bridgeParams`: schema's buckets, the hook's buckets all but `Key`, `Key` the safe-range
bucket) and its post-lock hook set for good to a function `f` (`plHookRO`, not nil: etcd's
server sets it once), is a backend of mvcc's contract (`isKeyBackendG`) over the `Key` bucket:
the view `bkView γ`, the reader's token `bkRTx γ P b` (a reader's slot and a share of the
backend open), the session's token `wbTok γ` (a write-back's budget), the puts' condition
`keyPutOk` (the key above the bucket's and the session's keys), the lock's resource `W` (its
initial resource too) and the hooks' resource `Pk` as mvcc's lock resource and invariant, and
the hook `f`. The range read of the `Key` bucket (the watchable store's, through `ReadTx`) rests
on the premise `keySized` (fewer than `2^62` entries); a `ConcurrentReadTx` promises no range. -/
theorem isKeyBackendG_of_backend
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
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
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc)
    (f : GoFunc) (hf : f ≠ func.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ plHookRO γ f ∗ keySized γ P b ⊢
      isKeyBackendG
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b)
        (bkView γ) (bkRTx γ P b) (wbTok γ) keyPutOk W W Pk #f := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hhk, #Hsafe⟩
  iunfold isKeyBackendG
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #b⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply bridge_crt hCRT hcRL hcRU hcUR hID hName hSafe hP γ W Pk b
      $$ [$Hpkg $Hsch $Hb]
  isplitr
  · iapply bridge_rt hRT hrRL hrRU hrUR hID hName hSafe hP γ W Pk b
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
      · iapply bt_lockIn hLI hP γ W Pk b t f hf $$ [$Hpkg $Hb $Ht $Hhk]
      isplitr
      · iapply bt_seqPut hSP hID hName hSafe hP γ W Pk b t $$ [$Hpkg $Hsch $Hb $Ht]
      isplitr
      · iapply bt_unlock0 hUL hP γ W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iapply bt_unlock hUL hP γ W Pk b t $$ [$Hpkg $Hb $Ht]
      iapply bt_range hbUR hID hName hSafe hP γ W Pk b t $$ [$Hpkg $Hsch $Hb $Ht]
    · iunfold batchTxInitSpec
      isplitr
      · iapply bt_lockOut hLO γ P W Pk b t $$ [$Hpkg $Hb $Ht]
      isplitr
      · iapply bt_create hCB hID hName hSafe hP γ W Pk b t $$ [$Hpkg $Hsch $Hb $Ht]
      iapply bt_unlockO hUL γ P W Pk b t $$ [$Hpkg $Hb $Ht]
  iapply bk_forceCommit hFC γ P W Pk b $$ [$Hpkg $Hb]

/-- **The store's backend contract, of the real backend** (unit 5): a backend made for the real
instance `d` (its ghost names `d.γB`, parameters `d.P` with schema's buckets, location `d.be`,
and the late-bound lock resource `lateW d.gx`) gives, for every store `(s, γ)` of that
instance, the contract `NewStore` takes (`mvcc.NewStore.spec`'s premise). -/
theorem storeBackend_of_backend
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
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
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (f : GoFunc) (hf : f ≠ func.nil)
    (γb : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ plHookRO d.γB f ∗ keySized d.γB d.P d.be ⊢
      ∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d⌝ →
        isKeyBackendG
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be)
          (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (storeW s γ) (kbWi γ.kb) Pk #f := by
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
  rw [hv, hrt, hwt, hpo, hw, hk]
  simp only [kbWi]
  iapply isKeyBackendG_of_backend hCRT hRT hBT hFC hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL
    hbUR hCB hID hName hSafe hP d.γB (lateW d.gx) Pk d.be f hf $$ H

end main

end mvcc
end EtcdGrove
end Perennial
