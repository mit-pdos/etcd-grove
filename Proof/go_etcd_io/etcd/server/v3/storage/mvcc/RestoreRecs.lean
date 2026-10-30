/-
**The backend vocabulary with the compaction records, and `restore()`'s protocol** (M2, the storage
side, 2026-10-30: the approval's item 27, switched with item 18, the inner `store.restore` in
compaction mode). Moved from `M2StorageDraftRestore.lean`.

- **The records threaded through the read vocabulary** (item 27): `keyReadLockedR`, `keyReadSnapR`,
  `keyReadSnapCR`, `keyCleanReadR`, `isKeyBackendGR`: today's `keyReadLocked`, ... with the meta
  clause at the records `r` (`metaReadSpecR rt (some r)`) in place of `metaReadSpec rt true`; at no
  record each *is* today's (`…_empty`). Beside today's, not in their place (the plan's "with `r` a
  parameter of default `empty`"): today's are the backend bridge's vocabulary, which the backend
  side changes on its own branch; the replacement is a rename once both land.
- **The view `restore()` reads** (`restoreViewR`): the empty bucket, or the image's bucket `m` with
  the clean read at the records `r` under the records' resource `NC` (item 27's text over `NC`, a
  parameter: the store's `kbRecs γ.kb γ.bucket r`, which stays the backend's, in the Draft).
- **`restore()`'s protocol for the records** (item 18): the finished record's lock round
  (`revFinW`), what `restore()` has once the index is published (`restoreDone`), the resume of a
  scheduled compaction as the caller provides it (`resumeK`).
- **Today's `store.restore` text** (`store.restore.specNC`, the spec before item 18), which the
  switched spec gives at no record and the whole bucket (`store.restore.specNC_of_spec`): what
  `NewStore` and today's `store.Restore` use.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCut
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## The read vocabulary with the records (item 27) -/

/-- **`keyReadLocked` with the records `r`** (its meta clause: with `NC`, the reads of the
compaction keys find the records). -/
def keyReadLockedR (RT NC : IProp GF) (r : CmpRecs) (rng : Bool) (rt : GoInterfaceOk)
    (m : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    IProp GF :=
  iprop(□ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) ∗
    □ keyRangeSpec rt m Rd Tok ∗
    (if rng then iprop(□ keyRangeReadSpec rt m Rd Tok ∗ □ keyRangeLimSpec rt m Rd Tok cl ∗
      □ rdSplit rt m Rd Tok cl ∗ □ (NC -∗ NC ∗ □ metaReadSpecR rt (some r) Rd Tok))
     else iprop(True)) ∗
    rdCap Rd Tok)

instance keyReadLockedR_persistent (RT NC : IProp GF) (r : CmpRecs) (rng : Bool)
    (rt : GoInterfaceOk) (m : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF)
    (cl : Bool) : Persistent (keyReadLockedR RT NC r rng rt m Rd Tok cl) := by
  unfold keyReadLockedR; cases rng <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

theorem keyReadLockedR_empty (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk)
    (m : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool) :
    keyReadLockedR RT NC CmpRecs.empty rng rt m Rd Tok cl =
      keyReadLocked RT NC rng rt m Rd Tok cl := by
  unfold keyReadLockedR keyReadLocked; rw [metaReadSpecR_empty]

theorem keyReadLockedR_rangeLim (RT NC : IProp GF) (r : CmpRecs) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLockedR (GF := GF) RT NC r true rt m Rd Tok cl ⊢ □ keyRangeLimSpec rt m Rd Tok cl := by
  unfold keyReadLockedR
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨-, #H, -⟩, -⟩
  iexact H

theorem keyReadLockedR_split (RT NC : IProp GF) (r : CmpRecs) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLockedR (GF := GF) RT NC r true rt m Rd Tok cl ⊢ □ rdSplit rt m Rd Tok cl := by
  unfold keyReadLockedR
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨-, -, #H, -⟩, -⟩
  iexact H

/-- With the records' resource, the reads of the compaction keys find the records. -/
theorem keyReadLockedR_meta (RT NC : IProp GF) (r : CmpRecs) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLockedR (GF := GF) RT NC r true rt m Rd Tok cl ⊢
      □ (NC -∗ NC ∗ □ metaReadSpecR rt (some r) Rd Tok) := by
  unfold keyReadLockedR
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨-, -, -, #H⟩, -⟩
  iexact H

theorem keyReadLockedR_cap (RT NC : IProp GF) (r : CmpRecs) (rng : Bool) (rt : GoInterfaceOk)
    (m : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLockedR (GF := GF) RT NC r rng rt m Rd Tok cl ⊢ rdCap Rd Tok := by
  unfold keyReadLockedR
  iintro ⟨-, -, -, #H⟩
  iexact H

theorem keyReadLockedR_unlock (RT NC : IProp GF) (r : CmpRecs) (rng : Bool) (rt : GoInterfaceOk)
    (m : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLockedR (GF := GF) RT NC r rng rt m Rd Tok cl ⊢
      □ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) := by
  unfold keyReadLockedR
  iintro ⟨#H, -, -, -⟩
  iexact H

/-- **`keyReadSnap` with the records.** -/
def keyReadSnapR (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) (r : CmpRecs)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (m' : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ keyReadLockedR RT NC r rng rt m' Rd Tok ∗ snapThin m m' Del }}))

instance keyReadSnapR_persistent (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) (r : CmpRecs)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    Persistent (keyReadSnapR View RT NC r Del rng rt m L) := by
  unfold keyReadSnapR; infer_instance

theorem keyReadSnapR_empty (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    keyReadSnapR View RT NC CmpRecs.empty Del rng rt m L = keyReadSnap View RT NC Del rng rt m L := by
  unfold keyReadSnapR keyReadSnap; simp only [keyReadLockedR_empty]

/-- **`keyReadSnapC` with the records.** -/
def keyReadSnapCR (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) (r : CmpRecs)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) : IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ keyReadLockedR RT NC r true rt m Rd Tok true }}))

instance keyReadSnapCR_persistent (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) (r : CmpRecs)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    Persistent (keyReadSnapCR View RT NC r rt m L) := by
  unfold keyReadSnapCR; infer_instance

theorem keyReadSnapCR_empty (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    keyReadSnapCR View RT NC CmpRecs.empty rt m L = keyReadSnapC View RT NC rt m L := by
  unfold keyReadSnapCR keyReadSnapC; simp only [keyReadLockedR_empty]

/-- **`keyCleanRead` with the records** (what `store.restore` takes of a backend holding data, its
`NC` the records' resource; D22's walk builds it from `keyCleanRead_of_backendC`). -/
def keyCleanReadR (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (r : CmpRecs) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnapCR View RT NC r rt m L }}))

instance keyCleanReadR_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT NC : IProp GF) (r : CmpRecs) : Persistent (keyCleanReadR b View RT NC r) := by
  unfold keyCleanReadR; infer_instance

theorem keyCleanReadR_empty (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) :
    keyCleanReadR b View RT NC CmpRecs.empty = keyCleanRead b View RT NC := by
  unfold keyCleanReadR keyCleanRead; simp only [keyReadSnapCR_empty]

/-- **`isKeyBackendG` with the records** (its two `ReadTx`s' snapshots at `r`). -/
def isKeyBackendGR (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (r : CmpRecs) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF := fun X Y => iprop(□ (X -∗ Y)))
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (Bt : GoInterfaceOk → IProp GF := fun _ => iprop(True))
    (SR SRh : IProp GF := iprop(True)) (MW : IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnapR View RT NC r Del false rt m L }}) ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnapR View RT NC r Del true rt m L }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt);
          isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW }}) ∗
    □ (∀ (X Y : IProp GF),
      {{ RT ∗ WT ∗ X ∗ Req X Y }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      {{ RET #(); RT ∗ Y }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"Size" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"SizeInUse" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ (⌜Cmp⌝ -∗
      □ ({{ SR }} (App (Val #(methods bi.ty go!"LockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); SRh }}) ∗
      □ ({{ SRh }} (App (Val #(methods bi.ty go!"UnlockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); SR }}) ∗
      □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); metaReadTx rt RT }})))

instance isKeyBackendGR_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT NC : IProp GF) (r : CmpRecs) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF) (Req : IProp GF → IProp GF → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (SR SRh MW : IProp GF) :
    Persistent (isKeyBackendGR b View RT WT NC r PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW) := by
  unfold isKeyBackendGR; infer_instance

theorem isKeyBackendGR_empty (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT NC : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF) (Req : IProp GF → IProp GF → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (SR SRh MW : IProp GF) :
    isKeyBackendGR b View RT WT NC CmpRecs.empty PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW =
      isKeyBackendG b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW := by
  unfold isKeyBackendGR isKeyBackendG; simp only [keyReadSnapR_empty]

/-- **The view `restore()` reads, over the image's bucket `m` and records `r`** (item 27's
`restoreViewR`, over the records' resource `NC`): `NewStore`'s empty bucket (no record), or the
bucket `m` over a clean read buffer with the records' clean read. -/
def restoreViewR (b : GoInterface) (γ : StoreNames) (RT : IProp GF) (q : Qp) (R : Log)
    (m : Bucket) (NC : IProp GF) (r : CmpRecs) : IProp GF :=
  if R = [] then iprop(bucketView γ q ∅ ∗ ⌜m = ∅ ∧ r = CmpRecs.empty⌝)
  else iprop(bucketViewC γ q m ∗ keyCleanReadR b (bucketViewC γ) RT NC r)

/-- At no record and the whole bucket it is today's `restoreView`. -/
theorem restoreViewR_empty (b : GoInterface) (γ : StoreNames) (RT : IProp GF) (q : Qp) (R : Log) :
    restoreView (GF := GF) b γ RT q R ⊢
      restoreViewR b γ RT q R (bucketMap ([[], []] ++ R)) (kbNoCmp γ.kb γ.bucket) CmpRecs.empty := by
  iintro Hview
  iunfold restoreView at Hview
  iunfold restoreViewOut at Hview
  iunfold restoreViewR
  by_cases hR0 : R = []
  · subst hR0
    simp only [↓reduceIte]
    icases Hview with ⟨Hv, -⟩
    iframe Hv
    ipureintro; exact ⟨rfl, trivial⟩
  · simp only [hR0, ↓reduceIte]
    rw [keyCleanReadR_empty]
    iexact Hview

/-! ## `restore()`'s protocol for the records (item 18) -/

/-- **`restore()`'s lock round for the finished record** (`kvstore.go:330-341`): none if the image
has no finished record; else `RevP0` gives, at `Lock`, the lock's part `dql` of `compactMainRev`
with `RevK0`, and `Unlock` takes it at the record with `RevK0` and gives `RevP` (the second
round's, `revLockW`). `NewStore`: private memory; `store.Restore`: the lock in restoring mode. -/
def revFinW (s : Loc) (dql : DFrac) (fin : Option w64) (RevP0 RevP : IProp GF) : IProp GF :=
  match fin with
  | none => iprop(RevP0 -∗ RevP)
  | some x => iprop(∃ RevK0 : IProp GF,
      (∀ Ψ : val → IProp GF, RevP0 -∗
        ▷ (∀ v : w64, (s.[store, go!"compactMainRev"] ↦{dql} v : IProp GF) -∗ RevK0 -∗ Ψ #()) -∗
        WP (App (Val (s.[store, go!"revMu"] @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Lock"))
          (Val #())) {{ Ψ }}) ∗
      (∀ Ψ : val → IProp GF, (s.[store, go!"compactMainRev"] ↦{dql} x : IProp GF) -∗ RevK0 -∗
        ▷ (RevP -∗ Ψ #()) -∗
        WP (App (Val (s.[store, go!"revMu"] @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Unlock"))
          (Val #())) {{ Ψ }}))

/-- **What `restore()` has once the index is published and `s.revMu` released**: the reader's token
`RT`, the records' resource `NC`, a time receipt per entry the rebuild took (`ents.length`: the log's
`logCh` for the whole bucket, `logEnts_length`), `RevQ`, `currentRev` at the restored log's last
revision, `compactMainRev` at the finished record (`-1` if none), the backend and the index. -/
def restoreDone (s : Loc) (b : GoInterface) (ti : Loc) (q1 : Qp) (dqb dqi dqc : DFrac) (L' : Log)
    (ents : List KvEnt) (r : CmpRecs) (RT NC RevQ : IProp GF) : IProp GF :=
  iprop(RT ∗ NC ∗ ⧗ ents.length ∗ RevQ ∗
    s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((L'.length : Int) - 1) : w64) ∗
    s.[store, go!"compactMainRev"] ↦{dqc} (r.fin.getD (W64 (-1))) ∗
    s.[store, go!"b"] ↦{dqb} b ∗
    s.[store, go!"kvindex"] ↦{dqi}
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface))

/-- **The resume, as `restore()`'s caller provides it**: if the records resume a compaction,
`s.compactLockfree(sched)` from `Done` ends in `Fin`, whatever it returns (`restore()` only logs the
error); else `Done` is `Fin`. `store.Restore` in compaction mode provides it from
`compactLockfree.spec` (the store's invariant re-established at the new names first, the new
backend's unset hook lent); `NewStore`'s, over a fresh bucket, never resumes. -/
def resumeK (s : Loc) (r : CmpRecs) (Done Fin : IProp GF) : IProp GF :=
  if r.resumes then
    iprop(∀ Ψ : val → IProp GF, Done -∗
      ▷ (∀ (ch : GoChan) (err : GoInterface), Fin -∗ Ψ (PairV #ch #err)) -∗
      WP (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree"))
        (Val #(r.sched.getD (W64 0)))) {{ Ψ }})
  else iprop(Done -∗ Fin)

end vocab

end mvcc
end EtcdGrove
end Perennial
