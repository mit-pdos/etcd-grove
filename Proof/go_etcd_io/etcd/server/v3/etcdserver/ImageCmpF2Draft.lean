/-
**F2: the sender's observation of the compaction records** (spec-first Draft, 2026-11-02;
`notes/image-cmp-f2-plan.md`). Lean-first (no Rocq counterpart). Nothing here is linked: the
definitions the changed statements are written in, the restated trusted text (`backend.Snapshot`'s
spec, `specF2`), mvcc's tracking (`cmpTrack`), and the statements the Prove phase proves, as `Prop`s
(`*_stmt`). The one pure law that shows the observation suffices is proved
(`keyImageM_of_tracked`).

The gap (SNAPSHOT-SORRY #7-cmp, `SnapSendBranch.srvBeSnapOk_cmpRecs`): a snapshot of the server's
backend in compaction mode must observe `keyImageM true log r D` at `r.crev = x.crev`, i.e. (1) the
`Meta` bucket's two compaction keys hold the records' bytes, and (2) the `Key` bucket is the log's
entries cut per key at a prefix of the ones compaction at `r.crev` deletes (`entsCutAt`). Today's
`backend.Snapshot.spec` gives (1) only as a lower bound of the compaction-key flag (`fkRd`: the
values at the open, while nothing was put), and of (2) only a physical view thin of the logical one
(`viewAt`: every missing entry deletable, no shape); mvcc tracks neither the records' values against
the backend nor the job's cut.

The design (two backend ghosts, exact halves, as `hkOwn`/`rbOwn` already are):

* `backend.pvHalf γ vd`: half of the **physical view** of the non-hook buckets (`vData` of the
  writer's contents: for the server's backend, the `Key` bucket alone, `KBReal.P`'s one non-hook
  bucket); the batch lock holds the other half. Every write to a non-hook bucket (`UnsafePut`,
  `UnsafeSeqPut`, `UnsafeDelete`, `UnsafeDeleteBucket`; the locker holds the client's half in `W`)
  updates both; a commit leaves them at the committed data's `sData` (review round 1, F2-A2).
* `backend.ckHalf γ v`: half of the **compaction keys' values** (`fkVals` of the writer's contents);
  the batch lock holds the other half. A put of a compaction key (`metaPutCap`'s `UnsafePut`)
  updates both.
* `backend.Snapshot.specF2`: today's spec with the observation given the batch lock's two new halves
  as well (at the committed data of the last commit before the read transaction), and `Q` a fourth
  argument, the compaction keys' values: the post `Q (sData P D) (hkData P D) (rbData P D) (fkVals D)`.
  Why it is true of Go: unchanged from today's axiom's docstring, with the two ghosts beside
  `hkOwn`/`rbOwn` (the batch lock's halves are of the writer's contents, which a commit makes the
  committed data; `Snapshot` commits first, so the read transaction sees the last commit, made with
  the lock free). Go tests: `TestImageCmpMidJob`, `TestSnapshotPendingWrites`, `TestSnapshotWaitsForSession` (the
  axiom check).
* mvcc (`cmpTrack`, in `compactRes`, so in the batch lock's resource `W`, `writerRes`): the client's
  halves, a half of the scheduled record (`schedHalf`, a physical name: the apply thread's compaction
  right holds the other, so `r.crev = x.crev`), and the pure fact that the physical `Key`
  bucket is cut at the records' revision (`entsCutAt`), with the records of the log (`recsOk`,
  `recsPos`). The job keeps the cut a prefix per key by deleting in revision order from the
  bottom: its own cursor (`jobCursor`), whose authority `cmpTrack` holds, says every entry below it
  deletable at the job's revision is gone.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The backend's two exact ghosts

Now real (F2's stage 1): `backend.BNames`' fields `pv` and `ck`, `backend.pvHalf` and
`backend.ckHalf` (`InvBackend.lean`), the batch lock holding the other halves at the writer's
contents. -/

/-! ## The restated trust boundary -/

variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions] in
/-- **`b.Snapshot()`, observing the physical view and the compaction keys** (Draft of the restated
`backend.backend.Snapshot.spec`; the trusted text for the user). Today's spec but for the
observation: besides `R`, `W`, `Pk`, the quarter `viewAt`, `hkOwn` and `rbOwn`, it is handed the
batch lock's halves of the physical view (`pvHalf`, at the observed `vd` itself) and of the
compaction keys' values (`ckHalf` at `v`), and `Q` takes `v`: the post's `Q` is at
`fkVals D`, the values bbolt's committed data holds at `Meta`'s compaction keys. -/
abbrev backend.backend.Snapshot.specF2 : Prop :=
  ∀ (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp) (R : IProp GF)
    (Q : backend.VData → GMap (GoString × GoString) GoString → GMap GoString backend.BktData →
      backend.FkVals → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W Pk b ∗ backend.bOpen γ qo ∗ backend.wbTok γ ∗ R ∗
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData) (v : backend.FkVals),
        R -∗ W -∗ Pk -∗ backend.viewAt γ vd -∗ backend.pvHalf γ vd -∗ backend.hkOwn γ d -∗
          backend.rbOwn γ r -∗ backend.ckHalf γ v -∗ ⌜Q vd d r v⌝) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : backend.Data), RET #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp);
      backend.snapOpen sp D ∗ backend.bOpen γ qo ∗ R ∗ backend.fkRd γ P (D, ⟨∅, W64 0⟩) ∗
      ⌜Q (backend.sData P D) (backend.hkData P D) (backend.rbData P D) (backend.fkVals D)⌝ }}

variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions] in
/-- Today's spec is an instance (`Q` ignoring the new argument, the observation ignoring the new
halves): the restatement only strengthens the axiom. -/
theorem backend.backend.Snapshot.spec_of_specF2
    (h : backend.backend.Snapshot.specF2 (GF := GF) (hG := hG)) :
    backend.backend.Snapshot.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b qo R Q
  iintro %Φ ⟨#Hpkg, #Hb, Ho, Hwb, HR, #HQ⟩ HΦ
  wp_apply h γ P W Pk b qo R (fun vd d r _ => Q vd d r) $$ [Ho Hwb HR]
    as %sp %D ⟨Hsn, Ho, HR, #Hfk, %HQD⟩
  · iframe #; iframe
    iintro !> %vd %d %r %v HR' HW HPk Hv - Hh Hr -
    iapply HQ $$ HR' HW HPk Hv Hh Hr
  iapply HΦ
  iframe Hsn Ho HR Hfk
  ipureintro; exact HQD

/-! ## mvcc's tracking (Draft: a conjunct of `compactRes` at the switch) -/

variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The `Key` bucket of a physical view** as the store's bucket. -/
def mvcc.keyOfView (vd : backend.VData) : mvcc.Bucket → Prop :=
  fun m => ∀ k, vd.lookup (mvcc.keyName, k) = m.lookup k

/-- **The physical image is cut at the records** (pure): the physical view's `Key` bucket is the
log's entries `ents` cut per key at a prefix of the deletable ones at the records' revision, the
records of the log and past revision `0`. -/
def mvcc.physCut (L : mvcc.Log) (r : mvcc.CmpRecs) (vd : backend.VData) : Prop :=
  ∃ ents : List mvcc.KvEnt, mvcc.keyOfView vd (mvcc.bucketOfEnts ents) ∧
    mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents

/-- **The running job's cursor** (Draft placeholder for a `PhysNames` field and its ghost: jobs die
at a restore, review F2-C6): the job at revision `c` has deleted every entry below the revision
`(pm, ps)` (a whole revision, main and sub: Go's `last` is `(rev.Main, rev.Sub+1)`, so a batch may
end between two sub-revisions of one main; review F2-C1) that compaction at `c` deletes. The
authority is `cmpTrack`'s; the job's fragment is handed from job to job in `compactTok` (not
`compactJobPre`, which is persistent; review F2-C3). -/
opaque mvcc.StoreNames.jcG (γ : mvcc.StoreNames) : GName

/-- The job's cursor (the job's half: the job's revision `c` and the revision `p` below which it
has deleted). -/
def mvcc.jobCursor (γ : mvcc.StoreNames) (c : Int) (p : mvcc.Rev) : IProp GF :=
  ghostVar γ.jcG (1 : Qp).half (c, p.main, p.sub)

/-- **Every entry below the cursor deletable at the job's revision is gone** (pure). -/
def mvcc.cursorDone (L : mvcc.Log) (c : Int) (p : mvcc.Rev) (vd : backend.VData) : Prop :=
  ∀ e ∈ mvcc.logEnts L 0 L.length, mvcc.KeyDel L c (mvcc.revBytes e.rev e.tomb) →
    mvcc.Rev.lt e.rev p → vd.lookup (mvcc.keyName, mvcc.revBytes e.rev e.tomb) = none

/-- Draft placeholder for a `PhysNames` field (renewed by `store.Restore`, review F2-C2): the
scheduled record's ghost, the tie between the records and the apply thread's revision. -/
opaque mvcc.StoreNames.schG (γ : mvcc.StoreNames) : GName

/-- **A half of the scheduled record** (exclusive): `cmpTrack` (the batch lock's resource) holds
one, the store's restorable compaction right (`compactRightR`, so the apply thread's `cmpOwn`) the
other; only `updateCompactRev` (holding the right, then the batch lock) and `restore` move it. The
job writes `finishedCompactRev` only, so the right's half is not disturbed by it. -/
def mvcc.schedHalf (γ : mvcc.StoreNames) (sched : Option w64) : IProp GF :=
  ghostVar γ.schG (1 : Qp).half sched

/-- **mvcc's tracking of the compaction records and the job's cut** (in `compactRes` at the
switch, so in the batch lock's resource `W`, for the real backend in compaction mode; `L` is
`writerRes`'s log): the client's halves of the physical view (`pvHalf`; in either mode at the
switch, every writer of a non-hook bucket moves it) and of the compaction keys' values (the
records' bytes), the scheduled record's half (`schedHalf`; until review round 1 a quarter of
`crevUB`, a logical share a restore would strand in the old backend, F2-C2), the cursor's authority
with what it has done, and the physical cut, with the finished record not past the scheduled one
(F2-C3: so the job's write of `finishedCompactRev` keeps `r.crev`). -/
def mvcc.cmpTrack (γ : mvcc.StoreNames) (d : mvcc.KBReal) (L : mvcc.Log) (r : mvcc.CmpRecs) :
    IProp GF :=
  iprop(∃ (vd : backend.VData) (c : Int) (p : mvcc.Rev),
    backend.pvHalf d.γB vd ∗ backend.ckHalf d.γB (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∗
    mvcc.schedHalf γ r.sched ∗ ghostVar γ.jcG (1 : Qp).half (c, p.main, p.sub) ∗
    ⌜mvcc.physCut L r vd ∧ r.finRev ≤ r.schedRev ∧ c ≤ r.crev ∧ mvcc.cursorDone L c p vd⌝)

/-! ## The image from the tracked facts (proved) -/

/-- **The observation suffices** (pure): a committed `D` whose `Key` bucket is a cut physical view
and whose compaction keys hold the records' bytes is the image `keyImageM true`. -/
theorem mvcc.keyImageM_of_tracked (d : mvcc.KBReal) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (D : backend.Data) (hcut : mvcc.physCut L r (backend.sData d.P D))
    (hv : backend.fkVals D = (mvcc.recBytes r.fin, mvcc.recBytes r.sched)) :
    mvcc.keyImageM true L r D := by
  obtain ⟨ents, hk, hok, hpos, hc⟩ := hcut
  unfold mvcc.keyImageM
  simp only [↓reduceIte]
  refine ⟨ents, fun k => ?_, ?_, ?_, hok, hpos, hc⟩
  · rw [← hk k, backend.sData_lookup]; simp [mvcc.KBReal.P]
  · have := congrArg Prod.fst hv
    simp only [backend.fkVals] at this
    exact this
  · have := congrArg Prod.snd hv
    simp only [backend.fkVals] at this
    exact this

/-! ## The Prove phase's statements -/

/-- **The writer's observation** (the Prove phase's lemma, replacing `srvBeSnapOk_cmpRecs`): in
`srvBeSnapOk_window`'s observation, the KV's sole writer at `log` and the apply thread's
compaction resources at `crev` (the frame), the batch lock's resource (its `cmpTrack`) and the
batch lock's two halves give the physical cut at records `r` of revision `crev` with the
compaction keys' values the records'. Review round 1 (F2-D1, D2): as stated it needs (a) the
backend's `lateW` to carry `cmpTrack` in either state (unregistered too: after a restore no writer
may have taken the batch lock yet, `writerReg`), and (b) the writer's log `L` of `cmpTrack` to be
`kvWriter`'s `log` (a share of `γ.wv` in the writer's pin); both are the Prove phase's changes,
open (`notes/image-cmp-f2-plan.md`, questions 5 and 6). -/
def apply.cmpObs_stmt : Prop :=
  ∀ (E : apply.AEnv GF) (d : mvcc.KBReal), E.γ.kb = some d → d.cm = true →
  ∀ (log : mvcc.Log) (crev : Int) (vd : backend.VData) (v : backend.FkVals),
    txn.kvWriter E.s E.γ log ∗ apply.cmpOwn E crev ∗ mvcc.lateW d.gx ∗
      backend.pvHalf d.γB vd ∗ backend.ckHalf d.γB v ⊢
    ⌜∃ r : mvcc.CmpRecs, mvcc.physCut log r vd ∧
      v = (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∧ r.crev = crev⌝

/-- **The window's snapshot observes the records** (the Prove phase's restatement of
`srvBeSnapOk_window`'s use in `mergedCreate_window`, over `specF2`): the observation's conjunct
`d.cm = true → ∃ r, keyImageM true log r D ∧ r.crev = crev`, from `cmpObs_stmt` and
`keyImageM_of_tracked`. Stated here as the shape of `srvBeSnapOk_window`'s new observation argument:
`QK vd v` of the physical view and the compaction keys' values. -/
def apply.windowObs (d : mvcc.KBReal) (log : mvcc.Log) (crev : Int) (vd : backend.VData)
    (v : backend.FkVals) : Prop :=
  d.cm = true → ∃ r : mvcc.CmpRecs, mvcc.physCut log r vd ∧
    v = (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∧ r.crev = crev

/-- What the window's post then gives, by `keyImageM_of_tracked`. -/
theorem apply.windowObs_image (d : mvcc.KBReal) (log : mvcc.Log) (crev : Int) (D : backend.Data)
    (h : apply.windowObs d log crev (backend.sData d.P D) (backend.fkVals D)) :
    d.cm = true → ∃ r : mvcc.CmpRecs, mvcc.keyImageM true log r D ∧ r.crev = crev := by
  intro hc
  obtain ⟨r, hcut, hv, hr⟩ := h hc
  exact ⟨r, mvcc.keyImageM_of_tracked d log r D hcut hv, hr⟩

end draft

end EtcdGrove
end Perennial
