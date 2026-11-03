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

-- (F2, stage 2, 2026-11-03) `keyOfView`, `physCut`, `cursorDone` and the tracking (`cmpFacts`,
-- `cmpTrackOn`, `cmpTrack`, with the tie ghosts `KBReal.ties` in place of this Draft's
-- placeholders `jcG`/`schG`) are real definitions now: `InvStore.lean`.

/-! ## The image from the tracked facts: `mvcc.keyImageM_of_tracked` (proved, moved to
`RestoreImageOpen.lean` with its converse `mvcc.tracked_of_keyImageM`, F2's stage 2) -/

/-! ## The Prove phase's statements -/

/-- **The writer's observation** (the Prove phase's lemma, replacing `srvBeSnapOk_cmpRecs`; restated
at F2's stage 2 over the real tracking): in `srvBeSnapOk_window`'s observation, the KV's sole writer
at `log` (its pin's quarter of the log tie), the apply thread's compaction resources at `crev` (the
compaction right's half of the revision tie), the batch lock's resource (`lateWD d`: its tracking,
`cmpTrack`) and the backend's two halves (`pvHalf`/`ckHalf`, as `Snapshot.specF2` hands them) give the physical
cut at records `r` of revision `crev` with the compaction keys' values the records'. Its mvcc half
is the law `mvcc.lateWD_cmpObsP` (proved, `InvCompact.lean`; over its footprint `lateWD_cmpObs`), at
the writer's pin (`writerPin`, in `kvWriter`, which since review round 2 carries the registration
fact `pinRegd`: no separate `storeRegd` frame) and the compaction right (`compactRightR`, in
`cmpOwn`); what stage 4 adds is opening `kvWriter` and `cmpOwn` to those two. -/
def apply.cmpObs_stmt : Prop :=
  ∀ (E : apply.AEnv GF) (d : mvcc.KBReal), E.γ.kb = some d → d.cm = true →
  ∀ (log : mvcc.Log) (crev : Int) (vd : backend.VData) (v : backend.FkVals),
    txn.kvWriter E.s E.γ log ∗ apply.cmpOwn E crev ∗ mvcc.lateWD d ∗
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
