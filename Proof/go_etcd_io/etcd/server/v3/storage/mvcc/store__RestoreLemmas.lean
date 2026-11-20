/-
`mvcc.cmpOk_restored` and `mvcc.cmpTrack_restored`, out of `store__Restore.lean`'s proof so that
`NewStoreImage.lean` imports them without the proof (import tiers, 2026-11-18).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreNC
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreOn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactLockfree

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

omit package_sem in
/-- **The restored store's cut** (track A, 2026-11-06): at the restored log `L`, the image's entries
`ents` cut at its records' compaction revision (`restoreImageM`'s), nothing deleted yet, the image's
records `r` and the job's cursor at the finished record, before every entry, the tracked
compaction's pure fact holds. -/
theorem mvcc.cmpOk_restored (L : mvcc.Log) (hb : mvcc.LogB L) (r : mvcc.CmpRecs)
    (ents : List mvcc.KvEnt) (hrec : mvcc.recsOk L r) (hpos : mvcc.recsPos r)
    (hcut : mvcc.entsCutAt L r.crev ents) :
    mvcc.snap.cmpOk L (mvcc.bucketOfEnts ents) (∅ : backend.VData) r
      (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev)) := by
  have hfb := mvcc.CmpRecs.finRev_bounds L r hrec
  refine ⟨ents, hcut, ?_, hrec, hpos, ?_, ?_, hfb.1, hfb.2, Int.le_refl _⟩
  · intro k
    simp [mvcc.snap.physLookup]
  · intro k h; simp at h
  · intro e he hlt _
    have hbd := mvcc.logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _) e he
    unfold mvcc.Rev.lt at hlt
    have h0 : sint.Z (W64 0) = 0 := by decide
    simp only [h0] at hlt
    omega

/-- **The restored store's tracked compaction** (track A, 2026-11-06; in place of `cmpTrack_new_M1`
at `store.Restore`): the image's values' halves at its records (`restoreImageM`'s on-arm, from the
open's exact `fkCl`), nothing deleted, and the new names' fresh ghost state at the records (the
compaction revision's half, the job cursor's half at the finished record and the lower bounds'
authority at the compaction revision). -/
theorem mvcc.cmpTrack_restored (γ : mvcc.StoreNames) (d' : mvcc.KBReal) (hk : γ.kb = some d')
    (hon : d'.cm = true) (L : mvcc.Log) (hb : mvcc.LogB L) (r : mvcc.CmpRecs)
    (ents : List mvcc.KvEnt) (hrec : mvcc.recsOk L r) (hpos : mvcc.recsPos r)
    (hcut : mvcc.entsCutAt L r.crev ents) :
    mvcc.kbVals (GF := GF) (some d') (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∅ ∗
      ghostVar γ.rcv (1 : Qp).half r.crev ∗
      ghostVar γ.jc (1 : Qp).half (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev)) ∗
      monoNatAuthOwn γ.rcl 1 (mvcc.crevN r.crev) ⊢
      mvcc.cmpTrack γ L (mvcc.bucketOfEnts ents) r := by
  unfold mvcc.cmpTrack
  rw [hk]
  simp only [hon, ↓reduceIte, mvcc.kbVals]
  iintro ⟨⟨Hf, Hd⟩, Hr, Hj, Hl⟩
  iframe Hf Hr Hl
  iexists ∅, (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev))
  iframe Hd Hj
  ipureintro; exact mvcc.cmpOk_restored L hb r ents hrec hpos hcut


end proof

end EtcdGrove
end Perennial
