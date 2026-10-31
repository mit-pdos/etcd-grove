/-
**`store.restore`'s text before item 18** (M2, the storage side, 2026-10-30): `store.restore`
over a backend that records no compaction (`kbNoCmp`) and the whole bucket of the restored log, as
`NewStore` and `store.Restore` (off mode) call it. The switched spec gives it
(`store.restore.specNC_of_spec`: at no record, the whole bucket, `RevP0 = RevP` and `Fin` the post),
so those callers read as before. See `Spec/.../mvcc/store__restore.lean` for the text's account.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`store.restore` at no record and the whole bucket** (the spec before item 18; what
`NewStore` and `store.Restore` use). -/
abbrev mvcc.store.restore.specNC : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (MW SR SRh : IProp GF)
    (dqb dqi : DFrac)
    (R : mvcc.Log) (RevP RevK RevQ : IProp GF) (dqc : DFrac) (q1 q2 : Qp),
  mvcc.restoreLogOk R → q1 + q2 = 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT (mvcc.kbNoCmp γ.kb γ.bucket) PutOk (mvcc.delKey γ) W Wi Dep
        Cmp P HF (Rb := Rb) (Bt := Bt) (SR := SR) (SRh := SRh) (MW := MW) ∗
      RT ∗ mvcc.kbNoCmp γ.kb γ.bucket ∗ mvcc.restoreView b γ RT q R ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length ∗
      mvcc.idxWriterLb γ.idx ([[], []] ++ R) ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗ RevP ∗
      mvcc.revLockW s q2 RevP RevK ∗
      mvcc.revUnlockW s q2 ([[], []] ++ R) RevK
        iprop(mvcc.restoreViewOut γ q R ∗ mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗
          ⌜mvcc.logCh ([[], []] ++ R) < receiptBound GF⌝) RevQ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; RT ∗ mvcc.kbMW γ.kb γ.bucket ∗
      ⧗ (mvcc.logCh ([[], []] ++ R)) ∗ RevQ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((([[], []] ++ R).length : Int) - 1) : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) }}


set_option maxHeartbeats 800000 in
/-- **At no record and the whole bucket the spec reads as before item 18.** -/
theorem mvcc.store.restore.specNC_of_spec (h : mvcc.store.restore.spec (GF := GF) (hG := hG)) :
    mvcc.store.restore.specNC (GF := GF) (hG := hG) := by
  intro s γ b le ti lg q P HF RT WT W Wi Dep Cmp PutOk Rb Bt MW SR SRh dqb dqi R RevP RevK RevQ dqc
    q1 q2 hR hq12
  iintro %Φ ⟨#Hpkg, Hb, #Hbk, Hrt, Hnc, Hview, Hkvi, Hix, Hig, #Hiw, #Hle, #Hlg, %Hlgnn, Hcur1, Hcmp,
    HRevP, HLk, HUl⟩ HΦ
  have hrec : mvcc.recsOk ([[], []] ++ R) mvcc.CmpRecs.empty := by
    unfold mvcc.recsOk mvcc.CmpRecs.empty
    refine ⟨?_, ?_⟩ <;> intro x hx <;> cases hx
  iapply (h s γ b le ti lg q P HF RT WT W Wi Dep (mvcc.kbNoCmp γ.kb γ.bucket) Cmp PutOk Rb Bt MW SR SRh
      dqb dqi R RevP RevP RevK RevQ dqc DFrac.discard q1 q2 mvcc.CmpRecs.empty
      (mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length)
      iprop(RT ∗ mvcc.kbMW γ.kb γ.bucket ∗
        ⧗ (mvcc.logCh ([[], []] ++ R)) ∗ RevQ ∗
        s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((([[], []] ++ R).length : Int) - 1) : w64) ∗
        s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗
        s.[store, go!"b"] ↦{dqb} b ∗
        s.[store, go!"kvindex"] ↦{dqi}
          (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface))
      hR hq12 hrec (fun x hx => by cases hx) (mvcc.entsCutAt_full _ _) (Or.inl rfl)) $$
    [Hb Hrt Hnc Hview Hkvi Hix Hig Hcur1 Hcmp HRevP HLk HUl]
  · rw [mvcc.isKeyBackendGR_empty, mvcc.bucketOfEnts_logEnts, mvcc.CmpRecs.crev_empty]
    ihave Hig := (mvcc.idxLockG_at _ _).1 $$ Hig
    ihave Hview := mvcc.restoreViewR_empty _ _ _ _ _ $$ Hview
    ihave Hfw : mvcc.revFinW s DFrac.discard mvcc.CmpRecs.empty.fin RevP RevP $$ []
    · simp only [mvcc.CmpRecs.empty]
      iunfold mvcc.revFinW
      iintro H; iexact H
    iunfold mvcc.restoreViewOut at HUl
    ihave Hk : mvcc.resumeK s mvcc.CmpRecs.empty
        (mvcc.restoreDone s b ti q1 dqb dqi dqc ([[], []] ++ R)
          (mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length) mvcc.CmpRecs.empty RT
          (mvcc.kbNoCmp γ.kb γ.bucket) RevQ)
        iprop(RT ∗ mvcc.kbMW γ.kb γ.bucket ∗
          ⧗ (mvcc.logCh ([[], []] ++ R)) ∗ RevQ ∗
          s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((([[], []] ++ R).length : Int) - 1) : w64) ∗
          s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗
          s.[store, go!"b"] ↦{dqb} b ∗
          s.[store, go!"kvindex"] ↦{dqi}
            (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface)) $$ []
    · iunfold mvcc.resumeK
      simp only [mvcc.CmpRecs.resumes_empty, Bool.false_eq_true, ↓reduceIte]
      unfold mvcc.restoreDone
      simp only [mvcc.CmpRecs.empty, Option.getD_none, mvcc.logEnts_length]
      iintro ⟨H1, H2, H3⟩
      ihave H2 := mvcc.kbNoCmp_MW _ _ $$ H2
      iframe H1 H2 H3
    iframe Hpkg Hb Hbk Hrt Hnc Hkvi Hix Hiw Hle Hlg Hcur1 Hcmp HRevP HLk Hig Hview Hfw HUl Hk
    ipureintro; exact Hlgnn
  iintro !> H
  iapply HΦ
  iexact H

end spec

end EtcdGrove
end Perennial
