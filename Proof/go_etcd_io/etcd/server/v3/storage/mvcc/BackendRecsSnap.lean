/-
**The records' contract of a compacting real backend** (M2's item 15, stage B;
`notes/m2-storage-plan.md`, "Step 2: restore in compaction mode", (e)): `storeBackendT_of_backendC`
at the records `r` the backend was opened over (`storeBackendTR`, what `store.Restore` takes of the
received backend in compaction mode). The contract differs from today's in one clause, `ReadTx`'s
snapshot (`keyReadSnapR`), whose locked reads of the compaction keys find the records
(`metaReadSpecR … (some r)`, `rt_metaRecs`) under the client's half of the compaction-key flag at
the open (`bkRecs`); `ConcurrentReadTx`'s snapshot has no meta clause. No new trust.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ContractLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode backend

section recs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Without the range reads (`rng = false`) the records' clause is absent: the snapshot at any
records is today's at any no-compaction resource. -/
theorem keyReadSnapR_false (View : Qp → Bucket → IProp GF) (RT NC NC' : IProp GF) (r : CmpRecs)
    (Del : GoString → IProp GF) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    keyReadSnapR View RT NC r Del false rt m L = keyReadSnap View RT NC' Del false rt m L := by
  unfold keyReadSnapR keyReadSnap keyReadLockedR keyReadLocked
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- **The contract with the records from today's and the records' `ReadTx`** (a backend's
`isKeyBackendG` at any no-compaction resource `NC'`, with its `ReadTx` at the records). -/
theorem isKeyBackendGR_of_G (bi : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT NC NC' : IProp GF) (r : CmpRecs) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF) (Req : IProp GF → IProp GF → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (SR SRh MW HN : IProp GF) :
    isKeyBackendG (GF := GF) (GoInterface.ok bi) View RT WT NC' PutOk Del W Wi Dep Cmp P HF Req
        Rb Bt SR SRh MW HN ∗
      □ (∀ (q : Qp) (m : Bucket),
        {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnapR View RT NC r Del true rt m L }}) ⊢
    isKeyBackendGR (GoInterface.ok bi) View RT WT NC r PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR
      SRh MW HN := by
  iintro ⟨#H, #HR⟩
  iunfold isKeyBackendG at H
  icases H with ⟨%bi', %hb, #HC, -, #HB, #HFC, #HS, #HSU, #HCmp⟩
  have hb' : bi' = bi := by injection hb with h; exact h.symm
  subst hb'
  iunfold isKeyBackendGR
  simp only [keyReadSnapR_false (NC' := NC')]
  iexists bi'
  isplitr
  · ipureintro; rfl
  iframe HC HR HB HFC HS HSU HCmp

/-- **The held read transaction at the records, of a snapshot** (`rt_lockedR` without the clean
buffer: the records' meta clause, `rt_metaRecs`, does not need it). -/
theorem rt_lockedRS [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (m : Bucket) (hv : keyView (vData P rv) m) (r : CmpRecs) (hpos : recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ keySized γ P b ∗ fkRd γ P rv ⊢
      keyReadLockedR (bkRTx γ P b) (bkRecs γ r) r true
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv rdOpen) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hsafe, #Hfk⟩
  ihave #Hl := rt_locked hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m hv
    $$ [$Hpkg $Hsch $Hb $Hrt $Hsafe $Hfk]
  by_cases he : r = CmpRecs.empty
  · subst he
    have hnc : bkRecs (GF := GF) γ CmpRecs.empty = bkNoCmp γ := by unfold bkRecs; simp
    rw [hnc, keyReadLockedR_empty]
    iexact Hl
  · iapply keyReadLockedR_of_locked (NC' := bkNoCmp γ)
    iframe Hl
    iintro !> Hnc
    have hnc : bkRecs (GF := GF) γ r = iprop(∃ n : Nat, fkOwn γ n ∗ fkOpen γ n (recsVals r)) := by
      unfold bkRecs; simp [he]
    rw [hnc]
    icases Hnc with ⟨%n, Ho, #Hop⟩
    icases rt_metaRecs hUR hID hName hSafe hP γ W Pk b rt rtx rv rdOpen r n
      (fun kn x _ hx => recsSign_at r hpos kn x hx) $$ [$Hpkg $Hsch $Hb $Hrt $Hfk $Ho $Hop]
      with ⟨Ho, #Hm⟩
    isplitl [Ho]
    · iexists n; iframe Ho Hop
    iintro !>
    iexact Hm

/-- **`ReadTx()` over the thin view, at the records** (`bridge_rtC` with the records' meta clause,
and its thinning's deletable keys any `Del'` the backend's give up to `◇`). -/
theorem bridge_rtCR [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc) (r : CmpRecs)
    (hpos : recsSign r) (Del' : GoString → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ keySized γ P b ∗ □ (∀ k, bkDel γ k -∗ ◇ Del' k) ⊢
      □ (∀ (q : Qp) (m : Bucket),
        {{ bkView γ q m ∗ bkRTx γ P b }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkView γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnapR (bkView γ) (bkRTx γ P b) (bkRecs γ r) r Del' true rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe, #Hd⟩ !> %q %m %Φ !> ⟨Hv, Hrt⟩ HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrtf
  iapply HΦ
  iframe Hv
  iexists (bkRTx γ P b)
  iframe Hrt
  iunfold keyReadSnapR
  iintro !> %q' %Φ' !> ⟨HL, Hv'⟩ HΦ'
  iapply wp_fupd
  iunfold bkRTx at HL
  icases HL with ⟨Hrd, Ho⟩
  wp_apply (hRL γ P W Pk b rt rdOpen) $$ [$Hb $Hrtf $Hrd $Ho] as ⟨%rtx, %rv, Hh, Ho⟩
  iunfold bkView at Hv'
  icases Hv' with ⟨%vd, Hv', %Hvd⟩
  icases rtHeld_view γ P b rtx rv q' vd $$ [$Hh $Hv'] with ⟨Hh, Hv', #Hth⟩
  icases rtHeld_fkRd γ P b rtx rv $$ Hh with ⟨Hh, #Hfk⟩
  icases keyView_thin γ P rv vd m Hvd $$ Hth with ⟨%m', %Hvm', #Hthin⟩
  ihave Hth' := snapThin_congr m m' (bkDel γ) Del' $$ [$Hthin]
  · iintro !>; iexact Hd
  imod Hth' with #Hth'
  imodintro
  iapply HΦ'
  isplitl [Hv']
  · iunfold bkView
    iexists vd
    iframe Hv'
    ipureintro; exact Hvd
  iexists m', (rdB rtx), (rtTok γ P b rtx rv rdOpen)
  isplitl [Hh Ho]
  · iunfold rtTok; iframe
  isplitr
  · iapply rt_lockedRS hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m' Hvm' r hpos
      $$ [$Hpkg $Hsch $Hb $Hrtf $Hsafe $Hfk]
  iexact Hth'

/-- At a real instance the records' resource is the backend's (`bkRecs`; `fkOpenD` of the
records' bytes is `fkOpen … (recsVals r)` by definition). -/
theorem kbRecs_some (d : KBReal) (γb : GName) (r : CmpRecs) :
    kbRecs (GF := GF) (some d) γb r = bkRecs d.γB r := by
  unfold kbRecs bkRecs
  split
  · rfl
  · rfl

/-- **The store's backend contract of a compacting real backend at the records `r`**
(`storeBackendT_of_backendC` with the records: what `store.Restore` takes of the received backend in
compaction mode, `storeBackendTR`, its `restoreFixM` being the registration `storeDlReg`). -/
theorem storeBackendTR_of_backendC [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
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
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) (γi : IdxNames)
    (r : CmpRecs) (hpos : recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ∗
        storeDlReg d.γB γi ∗ fkV d.γB true ⊢
      ∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        storeBackendTR
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) s γ Pk r := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsz, #Hreg, #Hfv⟩ %s %γ %hγ
  ihave #HT := storeBackendT_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
    hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi
    $$ [$Hpkg $Hsch $Hb $Hsz $Hreg $Hfv] %s %γ %hγ
  obtain ⟨-, hk, hi⟩ := hγ
  have hreg : storeDlReg (GF := GF) d.γB γi = storeDlReg d.γB γ.idx := by rw [hi]
  rw [hreg] at *
  icases storeDlReg_congr d.γB γ (storeCmp γ) $$ Hreg with ⟨#Hd, -⟩
  ihave #HR := bridge_rtCR hRT hrRL hrRU hrUR hID hName hSafe hP d.γB (lateW d.gx) Pk d.be r hpos
    (delKey γ) $$ [$Hpkg $Hsch $Hb $Hsz $Hd]
  have hv : bucketView (GF := GF) γ = bkView d.γB := by
    funext q m; unfold bucketView kbView; rw [hk]
  have hrt : storeRT (GF := GF) γ = bkRTx d.γB d.P d.be := by
    unfold storeRT kbRT bkRTx; rw [hk]
  have hrc : kbRecs (GF := GF) γ.kb γ.bucket r = bkRecs d.γB r := by
    rw [hk, kbRecs_some]
  iunfold storeBackendT at HT
  unfold storeBackendTR
  rw [hrc]
  rw [hv, hrt] at *
  iapply isKeyBackendGR_of_G _ (bkView d.γB) (bkRTx d.γB d.P d.be) (storeWT γ) (bkRecs d.γB r)
    (kbNoCmp γ.kb γ.bucket)
  iframe HT
  iexact HR

end recs

end mvcc
end EtcdGrove
end Perennial
