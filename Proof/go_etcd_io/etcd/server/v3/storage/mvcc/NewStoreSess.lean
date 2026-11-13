/-
**B3 (mvccfull F1): what `NewStore`'s batch session needs of the backend** (`NewStoreR.lean`).

`NewStore` (`kvstore.go:120-125`) runs a batch session before `restore()`: `BatchTx()`,
`LockOutsideApply()`, `UnsafeCreateBucket(Key)`, `UnsafeCreateMetaBucket`, `Unlock()`,
`ForceCommit()`. Its proof (`NewStore.lean` l.408-490) uses only the contract's `BatchTx` clause
(through `isBatchTxG`'s `batchTxInitSpec`) and its `ForceCommit` clause. Neither names the deletable
keys `Del` or the no-compaction resource `NC`: `batchTxInitSpec` takes `RT WT W Wi Dep LockedO P`,
and the `ForceCommit` clause takes `RT WT Req`. So the session needs **some** contract at the store's
names, at any `Del`. It does not need the store's `delKey γ`, which only the registration `storeDlReg`
gives. The real backend has one with no registration fixed: `isKeyBackendG_of_backendC` at the
backend's own deletable keys `bkDel` (`NewStoreSessReal.lean`). The registration stays unfixed
(`restoreRegM d`, `dlInit`) through the session. `restore()`'s clean read is then lent it
(`keyCleanRead_of_backendC`, as in `store.Restore`), and the fix comes once that read gives it back
(`storeSess_fix`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The session's contract** (persistent): `storeBackendT` at some deletable keys `Del` (the
session deletes nothing, and no clause it uses names `Del`). -/
def mvcc.storeSessT (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) : IProp GF :=
  iprop(∃ Del : GoString → IProp GF,
    mvcc.isKeyBackendG b (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
      (mvcc.kbNoCmpF γ.kb γ.bucket) (mvcc.storePutOk γ) Del (mvcc.storeW s γ) (mvcc.kbWi γ.kb)
      iprop(True) (mvcc.storeCmp γ) P (mvcc.hookFn γ) (mvcc.storeReq γ) (mvcc.storeRb γ)
      (mvcc.storeBt γ) (mvcc.kbSR γ.kb) (mvcc.kbSRh γ.kb) (mvcc.kbMWv γ.kb γ.bucket)
      (mvcc.kbHookNilAt γ.kb))

instance mvcc.storeSessT_persistent (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) :
    Persistent (mvcc.storeSessT (GF := GF) b s γ P) := by
  unfold mvcc.storeSessT; infer_instance

/-- The store's contract is a session contract (`Del := delKey γ`; the fresh instance). -/
theorem mvcc.storeSessT_of_storeBackendT (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames)
    (P : IProp GF) : mvcc.storeBackendT (GF := GF) b s γ P ⊢ mvcc.storeSessT b s γ P := by
  iintro #H
  iunfold mvcc.storeSessT
  iexists mvcc.delKey γ
  iunfold mvcc.storeBackendT at H
  iexact H

/-- **What the session uses** (`NewStore.lean` l.408-415): from a session contract, `BatchTx()`
returning a batch transaction with `NewStore`'s initial calls (`batchTxInitSpec`, at the deposit
witness `True`), and `ForceCommit()`. -/
theorem mvcc.storeSessT_session (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) :
    mvcc.storeSessT (GF := GF) b s γ P ⊢
      ∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
        □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
          {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt);
              ∃ LockedO : Nat → IProp GF, mvcc.batchTxInitSpec bt (mvcc.storeRT γ) (mvcc.storeWT γ)
                (mvcc.storeW s γ) (mvcc.kbWi γ.kb) iprop(True) LockedO P }}) ∗
        □ (∀ (X Y : IProp GF),
          {{ mvcc.storeRT γ ∗ mvcc.storeWT γ ∗ X ∗ mvcc.storeReq γ X Y }}
            (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
          {{ RET #(); mvcc.storeRT γ ∗ Y }}) := by
  iintro #H
  iunfold mvcc.storeSessT at H
  icases H with ⟨%Del, #H⟩
  iunfold mvcc.isKeyBackendG at H
  icases H with ⟨%bi, %Hbi, -, -, #HB, #HF, -⟩
  iexists bi
  isplitr
  · ipureintro; exact Hbi
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply HB as %bt #Hbt
    iapply HΦ
    iunfold mvcc.isBatchTxG at Hbt
    icases Hbt with ⟨%Locked, %LockedO, -, #Hinit, -⟩
    iexists LockedO
    iexact Hinit
  · iexact HF

/-- **The fix after the clean read** (in `restore()`'s resume continuation, or after `restore()`
returns: `restoreDone` gives the lent `storeRT γ ∗ restoreRegM d` back): the unfixed registration
fixed (`restoreRegM_fix`), the contract at the records. -/
theorem mvcc.storeSess_fix (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF)
    (d : mvcc.KBReal) (r : mvcc.CmpRecs) :
    mvcc.restoreRegM (GF := GF) d ∗ (mvcc.restoreFixM d γ -∗ mvcc.storeBackendTR b s γ P r) ⊢
      |==> mvcc.storeBackendTR b s γ P r := by
  iintro ⟨Hreg, Hw⟩
  imod mvcc.restoreRegM_fix d γ $$ Hreg with #Hfix
  imodintro
  iapply Hw $$ Hfix

/-- **`restore()`'s clean-read part** (`restoreViewR`'s `ns = false` branch), at the reader's token
`storeRT γ ∗ restoreRegM d`: the clean view and the clean read of the restated pre. -/
theorem mvcc.storeSess_restoreView (b : GoInterface) (γ : mvcc.StoreNames) (d : mvcc.KBReal)
    (q : Qp) (m : mvcc.Bucket) (r : mvcc.CmpRecs) :
    mvcc.bucketViewC (GF := GF) γ q m ∗
      mvcc.keyCleanReadR b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d)
        (mvcc.kbRecs γ.kb γ.bucket r) r ⊢
      mvcc.restoreViewR b γ iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) q false m
        (mvcc.kbRecs γ.kb γ.bucket r) r := by
  iintro ⟨Hv, #Hc⟩
  iunfold mvcc.restoreViewR
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe Hv
  iexact Hc

end vocab

end EtcdGrove
end Perennial
