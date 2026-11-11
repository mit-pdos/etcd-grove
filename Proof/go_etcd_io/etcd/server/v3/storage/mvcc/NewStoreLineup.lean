/-
**Probe (B3, R1's restatement): `NewStore`'s resources from the session to `restore()`, over
`NewStore.specR`'s restated pre** (`NewStoreR.lean`). Scratch: these are lemmas, not a partial WP
of `NewStore`'s body. They show what each step of `NewStore.lean` l.408-550 takes at the restated
pre (on, a real backend `d`):

1. **The session** (`BatchTx`, `LockOutsideApply`, the creations, `Unlock`, `ForceCommit`): over the
   session contract (`storeSessT_session`, `NewStoreSess.lean`). Its `Unlock` takes `W ∗ P`, where
   `W` is the store's lock resource `storeW s γ`, which at a real backend is the late-bound `lateW
   d.gx`, the very `Wi` that `LockOutsideApply` gave (`sess_W_of_Wi`). So the session hands the lock
   back unregistered, and the store's registration stays pending (`writerReg`'s middle disjunct,
   `kbRegRight ∗ writerRes`), as after `store.Restore`. The fresh proof registers at this `Unlock`
   (`storeW_register` with the writer's resource at `[[], []]`). Over a bucket that already holds the
   image, the writer's resource at `[[], []]` does not exist: its `bucketViewL` would say the bucket
   is empty. So the whole view stays for `restore()` (step 2).
2. **`restore()`'s view and records** (`ns = false`): the image (`restoreImageM`, on) gives the
   whole clean view of the cut entries, the records `NC`, and the cut (`restore_inputs`). With the
   clean read lent `storeRT γ ∗ restoreRegM d`, that is `restoreViewR` at `q = 1`.
3. **The fix** when `restore()` gives the lent token back (`restoreDone`; in the resume
   continuation if the records resume a compaction): the registration fixed, the contract at the
   records (`restoreDone_fix`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreSess

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section lineup
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Step 1**: at a real backend, the session's `Unlock` takes back the lock's initial resource
(`kbWi` is `storeW`: both `lateW d.gx`), with nothing registered. -/
theorem mvcc.NewStore.sess_W_of_Wi (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal)
    (hk : γ.kb = some d) : mvcc.kbWi (GF := GF) γ.kb ⊢ mvcc.storeW s γ := by
  unfold mvcc.kbWi mvcc.storeW
  rw [hk]

/-- **Step 2**: the image (on) gives `restore()`'s clean view (whole), its records' resource and the
cut; with the clean read lent `storeRT γ ∗ restoreRegM d`, `restoreViewR` at `ns = false`. -/
theorem mvcc.NewStore.restore_inputs (b : GoInterface) (γ : mvcc.StoreNames) (d : mvcc.KBReal)
    (γb : GName) (L : mvcc.Log) (r : mvcc.CmpRecs) (hcm : d.cm = true) (hb : γ.bucket = γb)
    (hk : γ.kb = some d) :
    mvcc.restoreImageM (GF := GF) d γb L r ∗
      mvcc.keyCleanReadR b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d)
        (mvcc.kbRecs γ.kb γ.bucket r) r ⊢
      ∃ ents : List mvcc.KvEnt,
        mvcc.restoreViewR b γ iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) 1 false
          (mvcc.bucketOfEnts ents) (mvcc.kbRecs γ.kb γ.bucket r) r ∗
        mvcc.kbRecs γ.kb γ.bucket r ∗
        mvcc.kbVals (some d) (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∅ ∗
        backend.fkVM d.γB true ∗
        ⌜mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents⌝ := by
  iintro ⟨Him, #Hc⟩
  iunfold mvcc.restoreImageM at Him
  simp only [hcm, ↓reduceIte]
  icases Him with ⟨%ents, Hv, ⟨Hrec, Hvals⟩, Hfk, %Hok⟩
  iexists ents
  rw [hk, hb]
  iframe Hrec Hvals Hfk
  isplitl [Hv]
  · rw [← hk, ← hb]
    iapply mvcc.storeSess_restoreView b γ d 1 (mvcc.bucketOfEnts ents) r
    iframe Hc
    iunfold mvcc.bucketViewC
    rw [hk, hb]
    iexact Hv
  · ipureintro; exact Hok

/-- **Step 3**: `restore()`'s results give the lent token back with the unfixed registration; fixed,
the contract at the records. -/
theorem mvcc.NewStore.restoreDone_fix (s : Loc) (b : GoInterface) (ti : Loc) (q1 : Qp)
    (dqb dqi dqc : DFrac) (L' : mvcc.Log) (ents : List mvcc.KvEnt) (r : mvcc.CmpRecs)
    (NC RevQ : IProp GF) (γ : mvcc.StoreNames) (P : IProp GF) (d : mvcc.KBReal) (E : CoPset) :
    mvcc.restoreDone (GF := GF) s b ti q1 dqb dqi dqc L' ents r
        iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) NC RevQ ∗
      (mvcc.restoreFixM d γ -∗ mvcc.storeBackendTR b s γ P r) ⊢
      |={E}=> mvcc.restoreDone s b ti q1 dqb dqi dqc L' ents r (mvcc.storeRT γ) NC RevQ ∗
        mvcc.storeBackendTR b s γ P r := by
  iintro ⟨Hd, Hw⟩
  iunfold mvcc.restoreDone at Hd
  icases Hd with ⟨⟨Hrt, Hreg⟩, Hnc, Hrc, Hrq, Hcur, Hcmp, Hb, Hkv⟩
  ihave HT := mvcc.storeSess_fix b s γ P d r $$ [$Hreg $Hw]
  imod HT with HT
  imodintro
  iframe HT
  iunfold mvcc.restoreDone
  iframe Hrt Hnc Hrc Hrq Hcur Hcmp Hb Hkv

end lineup

end EtcdGrove
end Perennial
