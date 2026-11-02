/-
**`store.Restore` in either mode: the pieces** (M2's item 15, step A2; `notes/m2-storage-plan.md`,
"Step 2: restore in compaction mode"). What `store.Restore`'s proof uses of the store's right to
close by the mode (`restoreRightM`): the scheduler's stop and the fields' quarter back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **What `store.Restore` takes of the store's right, opened, in either mode**: at the current
objects `o`, the stop channel and its close, the scheduler's stop token and the jobs' queue (what
`Scheduler.Stop` takes), the closer's quarter of the fields once the scheduler is done (on, the
closer's eighth and the jobs' reclaimed: `fieldShare_reclaim`), and the compaction revision's part
the right holds: off, the frozen revision at `-1`; on, half the authority at `c`. -/
theorem restoreRightM_open (s : Loc) (γ : StoreNames) (c : Int) :
    restoreRightM (GF := GF) s γ c ⊢ ∃ o : StoreObjs,
      isStopChan o.sstop ∗ stopCloser o.sstop ∗ schedule.schedStopTok γ.sch ∗ compactQueue γ c ∗
      (schedule.schedDone γ.sch -∗ £ 1 ={⊤}=∗ fieldShareAt s γ (1 : Qp).half.half o) ∗
      (if kbCmpM γ.kb then crevUB γ.idx (1 : Qp).half c else iprop(crevFrozen γ ∗ ⌜c = -1⌝)) := by
  iintro H
  by_cases hm : kbCmpM γ.kb
  · icases (restoreRightM_on s γ c hm).1 $$ H with H
    icases (compactRightR_iff s γ c).1 $$ H with ⟨Hcu, Hq, %o, ⟨Hf, #Hsc, Hstc, Htok⟩, #HsR⟩
    iexists o
    simp only [hm, ↓reduceIte]
    iframe Hsc Hstc Htok Hq Hcu
    iintro Hd Hlc
    iapply fieldShare_reclaim s γ o $$ Hf HsR Hd Hlc
  · icases (restoreRightM_off s γ c hm).1 $$ H with ⟨H, #Hfrz, %Hc⟩
    subst Hc
    iunfold storeCloser at H
    icases H with ⟨%o, Hf, #Hsc, Hstc, Htok, Hq⟩
    iexists o
    simp only [hm, ↓reduceIte]
    iframe Hsc Hstc Htok Hq Hfrz
    iintro - -; imodintro; iexact Hf

end laws

end mvcc
end EtcdGrove
end Perennial
