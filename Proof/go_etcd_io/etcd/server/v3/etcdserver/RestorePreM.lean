/-
What the apply thread holds for `watchableStore.Restore`, in either mode (M2's item 15, stage B):
`restorePre_of_apply`'s store half, the store's right by the mode (`restoreRightM`): off, the inner
store's closer and the frozen revision, from the server's closer (`srvKVCloserW`, today's
`srvKVCloser` off); on, the apply thread's compaction right (`apply.cmpRight` at the store's
compaction revision), the server's closer holding only the watchable store's own parts.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestorePre
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`watchableStore.Restore`'s store half, from the apply thread, in either mode**
(`restorePre_of_apply` with the right by the mode): the apply thread's KV resources at the log
`log`, its compaction right at `c` (`apply.cmpRight`: on, the store's restorable right; off, `c =
-1`) and the server's closer (`srvKVCloserW`) give the right `Restore` takes (`restoreRightM` at
`c`), the writer's resources and the watchable store's own closer parts. -/
theorem etcdserver.restorePre_of_applyW (s : Loc) (E : apply.AEnv GF) (log : mvcc.Log) (c : Int)
    (hwq : E.γ.watchQ = true) (htie : mvcc.kbCmpM E.γ.kb ↔ E.γ.cm = true) :
    apply.kvOwn E log ∗ apply.cmpRight E c ∗ srvKVCloserW s E ⊢
      ∃ (ws : Loc) (γw : mvcc.WsNames), ⌜γw.st = E.γ⌝ ∗ mvcc.isWatchableStore ws E.s γw ∗
        mvcc.restoreRightM E.s γw.st c ∗ mvcc.writerFrag γw.st ∗ mvcc.writerOwn γw.st ∗
        mvcc.watchWriter γw log ∗
        (mvcc.storeReader E.s E.γ ∗ apply.leasesLive E.γ (mvcc.stateAfter log) ∗ E.RD) ∗
        (∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗
          mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) := by
  by_cases h : mvcc.kbCmpM E.γ.kb
  · -- on: the right is the apply thread's, the closer the watchable store's own parts
    iintro ⟨Hown, Hcr, Hcl⟩
    unfold apply.cmpRight srvKVCloserW
    simp only [h, ↓reduceIte]
    icases Hcr with ⟨Hcr, -⟩
    icases Hcl with ⟨%wsl, #Hkvf, %stc, #Hstc, Hstcl, Hwsw⟩
    iunfold apply.kvOwn at Hown
    icases Hown with ⟨Hrd, Hkw, Hll, HRD, Hwo⟩
    iunfold txn.kvWriter at Hkw
    icases Hkw with ⟨Hsw, Hwl, Hfrag⟩
    iunfold txn.wlogOwn at Hwl
    icases Hwl with ⟨Hwl, Hpin⟩
    iunfold txn.wlogOwnW at Hwl
    rw [hwq]
    simp only [↓reduceIte]
    icases Hwl with ⟨%ws, %γw, %hγw, #Hws, Hwl, -⟩
    iexists ws, γw
    iunfold mvcc.watchWriter
    rw [hγw]
    ihave Hr : mvcc.restoreRightM E.s E.γ c $$ [Hcr]
    · iapply (mvcc.restoreRightM_on E.s E.γ c h).2
      iexact Hcr
    ihave Hcp : iprop(∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗
        mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) $$ [Hstcl Hwsw]
    · iexists wsl, stc
      iframe Hkvf Hstc Hstcl Hwsw
    iframe Hws Hr Hfrag Hwo Hrd Hll HRD Hcp
    isplitr
    · ipureintro; rfl
    iunfold txn.soleWriter at Hsw
    icases Hsw with ⟨#Hc, Htoks, -⟩
    simp only [txn.soleBudget, mvcc.wBudget]
    iframe Hc Htoks Hwl Hpin
  · -- off: today's, the right the closer and the frozen revision at `-1`
    have hcm : E.γ.cm = false := Bool.eq_false_iff.mpr (fun hc => h (htie.2 hc))
    iintro ⟨Hown, Hcr, Hcl⟩
    unfold apply.cmpRight
    simp only [h, ↓reduceIte]
    icases Hcr with %hc
    rw [srvKVCloserW_off s E h]
    icases etcdserver.restorePre_of_apply s E log hwq hcm $$ [$Hown $Hcl] with
      ⟨%ws, %γw, %hγw, #Hws, Hscl, Hfrag, HwOwn, #Hfrz, HwW, Hrest, Hcp⟩
    iexists ws, γw
    iframe Hws Hfrag HwOwn HwW Hrest Hcp
    isplitr
    · ipureintro; exact hγw
    iapply (mvcc.restoreRightM_off E.s γw.st c (by rw [hγw]; exact h)).2
    iframe Hscl Hfrz
    ipureintro; exact hc

end lemmas

end EtcdGrove
end Perennial
