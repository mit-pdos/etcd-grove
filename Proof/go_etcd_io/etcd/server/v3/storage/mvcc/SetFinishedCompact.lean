/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c): its own critical
section of the batch lock around `UnsafeSetFinishedCompact`.
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.SetFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.SetFinishedCompact.wp_proof
    (h0 : mvcc.UnsafeSetFinishedCompact.spec (GF := GF) (hG := hG)) :
    mvcc.SetFinishedCompact.spec (GF := GF) (hG := hG) := by
  intro bt View RT WT PutOk Del W Dep Locked P HF Rb MW f value Pre Q Post Hv
  wp_start as ⟨#Hbt, #Hsw, Hrt, Hwt, Hhf, Hpre, #Hhook, Hupd⟩
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨#HLock, -, -, -, -, -, -, #HMeta, -⟩
  ihave #Hcap := HMeta $$ []
  · ipureintro; trivial
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  -- `tx.LockInsideApply()`: the hook run on the caller's `Pre`
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  ihave #HLock' := HLock $$ %Pre %Q %f
  iapply HLock' $$ [Hpre Hhf Hrt Hwt]
  · iframe Hpre Hhook Hhf Hrt Hwt
  inext
  iintro ⟨Hl, HW, HQ, Hrt⟩
  wp_auto_lc 1
  -- (question 5's core stage, part (1)) the compaction keys' write right, for the lock's resource
  iunfold mvcc.mwSwap at Hsw
  imod Hsw $$ [HW Hlc1] with ⟨HMW, Hback⟩
  · iframe HW Hlc1
  wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
    (Val #(GoInterface.ok bt))) (Val #value))
  iapply (h0 bt iprop(Locked [] ∗ MW) _ value Hv) $$ [Hl HMW]
  · iframe Hpkg Hcap Hl HMW
  inext
  -- (the backend-compaction stage, R2-3) the put leaves a token only `Unlock` takes; the right
  -- swapped back for the lock's resource
  iintro ⟨⟨%U, HU, #Hua⟩, HMW⟩
  imod Hback $$ HMW with HW
  iunfold mvcc.unlockAt at Hua
  icases Hua with ⟨#HUnlock0, -⟩
  (try wp_auto)
  -- the caller's update, then the deferred `tx.Unlock()`
  imod Hupd $$ [$HQ $HW] with ⟨HP, HW, HPost⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlock0 $$ [HU HW HP]
  · iframe HU HW HP
    ipureintro; rfl
  inext
  iintro -
  (try wp_auto)
  iapply HΦ
  iframe Hrt HPost

end proof

end EtcdGrove
end Perennial
