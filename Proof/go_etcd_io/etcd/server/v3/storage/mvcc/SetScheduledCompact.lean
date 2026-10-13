/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c): its own critical
section of the batch lock around `UnsafeSetScheduledCompact`.
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetScheduledCompact

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.SetScheduledCompact.wp_proof
    (h0 : mvcc.UnsafeSetScheduledCompact.spec (GF := GF) (hG := hG)) :
    mvcc.SetScheduledCompact.spec (GF := GF) (hG := hG) := by
  intro bt View Del W Dep Locked P f value Pre Q Post Hv
  wp_start as ⟨#Hbt, Hpre, #Hhook, Hupd⟩
  ihave #Hbt0 := Hbt
  iunfold mvcc.batchTxSpec at Hbt
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨#HLock, -, #HUnlock0, -⟩
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  -- `tx.LockInsideApply()`: the hook run on the caller's `Pre`
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  ihave #HLock' := HLock $$ %Pre %Q
  iapply HLock' $$ [Hpre]
  · iframe Hpre Hhook
  inext
  iintro ⟨Hl, HW, HQ, -⟩
  (try wp_auto)
  wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetScheduledCompact))
    (Val #(GoInterface.ok bt))) (Val #value))
  iapply (h0 bt View Del W Dep Locked P f [] value Hv) $$ [Hl]
  · iframe Hpkg Hbt0 Hl
  inext
  iintro Hl
  (try wp_auto)
  -- the caller's update, then the deferred `tx.Unlock()`
  imod Hupd $$ [$HQ $HW] with ⟨HP, HW, HPost⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlock0 $$ [Hl HW HP]
  · iframe Hl HW HP
  inext
  iintro -
  (try wp_auto)
  iapply HΦ
  iexact HPost

end proof

end EtcdGrove
end Perennial
