/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c): a `ReadTx` with no
view (`metaReadTx`, the contract's compaction clause), the two meta keys read under its lock.
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__checkPrevCompactionCompleted
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact

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

theorem mvcc.store.checkPrevCompactionCompleted.wp_proof
    (h0 : mvcc.UnsafeReadScheduledCompact.spec (GF := GF) (hG := hG))
    (h1 : mvcc.UnsafeReadFinishedCompact.spec (GF := GF) (hG := hG)) :
    mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG) := by
  intro s γ hcmp
  wp_start as #Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  ihave #Hbk' := mvcc.isKeyBackendG_cmp b s γ Dep Ph fh hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, -, -, -, -, #HCmp⟩
  subst Hbi
  ihave #HCmp' := HCmp $$ []
  · ipureintro; trivial
  icases HCmp' with ⟨-, -, #HRT⟩
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  wp_apply HRT as %rt #Hrt
  iunfold mvcc.metaReadTx at Hrt
  icases Hrt with ⟨#HRL, #HRU, #Hrd⟩
  (try wp_auto)
  wp_apply HRL
  (try wp_auto)
  wp_apply (h0 rt) $$ [] as %x1 %f1 -
  · iexact Hrd
  (try wp_auto)
  wp_apply (h1 rt) $$ [] as %x2 %f2 -
  · iexact Hrd
  (try wp_auto)
  wp_if_destruct
  all_goals
    (try wp_auto)
    wp_apply HRU
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
