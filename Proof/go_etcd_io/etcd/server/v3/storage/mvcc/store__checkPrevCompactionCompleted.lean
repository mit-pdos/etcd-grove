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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.checkPrevCompactionCompleted.wp_proof
    (h0 : mvcc.UnsafeReadScheduledCompact.spec (GF := GF) (hG := hG))
    (h1 : mvcc.UnsafeReadFinishedCompact.spec (GF := GF) (hG := hG)) :
    mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG) := by
  intro s γ q o hcmp
  wp_start as ⟨#Hs, Hfs, HRTok⟩
  iunfold mvcc.isStore at Hs
  iNamed Hs
  -- the backend, read through the caller's share of the fields (M2, the storage side, item 17)
  icases mvcc.fieldShareAt_acc s γ q o $$ Hfs with ⟨Hflds, #Hph, Hfclose⟩
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  obtain ⟨b, ti, ssched, sstop⟩ := o
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  ihave #Hbk' := mvcc.isKeyBackendG_cmpOn b s γ Dep Ph (mvcc.hookFn γ) hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, -, -, -, -, #HCmp⟩
  subst Hbi
  ihave #HCmp' := HCmp $$ []
  · ipureintro; trivial
  icases HCmp' with ⟨-, -, #HRT⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  wp_apply HRT as %rt #Hrt
  iunfold mvcc.metaReadTx at Hrt
  (try wp_auto)
  wp_apply Hrt $$ [$HRTok] as ⟨%Rd, %Tok, Htok, #Hcap, #Hrd, #HRU⟩
  (try wp_auto)
  wp_apply (h0 rt none Rd Tok) $$ [$Htok] as %x1 %f1 ⟨Htok, -⟩
  · rw [mvcc.metaReadSpecR_none]; iframe #
  (try wp_auto)
  wp_apply (h1 rt none Rd Tok) $$ [$Htok] as %x2 %f2 ⟨Htok, -⟩
  · rw [mvcc.metaReadSpecR_none]; iframe #
  (try wp_auto)
  wp_if_destruct
  all_goals
    (try wp_auto)
    wp_apply HRU $$ [$Htok] as HRTok
    (try wp_auto)
    iapply HΦ
    iframe HRTok
    iapply Hfclose; iunfold mvcc.storeFields; simp only [named]; iframe

end proof

end EtcdGrove
end Perennial
