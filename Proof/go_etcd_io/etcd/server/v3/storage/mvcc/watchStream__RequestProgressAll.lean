/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgressAll

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.RequestProgressAll.wp_proof :
    mvcc.watchStream.RequestProgressAll.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ
  wp_start as ⟨Hws, HPR⟩
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  wp_apply HprogAll $$ [$Hwm $Hws $HPR] as %b ⟨Hwm, HPR⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, closed, cm, wm, CM, WM
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hnn⟩
  iapply HΦ
  iframe HPR

end proof

end EtcdGrove
end Perennial
