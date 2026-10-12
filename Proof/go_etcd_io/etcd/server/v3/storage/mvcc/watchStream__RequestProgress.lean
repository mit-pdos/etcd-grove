/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgress

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

theorem mvcc.watchStream.RequestProgress.wp_proof :
    mvcc.watchStream.RequestProgress.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ id
  wp_start as Hws
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hwm] as Hwm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, closed, cm, wm, CM, WM
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hnn⟩
  cases hk : WM !! id with
  | none =>
    wp_auto
    iapply HΦ
    itrivial
  | some w =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_apply Hprog $$ [Hws]
    · iapply Hws $$ %id %w %hk
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
