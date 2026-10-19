/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsIDRemoved.lean`.
Lean-first (no Rocq counterpart); D21 M2 (2026-10-19): under the cluster's mutex, the removed
map, empty (`rcLockInv`), has no entry for `id`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsIDRemoved

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.IsIDRemoved.wp_proof :
    membership.RaftCluster.IsIDRemoved.spec (GF := GF) (hG := hG) := by
  intro c id
  wp_start as #Hrc
  iunfold membership.isRaftCluster at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, #Hloc, %rp, Hrf, Hrm⟩
  (try wp_auto)
  wp_apply wp_map_lookup1 _ _ rp (∅ : GMap w64 Bool) id (DFrac.own 1) $$ [$Hrm] as Hrm
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems Hrf Hrm]
  · inext
    iunfold membership.rcLockInv
    iexists mp, mm
    iframe Hmf Hmap Hmems Hloc
    isplitr
    · ipureintro; exact Hsz
    iexists rp
    iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
