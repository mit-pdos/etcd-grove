/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsIDRemoved.lean`.
Lean-first (no Rocq counterpart); D21 M2 (2026-10-19): under the cluster's mutex, the removed
map's entry for `id` (D43 M4, 2026-10-26: at any side condition, `rcLockInvG`; until then the
static cluster's empty map).
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
  intro c RM Pr id HPr
  wp_start as #Hrc
  iunfold membership.isRaftClusterG at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInvG at Hinv
  icases Hinv with ⟨%ms, %mem, Hmem, %Hsz, %lid, %rp, %rm, #Hlid, Hrf, Hrm, HRM⟩
  icases HPr lid ms rm $$ HRM with ⟨%Hp, HRM⟩
  (try wp_auto)
  wp_apply wp_map_lookup1 _ _ rp rm id (DFrac.own 1) $$ [$Hrm] as Hrm
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRM]
  · inext
    iunfold membership.rcLockInvG
    iexists ms, mem
    iframe Hmem
    isplitr
    · ipureintro; exact Hsz
    iexists lid, rp, rm
    iframe
    iexact Hlid
  (try wp_auto)
  iapply HΦ
  ipureintro
  exact ⟨rm, Hp, rfl⟩

end proof

end EtcdGrove
end Perennial
