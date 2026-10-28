/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsMemberExist.lean`.
Lean-first (no Rocq counterpart); 2026-10-26: under the cluster's mutex, a lookup in the members
map (`rcLockInv`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsMemberExist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.IsMemberExist.wp_proof :
    membership.RaftCluster.IsMemberExist.spec (GF := GF) (hG := hG) := by
  intro c id
  wp_start as #Hrc
  iunfold membership.isRaftCluster at Hrc
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mm, %mem, Hmem, %Hsz, #Hloc, %rp, Hrf, Hrm⟩
  icases membership.memAt_open c _ mm mem $$ Hmem with ⟨%mp, Hfl, Hmap, Hmems, Hmf⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm id (DFrac.own (1 : Qp).half) $$ [$Hmap] as Hmap
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hfl Hmap Hmems Hrf Hrm]
  · inext
    iunfold membership.rcLockInv
    iexists mm, mem
    isplitl [Hmf Hfl Hmap Hmems]
    · iapply Hmf $$ Hfl Hmap Hmems
    iframe Hloc
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
