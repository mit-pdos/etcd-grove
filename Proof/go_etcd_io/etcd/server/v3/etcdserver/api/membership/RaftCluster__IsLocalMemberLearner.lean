/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsLocalMemberLearner.lean`.
Lean-first (no Rocq counterpart); 2026-10-26: under the cluster's mutex, the members map has an
entry for `c.localID` (`rcLockInv`'s `rcLocalIn`), so the `Panic` branch is dead; the entry's
member is owned (`ownMember`), its `IsLearner` field read and returned.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsLocalMemberLearner

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

theorem membership.RaftCluster.IsLocalMemberLearner.wp_proof :
    membership.RaftCluster.IsLocalMemberLearner.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hrc
  iunfold membership.localKept at Hrc
  iunfold membership.isRaftCluster at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, #Hloc, %rp, Hrf, Hrm⟩
  ihave #Hloc' := Hloc
  iunfold membership.rcLocalIn at Hloc'
  icases Hloc' with ⟨%lid, #Hlid, %Hin⟩
  obtain ⟨m, Hm⟩ := Option.ne_none_iff_exists'.1 Hin
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm lid (DFrac.own 1) $$ [$Hmap] as Hmap
  rw [Hm]
  simp only [Option.getD_some, Option.isSome_some, decide_true]
  (try wp_auto)
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : w64) (m : Loc) =>
      membership.ownMember (GF := GF) m) Hm).1 $$ Hmems with ⟨Hown, Hclose⟩
  iunfold membership.ownMember at Hown
  icases Hown with ⟨%mid, Hmi⟩
  iunfold membership.memberIs at Hmi
  icases Hmi with ⟨%Hnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus,
    %Hpok⟩
  (try wp_auto)
  ihave Hmems := Hclose $$ [Hid Hpu Hil Hnm Hcu Hpus Hcus]
  · iunfold membership.ownMember
    iexists mid
    iunfold membership.memberIs
    isplitr
    · ipureintro; exact Hnn
    iexists pu, cu, il, nm, pus, cus
    iframe
    ipureintro; exact Hpok
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
