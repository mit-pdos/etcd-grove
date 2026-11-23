/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Member.lean`.
Lean-first (no Rocq counterpart); prove-srvloops (2026-11-21).

Under the cluster's mutex, the members map's lookup: a member (half of it, the lock's), which
`Clone` copies, its fields folded back into one points-to of the clone; or `nil`, whose `Clone()`
(stepped into: `if m == nil { return nil }`) is `nil`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Member
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member__Clone

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

theorem membership.RaftCluster.Member.wp_proof
    (hClone : membership.Member.Clone.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.Member.spec (GF := GF) (hG := hG) := by
  intro c RM id
  wp_start as #Hrc
  iunfold membership.isRaftClusterG at Hrc
  icases Hrc with ⟨%γcv, #Hrc⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInvG at Hinv
  icases Hinv with ⟨%mm, %mem, Hmem, %Hsz, Hrem⟩
  icases membership.memAt_open c _ mm mem $$ Hmem with ⟨%mp, Hfl, Hmap, Hmems, Hmf⟩
  wp_auto
  wp_apply wp_map_lookup1 _ _ mp mm id (DFrac.own (1 : Qp).half) $$ [$Hmap] as Hmap
  (try wp_auto)
  cases Hlk : mm !! id with
  | none =>
    simp only [Option.getD_none]
    -- `nil.Clone()`: `nil`
    rw [MethodUnfold.method_unfold
      (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.ty)
      (m := go!"Clone")]
    wp_auto
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hfl Hmap Hmems Hrem]
    · inext
      iunfold membership.rcLockInvG
      iexists mm, mem
      isplitl [Hmf Hfl Hmap Hmems]
      · iapply Hmf $$ Hfl Hmap Hmems
      iframe Hrem
      ipureintro; exact Hsz
    (try wp_auto)
    iapply HΦ
    ileft; ipureintro; rfl
  | some vv =>
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun (k : w64) (m : Loc) => membership.memberAt (GF := GF) m (1 : Qp).half
        ((mem !! k).getD default)) Hlk).1 $$ Hmems
      with ⟨Hown, Hmclose⟩
    wp_apply hClone vv _ _ $$ [Hown] as %mc ⟨Hown, Hmc, %Hnn⟩
    · iframe #; iframe Hown
    ihave Hmems := Hmclose $$ [Hown]
    · iexact Hown
    (try wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hfl Hmap Hmems Hrem]
    · inext
      iunfold membership.rcLockInvG
      iexists mm, mem
      isplitl [Hmf Hfl Hmap Hmems]
      · iapply Hmf $$ Hfl Hmap Hmems
      iframe Hrem
      ipureintro; exact Hsz
    (try wp_auto)
    iapply HΦ
    iright
    iunfold membership.memberIs at Hmc
    icases Hmc with ⟨%Hmcnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    iexists (go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.mk
      ((mem !! id).getD default).id
      (go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftAttributes.mk pu il)
      (go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes.mk nm cu)), pus, cus
    iframe Hpus Hcus
    iapply typedPointsto_combine _ _ _ Hmcnn
    simp only [TypedPointsto.typedPointstoDef]
    isplitl [Hid]
    · iexact Hid
    isplitl [Hpu Hil]
    · iapply typedPointsto_combine _ _ _ Hnn.1
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitl [Hnm Hcu]
    · iapply typedPointsto_combine _ _ _ Hnn.2
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    itrivial

end proof

end EtcdGrove
end Perennial
