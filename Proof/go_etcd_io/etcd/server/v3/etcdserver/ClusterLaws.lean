/-
The cluster's contracts that `bootOk` held as trusted clauses until #34 stage 1 (prove-ps2-bootstage1,
2026-11-23), proved of the cluster's lock (`membership.isRaftCluster`, whose invariant has the version
slot) through `RaftCluster.Version`'s and `RaftCluster.ID`'s specs: `clusterVersionMono` (`Hcvm`),
`lease.clusterOk` (`Hclok`) and `isCluster`'s `Version`/`ID` rows (`Hisc` is now `clusterApplyRest`,
from which `clusterApplyOk` follows). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Version
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`Hcvm`**: the cluster's `Version()` is monotone, of the lock at its version name. -/
theorem clusterVersionMono_of
    (hV : membership.RaftCluster.Version.spec (GF := GF) (hG := hG)) (c : Loc) (γcv : GName)
    (hnn : c ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterV c γcv ⊢ clusterVersionMono c γcv := by
  iintro ⟨#Hpi, #Hrc⟩
  iunfold clusterVersionMono
  isplitr
  · ipureintro; exact hnn
  iintro !> %known %Φ !> Hk HΦ
  wp_apply hV c γcv known $$ [Hk] as %v Hv
  · iframe #; iexact Hk
  iapply HΦ
  iexact Hv

/-- **`Hcvm`, at some name**: of `isRaftCluster`. -/
theorem clusterVersionMono_ex
    (hV : membership.RaftCluster.Version.spec (GF := GF) (hG := hG)) (c : Loc) (hnn : c ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ⊢ ∃ γcv : GName, clusterVersionMono c γcv := by
  iintro ⟨#Hpi, #Hrc⟩
  iunfold membership.isRaftCluster at Hrc
  icases Hrc with ⟨%γcv, #Hrc⟩
  iexists γcv
  iapply clusterVersionMono_of hV c γcv hnn
  iframe #

/-- **`Hclok`**: the lessor's contract of the cluster's interface. -/
theorem clusterOk_of
    (hV : membership.RaftCluster.Version.spec (GF := GF) (hG := hG)) (c : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ⊢
    lease.clusterOk (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty) #c) := by
  iintro ⟨#Hpi, #Hrc⟩
  iunfold membership.isRaftCluster at Hrc
  icases Hrc with ⟨%γcv, #Hrc⟩
  iunfold lease.clusterOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %Φ !> - HΦ
  wp_apply hV c γcv false $$ [] as %v Hv
  · iframe #; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iapply HΦ
  icases Hv with (%Hn | ⟨-, ⟨%x, #Hx⟩, -⟩)
  · ileft; ipureintro; exact Hn
  · iright; iexists x; iexact Hx

/-- **`isCluster`** from its unproved rows (`isClusterRest`), the lock and the id. -/
theorem isCluster_of
    (hV : membership.RaftCluster.Version.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (c : Loc) (cid : w64) (hnn : c ≠ null) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF)
    (RO : apply.RestM → IProp GF) (RW : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ∗ membership.clusterCid c cid ∗
      apply.isClusterRest c Pk f BT RO RW ⊢ apply.isCluster c Pk f BT RO RW := by
  iintro ⟨#Hpi, #Hrc, #Hcid, #Hrest⟩
  iunfold apply.isClusterRest at Hrest
  icases Hrest with ⟨#HSV, #HUA, #HSD⟩
  iunfold membership.isRaftCluster at Hrc
  icases Hrc with ⟨%γcv, #Hrc⟩
  iunfold apply.isCluster
  isplitr
  · ipureintro; exact hnn
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply hV c γcv false $$ [] as %v Hv
    · iframe #; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    iapply HΦ
    icases Hv with (%Hn | ⟨-, ⟨%x, #Hx⟩, -⟩)
    · ileft; ipureintro; exact Hn
    · iright; iexists x; iexact Hx
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply hID c cid $$ []
    · iframe #
    iapply HΦ
    itrivial
  iframe #

/-- **The cluster is not nil**, of `clusterApplyRest`. -/
theorem clusterApplyRest_nn (c : Loc) : clusterApplyRest (GF := GF) c ⊢ ⌜c ≠ null⌝ := by
  iintro H
  iunfold clusterApplyRest at H
  icases H with ⟨%h, -⟩
  ipureintro; exact h

/-- **`clusterApplyOk`** (`Hisc`'s former statement) from `clusterApplyRest`, the lock and the id. -/
theorem clusterApplyOk_of
    (hV : membership.RaftCluster.Version.spec (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG)) (c : Loc) (cid : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ∗ membership.clusterCid c cid ∗ clusterApplyRest c ⊢
    clusterApplyOk c := by
  iintro ⟨#Hpi, #Hrc, #Hcid, #Hrest⟩
  iunfold clusterApplyOk
  iunfold clusterApplyRest at Hrest
  icases Hrest with ⟨%hnn, #Hrest⟩
  iintro !> %M %d %W %Pk %f %RO %RW HB Hf Hfn Hvc HRO HRW
  ihave #Hr := Hrest $$ %M %d %W %Pk %f %RO %RW HB Hf Hfn Hvc HRO HRW
  iapply isCluster_of hV hID c cid hnn
  iframe #

end lemmas

end EtcdGrove
end Perennial
