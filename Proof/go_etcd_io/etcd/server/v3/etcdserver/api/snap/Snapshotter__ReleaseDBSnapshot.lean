/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__ReleaseDBSnapshot.lean`.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046` only). The
linearization point is the map delete, inside the critical section.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseDBSnapshot
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.Snapshotter.ReleaseDBSnapshot.wp_proof :
    snap.Snapshotter.ReleaseDBSnapshot.spec (GF := GF) (hG := hG) := by
  intro s γ dir id
  iintro %Φ ⟨#Hpkg, #Hs⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isSnapshotter at Hs
  icases Hs with ⟨%mref, %lg, #Hm, #Hlg, %Hlgnn, #Hdir, #Hfs, #Hmu⟩
  wp_method_call
  wp_call
  wp_call
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold snapPendingR at HR
  icases HR with ⟨%M, Hmap, Hg⟩
  (try wp_auto)
  wp_apply (wp_mapDelete mref M id go.uint64 (go.GoType.StructType [])) $$ [$Hmap] as Hmap
  -- the linearization point
  simp only [LawfulSet.diff_empty]
  iapply fupd_wp
  imod HAU with ⟨%M', Hs, Hcommit⟩
  icombine Hg Hs gives % ⟨_, Heq⟩
  subst Heq
  imod ghostVar_update_halves (GMap.delete id M) γ _ _ $$ Hg Hs with ⟨Hg, Hs⟩
  imod Hcommit $$ [Hs] with HΦ
  · iexact Hs
  imodintro
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hmap Hg]
  · inext
    iunfold snapPendingR
    iexists _
    iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
