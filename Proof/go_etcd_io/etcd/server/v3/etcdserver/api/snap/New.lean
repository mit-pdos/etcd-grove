/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/New.lean`. Lean-first (no Rocq
counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046` only). The mutex gets its lock
invariant (`snapPendingR`) with the new empty map and half of a fresh ghost variable at `∅`; the
other half is returned.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.New
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.New.wp_proof (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    snap.New.spec (GF := GF) (hG := hG) := by
  intro lg0 dir
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_NewNop as %l %Hl
    (try wp_auto)
    wp_apply (wp_map_make1 (K := w64) (V := Unit) go.uint64 (go.GoType.StructType [])) as %mref Hmap
    (try wp_auto)
    wp_alloc s as Hs
    iStructNamedPrefix Hs "f"
    imod ghostVar_alloc (GF := GF) (∅ : GMap w64 Unit) with ⟨%γ, Hv⟩
    icases ghostVar_split γ (∅ : GMap w64 Unit) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
    · rw [Qp.half_add_half]; iexact Hv
    imod sync.init_Mutex (snapPendingR γ mref) ⊤ (snapMuAddr s) $$ fpendingDBsMu [Hmap Hv1] with #Hmu
    · inext
      iunfold snapPendingR
      iexists ∅
      iframe
    ipersist fpendingDBs
    ipersist flg
    ipersist fdir
    ipersist ffsyncDir
    (try wp_auto)
    iapply HΦ
    iexists γ
    iframe Hv2
    iunfold isSnapshotter
    iexists mref, l
    iframe #
    ipureintro
    exact Hl
  · wp_apply (wp_map_make1 (K := w64) (V := Unit) go.uint64 (go.GoType.StructType [])) as %mref Hmap
    (try wp_auto)
    wp_alloc s as Hs
    iStructNamedPrefix Hs "f"
    imod ghostVar_alloc (GF := GF) (∅ : GMap w64 Unit) with ⟨%γ, Hv⟩
    icases ghostVar_split γ (∅ : GMap w64 Unit) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
    · rw [Qp.half_add_half]; iexact Hv
    imod sync.init_Mutex (snapPendingR γ mref) ⊤ (snapMuAddr s) $$ fpendingDBsMu [Hmap Hv1] with #Hmu
    · inext
      iunfold snapPendingR
      iexists ∅
      iframe
    ipersist fpendingDBs
    ipersist flg
    ipersist fdir
    ipersist ffsyncDir
    (try wp_auto)
    iapply HΦ
    iexists γ
    iframe Hv2
    iunfold isSnapshotter
    iexists mref, lg0
    iframe #
    ipureintro
    exact Hif

end proof

end EtcdGrove
end Perennial
