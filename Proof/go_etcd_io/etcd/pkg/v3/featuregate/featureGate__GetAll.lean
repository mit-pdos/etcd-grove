/-
`(*featureGate).GetAll` (see its spec): a fresh map, `known` loaded (a persistently held `Value`)
and type-asserted (it holds a map of `known`'s type), and `maps.Copy` of the read-only map into the
fresh one.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.featureGate__GetAll
public import Spec.maps.Copy
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.Assumptions]

theorem featuregate.featureGate.GetAll.wp_proof
    (wp_Copy : maps.Copy.spec (GF := GF) (hG := hG)) :
    featuregate.featureGate.GetAll.spec (GF := GF) (hG := hG) := by
  intro p K E
  unfold featuregate.isGate
  wp_start
  icases Hpre with ⟨%km, %em, #Hk, #HK, #He, #HE⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty
    _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec.ty) as %nm Hnm
  try wp_auto
  wp_apply_core sync.atomic.Value.wp_Load _ DFrac.discard $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe Hk
  iintro -
  imod Hcl with -
  imodintro
  try wp_auto
  wp_apply (wp_Copy (K := GoString) (V := _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    nm km DFrac.discard ∅ K) $$ [Hnm] as ⟨Hnm, -⟩
  · iframe Hnm; iexact HK
  try wp_auto
  rw [GMap.map_union_empty]
  iapply HΦ
  iexact Hnm

end proof

end EtcdGrove
end Perennial
