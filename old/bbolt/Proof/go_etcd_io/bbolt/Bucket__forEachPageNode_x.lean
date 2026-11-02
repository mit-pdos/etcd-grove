module
public import Spec.go_etcd_io.bbolt.Bucket__forEachPageNode_x
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.forEachPageNode.wp_xproof (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hfe : Bucket._forEachPageNode.xspec (GF := GF) (hG := hG)) :
    Bucket.forEachPageNode.xspec (GF := GF) (hG := hG) := by
  intro W bl bv B dqb txl pmap pm dqp fn nl R Q Hbv Htx Hnn Hpg Hr0 Hres Hcar Hps Hfn
  subst Hbv
  wp_start as ⟨Hb, Hib, Hnm, Hv, Hpf, Hpm, Hdb, HR⟩
  wp_auto
  rw [Hpg]
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  try wp_auto
  wp_apply hfe W bl B.bv B dqb txl pmap pm dqp B.ib.root' (W64 0) fn nl R Q rfl Htx Hnn
      (fun h => absurd h Hr0) Hres Hcar Hps Hfn
    $$ [Hb Hib Hnm Hv Hpf Hpm Hdb HR] as ⟨Hb, Hib, Hnm, Hv, Hpf, Hpm, Hdb, HQ⟩
  · iframe
  try wp_auto
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
