module
public import Spec.go_etcd_io.bbolt.Bucket___forEachPageNode_x

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

theorem Bucket._forEachPageNode.wp_xproof (hpageNode : Bucket.pageNode.wspec (GF := GF) (hG := hG)) :
    Bucket._forEachPageNode.xspec (GF := GF) (hG := hG) := by
  intro W bl bv B dqb txl pmap pm dqp pgid depth fn nl R Q Hbv Htx Hnn Hr0 Hres Hcar Hps Hfn
  wp_start as ⟨Hb, Hib, Hnm, Hv, Hpf, Hpm, Hdb, HR⟩
  wp_auto
  wp_apply hpageNode W bl bv B dqb txl pmap pm dqp pgid Hbv Htx Hnn Hr0
      (fun _ h => by rw [Hres] at h; cases h) Hcar Hps
    $$ [Hb Hib Hnm Hv Hpf Hpm Hdb] as %p %n ⟨%Hpn, Hb, Hib, Hnm, Hv, Hpf, Hpm, Hdb⟩
  · iframe
  rcases Hpn with ⟨Hres', rfl⟩ | ⟨Hres', -, -⟩
  · have hn : n = nl := Option.some.inj (Hres'.symm.trans Hres)
    rw [hn]
    try wp_auto
    ihave HF := Hfn
    wp_bind (App (App (App (Val #fn) (Val #null)) (Val #nl)) (Val #depth))
    iapply HF $$ [HR Hb Hv Hpf Hpm Hdb]
    · iframe
    inext
    iintro ⟨%nv0, Hnd, %Hleaf, HQ, Hb, Hv, Hpf, Hpm, Hdb⟩
    try wp_auto
    rw [Hleaf]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro; exact Hleaf
  · rw [Hres] at Hres'; cases Hres'

end proof

end bbolt
end EtcdGrove
end Perennial
