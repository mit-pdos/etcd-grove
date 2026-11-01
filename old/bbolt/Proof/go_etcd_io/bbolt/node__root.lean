module
public import Spec.go_etcd_io.bbolt.node__root

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.root.wp_proof : node.root.spec (GF := GF) (hG := hG) := by
  intro nl nv rest dq
  induction rest generalizing nl nv with
  | nil =>
    intro Hp
    simp only [parentPath] at Hp
    wp_start as ⟨Hn, Hnil⟩
    wp_auto
    rw [Hp]
    try wp_auto
    rw [List.getLast_singleton]
    iapply HΦ; iframe
  | cons q rest ih =>
    intro Hp
    obtain ⟨Hpar, Hnn, Hp'⟩ := Hp
    simp only at Hpar
    wp_start as ⟨Hn, Hrest⟩
    wp_auto
    try simp only
    rw [Hpar, decide_eq_false Hnn]
    try wp_auto
    try simp only
    try rw [Hpar]
    wp_apply ih q.1 q.2 Hp' $$ [Hrest] as Hrest
    · iframe
    rw [List.getLast_cons_cons]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
