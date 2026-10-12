module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.elemRef__count_w

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

theorem elemRef.count.wp_wproof (h : Page.Count.spec (GF := GF) (hG := hG)) :
    elemRef.count.wspec (GF := GF) (hG := hG) := by
  intro rl rv dqr nv dqn q pg Hpage
  wp_start as ⟨Hr, Hx⟩
  wp_auto
  by_cases Hnode : rv.node' = null
  · obtain ⟨Hc, Hlen⟩ := Hpage Hnode
    rw [Hnode, decide_eq_true rfl, Bool.not_true]
    simp only [↓reduceIte] at *
    try wp_auto
    icases (page_header_bytes (hG := hG) _ q pg Hlen Hc).1 $$ Hx with ⟨Hhd, Hrest⟩
    wp_apply h _ (pageOf pg) q $$ [Hhd] as Hhd
    · iframe
    try wp_auto
    ihave Hx := (page_header_bytes (hG := hG) _ q pg Hlen Hc).2 $$ [$Hhd $Hrest]
    have Hlt := leAt_lt pg 10 2
    rw [show uint.Z (W16 ((pageCount pg : Nat) : Int)) = ((pageCount pg : Nat) : Int) by
      unfold pageCount at *; word]
    iapply HΦ; iframe
  · rw [decide_eq_false Hnode, Bool.not_false]
    simp only [Hnode, ↓reduceIte] at *
    try wp_auto
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
