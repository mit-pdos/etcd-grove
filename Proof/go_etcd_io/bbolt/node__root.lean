/-
The proof of `Spec/go_etcd_io/bbolt/node__root.lean`: U8 (`notes/bbolt-proof-plan.md`), over `Rebalance/Heap`'s
`wtxHeap_objsDisj` (a `sorry` pending a shared fix: the heap's objects are disjoint).
-/
module

public import Spec.go_etcd_io.bbolt.node__root
public import Proof.go_etcd_io.bbolt.Rebalance.Heap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.root.wp_proof : node.root.spec (GF := GF) (hG := hG) := by
  intro tx dq X bl B n rt hb hroot
  induction hroot with
  | top n r hr hp =>
    wp_start as Hh
    ihave %Ho := wtxHeap_objs_node tx dq X bl B n r hb hr $$ Hh
    icases wtxHeap_node_ptr_acc tx dq X bl n r Ho $$ Hh with ⟨Hn, Hback⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_auto
    rw [decide_eq_true hp]
    wp_auto
    ihave Hn : (n ↦{dq} r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hh := Hback $$ Hn
    iapply HΦ
    iframe
  | up n rt r hr hp _ ih =>
    wp_start as Hh
    ihave %Ho := wtxHeap_objs_node tx dq X bl B n r hb hr $$ Hh
    icases wtxHeap_node_ptr_acc tx dq X bl n r Ho $$ Hh with ⟨Hn, Hback⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_auto
    rw [decide_eq_false hp]
    wp_auto
    ihave Hn : (n ↦{dq} r.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hh := Hback $$ Hn
    wp_apply ih $$ [Hh] as Hh
    · iframe
    try wp_auto
    iapply HΦ
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
