module
public import Spec.go_etcd_io.bbolt.Bucket__node_s
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Proof.go_etcd_io.bbolt.ShapeMat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.node` with the shape: `Bucket.node.spec`, the shape following by `bktShape_nodeRes`
(`ShapeMat.lean`). -/
theorem Bucket.node.wp_sproof (hnode : Bucket.node.spec (GF := GF) (hG := hG)) :
    Bucket.node.sspec (GF := GF) (hG := hG) := by
  intro γ W hwm bl B txl st pmap pm dqp pgid parent p pg src HvOK Hclean Htx Hpre
  wp_start_folded as ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb, Hsh⟩
  wp_apply hnode W bl B txl st pmap pm dqp pgid parent p pg src HvOK Htx
    (fun l h => (Hclean.2.2.2.2.1 _ l h).1)
    (fun h => ⟨(Hpre h).1, by
      rcases (Hpre h).2 with ⟨h0, -⟩ | ⟨i, rp, w, hrp, -⟩
      · exact Or.inl h0
      · exact Or.inr (by rw [hrp]; rfl)⟩)
    $$ [Hb Hv Hst Hpf Hpm Hdb] as %l %B' %st' ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb, %Hres⟩
  · iframe
  ihave Hsh := bktShape_nodeRes γ W hwm bl B pm pgid parent p pg src l B' st st' HvOK Hclean Hpre Hres
    $$ Hsh
  icases Hsh with ⟨Hsh, %Hf⟩
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hres, Hf.1⟩

end proof

end bbolt
end EtcdGrove
end Perennial
