module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.empty

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem empty.wp_proof : empty.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _
  wp_start
  rw [show (zero_val (optionalItem V)) = optionalItem.mk (zero_val V) false from rfl]
  wp_end

end proof

end btree
end EtcdGrove
end Perennial
