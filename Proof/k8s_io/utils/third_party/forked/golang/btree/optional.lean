module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.optional

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

theorem optional.wp_proof : optional.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ item
  wp_start
  wp_auto
  wp_end

end proof

end btree
end EtcdGrove
end Perennial
