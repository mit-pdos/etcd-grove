module
public import Proof.go_etcd_io.bbolt.NodeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.root()`, given the path of parent pointers from `n` up (`parentPath`): its last node. -/
abbrev node.root.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (rest : List (Loc × node)) (dq : DFrac),
  parentPath ((nl, nv) :: rest) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ [∗list] p ∈ (nl, nv) :: rest, p.1 ↦{dq} p.2 }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"root")) (Val #()))
  {{ RET #(((nl, nv) :: rest).getLast (List.cons_ne_nil _ _)).1;
      [∗list] p ∈ (nl, nv) :: rest, p.1 ↦{dq} p.2 }}

end spec

end bbolt
end EtcdGrove
end Perennial
