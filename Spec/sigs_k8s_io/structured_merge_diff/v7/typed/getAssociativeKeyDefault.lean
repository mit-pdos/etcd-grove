/-
`typed.getAssociativeKeyDefault(s, list, fieldName)` (internal): the default of a key field of an
associative list's element map type: none in the scope (no field defaults: `isField`), so
`(nil, nil)`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.getAssociativeKeyDefault.spec : Prop :=
  ∀ (sc : Loc) (S : Schema) (lp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString)
    (fs : List (GoString × TypeRef)) (el : Option TypeRef) (r : ElemRel) (n : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isSchema sc S ∗ isListRep lp e rel ks ∗ ⌜S.WF ∧ S.find e.name = some (.map fs el r)⌝ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.getAssociativeKeyDefault)) (Val #sc)) (Val #lp)) (Val #n))
  {{ RET (PairV #(interface.nil : GoInterface) #(interface.nil : GoInterface)); True }}

end spec

end smd
end EtcdGrove
end Perennial
