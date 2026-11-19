/-
`(*Schema).resolveNoOverrides(tr)` (internal): the atom of a reference: the named type's
(`FindNamedType`; the zero atom and `false` for an unknown name), or the reference's `Inlined`
atom when it has no name (in the scope only the empty `TypeRef`, whose atom is zero).

Internal (its one caller is `Resolve`), stated as `Resolve`'s. Draft (2026-11-19,
notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

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
variable [package_sem : schema.Assumptions]

/-- See the file header. -/
abbrev schema.Schema.resolveNoOverrides.spec : Prop :=
  ∀ (sc : Loc) (S : Schema) (tr : schema.TypeRef) (ot : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isSchema sc S ∗ isTypeRefOpt tr ot ∗ ⌜(S.types.map (·.1)).Nodup⌝ }}
    (App (Val (sc @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Schema.ty @!! go!"resolveNoOverrides")) (Val #tr))
  {{ (a : schema.Atom) (ok : Bool), RET (PairV #a #ok);
      ⌜ok = S.resolvesRef ot⌝ ∗ isAtomOpt a (S.resolveRef ot) }}

end spec

end smd
end EtcdGrove
end Perennial
