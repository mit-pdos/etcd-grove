/-
`typed.deduceAtom(atom, val)` (internal): the atom narrowed to the value's kind. In the scope
every atom is of one kind (`isAtom`: the other two pointers nil), so the narrowed atom is the atom
itself, whatever the value.

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
abbrev typed.deduceAtom.spec : Prop :=
  ∀ (a : schema.Atom) (A : Atom) (v : value.Value) (dq : DFrac) (o : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isAtomOpt a (some A) ∗ isValO v dq o }}
    (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom)) (Val #a)) (Val #v))
  {{ RET #a; isValO v dq o }}

end spec

end smd
end EtcdGrove
end Perennial
