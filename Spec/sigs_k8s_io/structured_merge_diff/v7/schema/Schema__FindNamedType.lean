/-
`(*Schema).FindNamedType(name)`: the type named `name`, from the schema's lazily built index.

The index (`map[string]TypeDef`, built once under the schema's `sync.Once` and published through
its `atomic.Pointer`) is part of the persistent `isSchema`: concurrent callers race to build it,
one wins, every one reads the same index (`sync.isOnce`). The index maps a name to the **last**
type definition of that name (a Go map assigned in order); `Schema.find` takes the first, so the
premise that the names are distinct (implied by `Schema.WF`, which every `isTV` carries) makes them
agree. On a miss Go returns the zero `TypeDef` (`schema.TypeDef{}`, whose atom is zero).

A cross-package spec (its callers: `resolveNoOverrides`, and through `Resolve` the `typed` walkers
and `fieldpath`'s `EnsureNamedFieldsAreMembers`). Draft (2026-11-19, notes/smd-plan.md).
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
abbrev schema.Schema.FindNamedType.spec : Prop :=
  ∀ (sc : Loc) (S : Schema) (n : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isSchema sc S ∗ ⌜(S.types.map (·.1)).Nodup⌝ }}
    (App (Val (sc @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Schema.ty @!! go!"FindNamedType")) (Val #n))
  {{ (td : schema.TypeDef) (ok : Bool), RET (PairV #td #ok);
      match S.find n with
      | some A => iprop(⌜ok = true ∧ td.Name' = n⌝ ∗ isAtomOpt td.Atom' (some A))
      | none => iprop(⌜ok = false ∧ td = zero_val schema.TypeDef⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
