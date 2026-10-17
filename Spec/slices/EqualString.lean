/-
`slices.Equal` on two `[]string` (etcd-io/etcd#22525: `hasPublishedAttributes` compares a member's
client URLs). Perennial does not translate `slices.Equal` (`Perennial/Code/slices.toml`): the trust
boundary, `Proof/slices/EqualString.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.slices

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `slices.Equal(s1, s2)` on `[]string` reads both slices and returns whether they hold the same
strings in the same order (Go: equal lengths and `s1[i] == s2[i]` for every `i`; a `string`'s
`==` is equality of contents). -/
abbrev slices.EqualString.spec : Prop :=
  ∀ (s1 s2 : GoSlice) (xs ys : List GoString) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ s1 ↦*{dq1} xs ∗ s2 ↦*{dq2} ys }}
    (App (App (Val #(functions _root_.Perennial.slices.Equal
        [go.GoType.SliceType go.string, go.string])) (Val #s1)) (Val #s2))
  {{ (b : Bool), RET #b; s1 ↦*{dq1} xs ∗ s2 ↦*{dq2} ys ∗ ⌜b = decide (xs = ys)⌝ }}

end spec

end EtcdGrove
end Perennial
