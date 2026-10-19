/- Lean-first (no Rocq counterpart).

`entriesEqual(a, b)` (linkv.go): whether the two slices hold the same entries, in order (Go's
`!=` on `kvEntry`, field by field).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev entriesEqual.spec : Prop :=
  ∀ (sa sb : GoSlice) (xs ys : List kvEntry) (dqa dqb : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      sa ↦*{dqa} xs ∗ sb ↦*{dqb} ys }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.entriesEqual)) (Val #sa))
      (Val #sb))
  {{ RET #(decide (xs = ys)); sa ↦*{dqa} xs ∗ sb ↦*{dqb} ys }}

end spec

end linkv
end EtcdGrove
end Perennial
