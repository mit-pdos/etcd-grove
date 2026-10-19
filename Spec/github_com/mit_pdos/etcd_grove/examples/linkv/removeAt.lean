/- Lean-first (no Rocq counterpart).

`removeAt(pend, i)` (linkv.go): a new slice, `pend` without its `i`-th entry (`removeAtL`), for an
index in bounds.
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
abbrev removeAt.spec : Prop :=
  ∀ (sl : GoSlice) (es : List kvEntry) (dq : DFrac) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      sl ↦*{dq} es ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.removeAt)) (Val #sl)) (Val #i))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* removeAtL es (sint.nat i) ∗ ownSliceCap kvEntry out (DFrac.own 1) }}

end spec

end linkv
end EtcdGrove
end Perennial
