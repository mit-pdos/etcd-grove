/- Lean-first (no Rocq counterpart).

`insertSorted(pend, e)` (linkv.go): a new slice, `pend` with `e` inserted before the first entry
not less than it (`insertSortedL`; `insertSortedL_perm`: a permutation of `e :: pend`). The
premise bounds `pend`'s length, as `set.spec`'s.
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
abbrev insertSorted.spec : Prop :=
  ∀ (sl : GoSlice) (es : List kvEntry) (dq : DFrac) (e : kvEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      sl ↦*{dq} es ∗ ⌜es.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.insertSorted)) (Val #sl))
      (Val #e))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* insertSortedL es e ∗ ownSliceCap kvEntry out (DFrac.own 1) }}

end spec

end linkv
end EtcdGrove
end Perennial
