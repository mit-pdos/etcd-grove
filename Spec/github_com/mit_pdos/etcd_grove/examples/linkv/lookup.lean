/- Lean-first (no Rocq counterpart).

`lookup(kv, k)` (linkv.go): the value of `k`'s first entry in `kv`, and whether there is one
(`lookupL`).
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
abbrev lookup.spec : Prop :=
  ∀ (sl : GoSlice) (es : List kvEntry) (dq : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      sl ↦*{dq} es }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.lookup')) (Val #sl)) (Val #k))
  {{ (v : GoString) (ok : Bool), RET (PairV #v #ok); sl ↦*{dq} es ∗ ⌜(v, ok) = lookupL es k⌝ }}

end spec

end linkv
end EtcdGrove
end Perennial
