/- Lean-first (no Rocq counterpart).

`holds(kvs, c)` (linkvtxn.go): a comparison's verdict on the store (`holdsL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev holds.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac) (c : Cmp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗ sl ↦*{dq} es }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.holds)) (Val #sl)) (Val #c))
  {{ RET #(holdsL es c); sl ↦*{dq} es }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
