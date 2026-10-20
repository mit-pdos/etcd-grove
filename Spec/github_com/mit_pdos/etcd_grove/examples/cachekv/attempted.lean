/- Lean-first (no Rocq counterpart).

`attempted(tried, key, val)` (cachekv.go): `true` when `(key, val)` is one of the Puts `tried`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.cachekv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- See the file header. -/
abbrev attempted.spec : Prop :=
  ∀ (sl : GoSlice) (tried : List ckv) (dq : DFrac) (key val : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv ∗
      sl ↦*{dq} tried }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.attempted)) (Val #sl))
      (Val #key)) (Val #val))
  {{ (b : Bool), RET #b; sl ↦*{dq} tried ∗ ⌜(key, val) ∈ tried.map pairOf → b = true⌝ }}

end spec

end cachekv
end EtcdGrove
end Perennial
