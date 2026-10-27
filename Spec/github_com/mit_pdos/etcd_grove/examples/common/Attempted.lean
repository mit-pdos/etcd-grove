/- Lean-first (no Rocq counterpart).

`Attempted(tried, key, val)` (`examples/common/watch.go`; watchkv's until 2026-10-22, D33): `true` when `(key, val)` is one of the Puts `tried`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev Attempted.spec : Prop :=
  ∀ (sl : GoSlice) (tried : List wkv) (dq : DFrac) (key val : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      sl ↦*{dq} tried }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Attempted)) (Val #sl))
      (Val #key)) (Val #val))
  {{ (b : Bool), RET #b; sl ↦*{dq} tried ∗ ⌜(key, val) ∈ tried.map pairOf → b = true⌝ }}

end spec

end common
end EtcdGrove
end Perennial
