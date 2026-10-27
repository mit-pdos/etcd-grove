/-
`InRange(k)` (`examples/authkv/authkv.go`; the auth plan's E2b). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `InRange(k)` is `k ∈ [lo, hi)` (`inRangeK`). -/
abbrev InRange.spec : Prop :=
  ∀ (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.InRange)) (Val #k))
  {{ RET #(decide (inRangeK k)); True }}

end spec

end authkv
end EtcdGrove
end Perennial
