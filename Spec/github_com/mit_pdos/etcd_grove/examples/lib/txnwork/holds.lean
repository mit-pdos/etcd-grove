/- Lean-first (no Rocq counterpart).

`holds(kvs, c)` (etcd_txnlin.go): a comparison's verdict on the store (`holdsL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.txnwork


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Assumptions]

/-- See the file header. -/
abbrev holds.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac) (c : Cmp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork ∗ sl ↦*{dq} es }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.holds)) (Val #sl)) (Val #c))
  {{ RET #(holdsL es c); sl ↦*{dq} es }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
