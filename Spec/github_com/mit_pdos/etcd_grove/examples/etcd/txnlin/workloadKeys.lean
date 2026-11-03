/- Lean-first (no Rocq counterpart).

`workloadKeys()` (etcd_txnlin.go): a new slice of the workload's keys (`wks`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.txnlin


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev workloadKeys.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.workloadKeys)) (Val #()))
  {{ (out : GoSlice), RET #out; out ↦* wks ∗ ownSliceCap GoString out (DFrac.own 1) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
