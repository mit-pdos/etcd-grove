/- Lean-first (no Rocq counterpart).

`resOf(o)` (etcd_txnlin.go): a new slice, the output's results (`resOfL`).
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
abbrev resOf.spec : Prop :=
  ∀ (x : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.resOf)) (Val #x))
  {{ (out : GoSlice), RET #out; out ↦* resOfL x ∗ ownSliceCap TRes out (DFrac.own 1) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
