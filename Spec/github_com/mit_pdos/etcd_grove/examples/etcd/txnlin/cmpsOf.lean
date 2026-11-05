/- Lean-first (no Rocq counterpart).

`cmpsOf(in)` (etcd_txnlin.go): a new slice, the transaction's comparisons (`cmpsOfL`).
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
abbrev cmpsOf.spec : Prop :=
  ∀ (x : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpsOf)) (Val #x))
  {{ (out : GoSlice), RET #out; out ↦* cmpsOfL x ∗ ownSliceCap Cmp out (DFrac.own 1) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
