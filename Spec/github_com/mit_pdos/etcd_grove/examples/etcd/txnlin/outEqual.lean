/- Lean-first (no Rocq counterpart).

`outEqual(kind, a, b)` (etcd_txnlin.go): an output compared with the model's, for an input of
kind `kind` (`outEqualL`: only the fields that kind answers).
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
abbrev outEqual.spec : Prop :=
  ∀ (kind : w64) (a b : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.outEqual)) (Val #kind)) (Val #a)) (Val #b))
  {{ RET #(outEqualL kind a b); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
