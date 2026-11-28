/- Lean-first (no Rocq counterpart).

`resEqual(x, y)` (etcd_txnlin.go): a transaction operation's result compared with the model's
(`resEqualL`).
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
abbrev resEqual.spec : Prop :=
  ∀ (x y : TRes),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.resEqual)) (Val #x)) (Val #y))
  {{ RET #(resEqualL x y); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
