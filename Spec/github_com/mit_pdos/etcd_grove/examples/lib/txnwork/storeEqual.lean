/- Lean-first (no Rocq counterpart).

`storeEqual(a, b)` (etcd_txnlin.go): whether the stores `a` and `b` hold the same entries and
revision.
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
abbrev storeEqual.spec : Prop :=
  ∀ (a b : store) (ga gb : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork ∗ storeOwn a ga ∗ storeOwn b gb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.storeEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (ga = gb)); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
