/- Lean-first (no Rocq counterpart).

`cmpStr(a, b)` (linkvtxn.go): -1, 0 or 1 as `a` is below, equal to or above `b` (Go's `<` on
strings: `cmpS`).
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
abbrev cmpStr.spec : Prop :=
  ∀ (a b : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStr)) (Val #a)) (Val #b))
  {{ RET #(ordW (cmpS a b)); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
