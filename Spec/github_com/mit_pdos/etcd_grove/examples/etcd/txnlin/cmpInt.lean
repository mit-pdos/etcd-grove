/- Lean-first (no Rocq counterpart).

`cmpInt(a, b)` (linkvtxn.go): -1, 0 or 1 as `a` is below, equal to or above `b` (signed:
`cmpW`).
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
abbrev cmpInt.spec : Prop :=
  ∀ (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt)) (Val #a)) (Val #b))
  {{ RET #(ordW (cmpW a b)); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
