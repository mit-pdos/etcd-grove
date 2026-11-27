/- Lean-first (no Rocq counterpart).

`genFrom(n)` (etcd_txnlin.go): an input `Apply` may take (`GenIn`), for any `n`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.GenLemmas

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
abbrev genFrom.spec : Prop :=
  ∀ (n : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.genFrom)) (Val #n))
  {{ (x : Input), RET #x; ⌜GenIn x⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
