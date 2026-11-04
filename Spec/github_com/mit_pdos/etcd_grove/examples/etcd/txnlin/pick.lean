/- Lean-first (no Rocq counterpart).

`pick(n, m)` (etcd_txnlin.go): `n mod m` and `n / m`, for `m` not zero.
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
abbrev pick.spec : Prop :=
  ∀ (n m : w64), m ≠ W64 0 →
  {{ (True : IProp GF) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.pick)) (Val #n)) (Val #m))
  {{ RET (PairV #(n % m) #(n / m)); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
