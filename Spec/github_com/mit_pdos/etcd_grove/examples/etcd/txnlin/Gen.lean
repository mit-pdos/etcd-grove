/- Lean-first (no Rocq counterpart).

`Gen(id)` (etcd_txnlin.go): `lintest`'s generator spec at `Apply`'s input (`linkvInOk`: a boxed
`Input` with `GenIn`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.txnlin


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  ⊢ lintest.genSpec (GF := GF)
      (functions github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Gen []) linkvInOk

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
