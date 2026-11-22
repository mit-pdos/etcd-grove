/-
`Gen(id)`: a client's next input, an increment or a read at random (`RandomUint64() % 2 == 0`),
boxed: `lintest`'s generator spec (`genSpec`) at the counter's inputs, the boxed `bool`s (`boxB`,
`cR γ`'s `iv`), for the function value `Gen` that `Orch` passes to `remote.Check`.
Proved in `Net/Proof/.../lib/remote/counter/Gen.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Gen [])
      (fun x => iprop(∃ b : Bool, ⌜x = boxB b⌝))

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
