/-
`github.com/mit-pdos/etcd-grove/examples/lib/durable.Read`'s spec. Lean-first (no Rocq counterpart).
A trusted function (`Code/github_com/mit_pdos/etcd_grove/examples/lib/durable.toml`): its model
(`TrustedCode/github_com/mit_pdos/etcd_grove/examples/lib/durable.lean`) is the durable-state
extension's `"Read"` operation (`GooseLang/Ext/Durable/Impl.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

/-- `Read(name)`: the contents of the file `name` and `true`, or `""` and `false` if there is no
such file (`durableReadResult`), in one atomic step: a logically atomic spec, so that the files'
ownership (`durableOwn`) is needed only at that step and can come from an invariant
(`GooseLang/Ext/Durable/Files.lean` gives the per-file form). In the mode `o` (`durableOwnM`: `none`, no area reserved, any name; `some r`, the
WAL area `r` reserved, a clean absolute name outside `r/`: `durableNameOk`). -/
abbrev github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec : Prop :=
  ∀ (o : Option GoString) (name : GoString), durableNameOk o name →
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ fs : DurableState, durableOwnM o fs ∗
        (durableOwnM o fs ={∅,⊤}=∗ Φ (durableReadResult fs name))) -∗
      WP (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Read)) (Val #name)) {{ Φ }}

end spec

end Perennial
