/-
`github.com/mit-pdos/etcd-grove/examples/durable.Write`'s spec. Lean-first (no Rocq counterpart).
A trusted function (`Code/github_com/mit_pdos/etcd_grove/examples/durable.toml`): its model
(`TrustedCode/github_com/mit_pdos/etcd_grove/examples/durable.lean`) is the durable-state
extension's `"Write"` operation (`GooseLang/Ext/Durable/Impl.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.durable.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.durable.Assumptions]

/-- `Write(name, data)`: the file `name` holds `data` (created if it did not exist), in one
atomic step: a logically atomic spec, so that the files' ownership (`durableOwn`) is needed only
at that step and can come from an invariant (`GooseLang/Ext/Durable/Files.lean` gives the
per-file form). -/
abbrev github_com.mit_pdos.etcd_grove.examples.durable.Write.spec : Prop :=
  ∀ (name data : GoString),
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ fs : DurableState, durableOwn fs ∗
        (durableOwn (<[name := data]> fs) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.durable.Write)) (Val #name))
        (Val #data)) {{ Φ }}

end spec

end Perennial
