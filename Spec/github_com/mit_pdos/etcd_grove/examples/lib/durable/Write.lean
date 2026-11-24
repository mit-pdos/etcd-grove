/-
`github.com/mit-pdos/etcd-grove/examples/lib/durable.Write`'s spec. Lean-first (no Rocq counterpart).
A trusted function (`Code/github_com/mit_pdos/etcd_grove/examples/lib/durable.toml`): its model
(`TrustedCode/github_com/mit_pdos/etcd_grove/examples/lib/durable.lean`) is the durable-state
extension's `"Write"` operation (`GooseLang/Ext/Durable/Impl.lean`).
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

/-- `Write(name, data)`: the file `name` holds `data` (created if it did not exist), in one
atomic step: a logically atomic spec, so that the files' ownership (`durableOwn`) is needed only
at that step and can come from an invariant (`GooseLang/Ext/Durable/Files.lean` gives the
per-file form). In the mode `o` (`durableOwnM`: `none`, no area reserved, any name; `some r`, the
WAL area `r` reserved, a clean absolute name outside `r/` that does not hide: `durableNameOk`).
(2026-11-21, the crash invariant) The update may use the generation's crash token when it opens
(`notCrashed`, handed back at once): the write is one step of the program, at which the token is
in the state interpretation (`wp_atomic_nc`); a client whose ghost step must run at the write's
step (kvdurable's *enter*) takes it there. -/
abbrev github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec : Prop :=
  ∀ (o : Option GoString) (name data : GoString), durableNameOk o name →
  ⊢ ∀ Φ : val → IProp GF, (notCrashed -∗ |={⊤,∅}=> notCrashed ∗ ∃ fs : DurableState, durableOwnM o fs ∗
        (durableOwnM o (<[name := data]> fs) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Write)) (Val #name))
        (Val #data)) {{ Φ }}

end spec

end Perennial
