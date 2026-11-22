/-
`lintest/counter`'s `(*Counter).Apply` as the counter server's operation calls it, from a thread
with no thread token (the server's `main`, `remote.Serve`'s loop): given the update of its
linearization point over the counter's state (`counterState γc s` to its step, a plain fancy update
from `⊤`), it returns the step's output, boxed, with the update's result. (lintest's
`Counter.Apply.spec` is the same with an atomic triple that lends the caller's thread token, which
lintest's clients have and the server's `main` does not.) Proved in
`Net/Proof/.../lib/remote/counter/CounterApply.lean`, as lintest's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open EtcdGrove.lintest.counter

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Assumptions]

/-- See the file header. -/
abbrev CounterApply.spec : Prop :=
  ∀ (γc : GName) (c : Loc) (b : Bool) (Φ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter ∗
      isCounter γc c ∗
      (|={⊤,∅}=> ∃ s, counterState γc s ∗
        (counterState γc (counterNext s (boxB b)) ={∅,⊤}=∗ Φ (counterNext s (boxB b)))) }}
    (App (Val #(methods (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Counter.ty) go!"Apply" #c))
      (Val #(boxB b)))
  {{ (v : GoInterface), RET #v; ∃ n, ⌜v = boxI n⌝ ∗ Φ n }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
