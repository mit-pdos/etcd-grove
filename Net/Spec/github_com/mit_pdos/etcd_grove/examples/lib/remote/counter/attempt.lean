/-
`attempt()`: `AttemptMs` milliseconds as a `time.Duration` (some `int64`; nothing more is needed:
the duration only bounds a call's attempt).
Proved in `Net/Proof/.../lib/remote/counter/attempt.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- See the file header. -/
abbrev attempt.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.attempt)) (Val #()))
  {{ (d : w64), RET #d; True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
