/-
`deadline(d)`: `time.Now().Add(d)`, a time (its value is not used: the net extension does not
model deadlines' values, `deadline_au`). Proved in `Net/Proof/.../lib/remote/deadline.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev deadline.spec : Prop :=
  ∀ (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.deadline)) (Val #d))
  {{ (t : time.Time), RET #t; True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
