/- Lean-first (no Rocq counterpart).

`New()` (logkvrw.go): a fresh server, serving a fresh register (`isServer γ s`) at `""`
(`regState γ ""`), with its apply goroutine started.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.New)) (Val #()))
  {{ (s : Loc), RET #s; ∃ γ : GName, isServer γ s ∗ regState (GF := GF) γ go!"" }}

end spec

end logkvrw
end lintest
end EtcdGrove
end Perennial
