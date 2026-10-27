/- Lean-first (no Rocq counterpart).

`New()` (counter.go): a fresh counter, at `0`, with its abstract state (`counterState`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.New)) (Val #()))
  {{ (c : Loc), RET #c; ∃ γ : GName, isCounter γ c ∗ counterState (GF := GF) γ (W64 0) }}

end spec

end counter
end lintest
end EtcdGrove
end Perennial
