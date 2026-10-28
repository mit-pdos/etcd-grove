/- Lean-first (no Rocq counterpart).

`(*Server).Get()` (logkvrw.go): logically atomic, with no invariant of its own (mask `∅`): it
returns the register's state at its linearization point.
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
abbrev Server.Get.spec : Prop :=
  ∀ (γ : GName) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw ∗ isServer γ s }}
    <<{ ∀∀ x, regState γ x }>>
      (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server.ty @!! go!"Get")) (Val #())) @@ ∅
    <<{ regState γ x }>>
  {{ RET #x; True }}

end spec

end logkvrw
end lintest
end EtcdGrove
end Perennial
