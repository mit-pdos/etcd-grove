/- Lean-first (no Rocq counterpart).

`(*Server).write(e)` (logkvappend.go, internal: `Put` and `Append` call it): logically atomic,
with no invariant of its own (mask `∅`): at its linearization point (in the apply goroutine, when
it applies `e`) the register goes from any state `x` to `entryStep e x` (`e.val`, or `x ++ e.val`
for an append).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvappend

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Assumptions]

/-- See the file header. -/
abbrev Server.write.spec : Prop :=
  ∀ (γ : GName) (s : Loc) (e : LEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend ∗ isServer γ s }}
    <<{ ∀∀ x, regState γ x }>>
      (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server.ty @!! go!"write")) (Val #e)) @@ ∅
    <<{ regState γ (entryStep e x) }>>
  {{ RET #(); True }}

end spec

end logkvappend
end lintest
end EtcdGrove
end Perennial
