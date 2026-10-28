/- Lean-first (no Rocq counterpart).

`(*Server).Put(v)` (logkvrw.go): logically atomic, with no invariant of its own (mask `∅`): at
its linearization point the register goes from any state to `v`. (The linearization point is
in the apply goroutine, when it applies the write's log entry; the spec does not say so: it is
a register's write, as a register under a mutex would have it.)
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
abbrev Server.Put.spec : Prop :=
  ∀ (γ : GName) (s : Loc) (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw ∗ isServer γ s }}
    <<{ ∀∀ x, regState γ x }>>
      (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server.ty @!! go!"Put")) (Val #v)) @@ ∅
    <<{ regState γ v }>>
  {{ RET #(); True }}

end spec

end logkvrw
end lintest
end EtcdGrove
end Perennial
