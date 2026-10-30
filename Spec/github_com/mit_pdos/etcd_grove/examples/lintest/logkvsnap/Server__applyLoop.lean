/- Lean-first (no Rocq counterpart).

`(*Server).applyLoop()` (logkvsnap.go): the apply goroutine; it never returns. Its only
resource is the server (`isServer`): whatever it applies, it applies under the mutex, against
the lock invariant (an internal spec: only `New` calls it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvsnap

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Assumptions]

/-- See the file header. -/
abbrev Server.applyLoop.spec : Prop :=
  ∀ (γ : GName) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap ∗ isServer γ s }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Server.ty @!! go!"applyLoop")) (Val #()))
  {{ RET #(); False }}

end spec

end logkvsnap
end lintest
end EtcdGrove
end Perennial
