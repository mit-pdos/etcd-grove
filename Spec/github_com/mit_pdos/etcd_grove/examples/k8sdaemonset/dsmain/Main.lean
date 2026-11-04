/-
`Main(checks)` (`dsmain.go`): `run(serverConfig(), checks)`. Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`).

The closed theorem's program body (`Adequacy.lean`): no thread of it panics or is stuck. The
premises are the bounds the adequacy theorem fixes (`run`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Defs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI apimodel dsctl informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]

/-- **`Main(checks)`**: returns (no panic). -/
abbrev Main.spec : Prop :=
  ∀ (nchk : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ ⌜receiptBound GF ≤ 2 ^ 63⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Main)) (Val #nchk))
  {{ RET #(); True }}

end spec

end dsmain
end EtcdGrove
end Perennial
