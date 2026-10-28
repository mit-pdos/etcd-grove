/- Lean-first (no Rocq counterpart).

`New()` (logkvcompact.go): a fresh server, serving a fresh register (`isServer γ s`) at `""`
(`regState γ ""`), with its apply goroutine started. For executions of fewer than `2^64` steps
(`receiptBound GF ≤ 2^64`): the server counts its writes in a `uint64`, which must not wrap.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvcompact

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  receiptBound GF ≤ 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.New)) (Val #()))
  {{ (s : Loc), RET #s; ∃ γ : GName, isServer γ s ∗ regState (GF := GF) γ go!"" }}

end spec

end logkvcompact
end lintest
end EtcdGrove
end Perennial
