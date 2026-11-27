/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`below(n)`: `primitive.RandomUint64() % n`, a number below `n` for `n > 0` (`n = 0` divides
by zero).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- See the file header. -/
abbrev below.spec : Prop :=
  ∀ (n : w64), 0 < uint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below)) (Val #n))
  {{ (r : w64), RET #r; ⌜uint.Z r < uint.Z n⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
