/- Lean-first (no Rocq counterpart).

`newRnd(seed)` (`examples/etcd/wal/wal.go`): a fresh choice source (the tester assumes nothing of its
choices: every spec over it allows any value).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev newRnd.spec : Prop :=
  ∀ (seed : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.newRnd)) (Val #seed))
  {{ (r : Loc), RET #r; ∃ v : rnd, r ↦ v }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
