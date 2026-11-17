/- Lean-first (no Rocq counterpart).

`(*rnd).next()` (`examples/etcd/wal/wal.go`): any value; the source's state moves.
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
abbrev rnd.next.spec : Prop :=
  ∀ (r : Loc) (v : rnd),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ r ↦ v }}
    (App (Val (r @!! go.GoType.PointerType rnd.ty @!! go!"next")) (Val #()))
  {{ (x : w64), RET #x; ∃ v' : rnd, r ↦ v' }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
