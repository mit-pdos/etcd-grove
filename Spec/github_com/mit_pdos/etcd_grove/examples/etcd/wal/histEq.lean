/- Lean-first (no Rocq counterpart).

`histEq(a, b)` (`examples/etcd/wal/ref.go`): whether two histories are equal.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

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
abbrev histEq.spec : Prop :=
  ∀ (sa sb : GoSlice) (ha hb : List TOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      opsRep sa ha ∗ opsRep sb hb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.histEq)) (Val #sa)) (Val #sb))
  {{ RET #(decide (ha = hb)); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
