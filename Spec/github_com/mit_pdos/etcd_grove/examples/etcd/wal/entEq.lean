/- Lean-first (no Rocq counterpart).

`entEq(a, b)` (`examples/etcd/wal/ref.go`): whether the entries are equal.
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
abbrev entEq.spec : Prop :=
  ∀ (a b : TEnt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.entEq)) (Val #a)) (Val #b))
  {{ RET #(decide (a = b)); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
