/- Lean-first (no Rocq counterpart).

`opEq(a, b)` (`examples/etcd/wal/ref.go`): whether two operations are equal.
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
abbrev opEq.spec : Prop :=
  ∀ (va vb : walOp) (oa ob : TOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      opRep va oa ∗ opRep vb ob }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.opEq)) (Val #va)) (Val #vb))
  {{ RET #(decide (oa = ob)); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
