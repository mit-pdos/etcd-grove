/- Lean-first (no Rocq counterpart).

`contentsEq(a, b)` (`examples/etcd/wal/ref.go`): whether two read states are equal.
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
abbrev contentsEq.spec : Prop :=
  ∀ (va vb : contents) (ca cb : TContents),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      contentsRep va ca ∗ contentsRep vb cb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.contentsEq)) (Val #va)) (Val #vb))
  {{ RET #(decide (ca = cb)); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
