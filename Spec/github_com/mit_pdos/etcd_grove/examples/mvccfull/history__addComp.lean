/- Lean-first (no Rocq counterpart).

`h.addComp(c)` (`examples/mvccfull/mvccfull.go`): the writer (`histW`, `History.lean`) appends
the compaction revision `c` to the history's compactions, under the write lock.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.History

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev history.addComp.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hs : List HRev) (Cs : List w64) (c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ isHistory h γ ∗ histW γ Hs Cs }}
    (App (h @!! go.GoType.PointerType history.ty @!! go!"addComp") (Val #c))
  {{ RET #(); histW γ Hs (Cs ++ [c]) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
