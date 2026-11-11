/- Lean-first (no Rocq counterpart).

`h.appendRev(st, chs)` (`examples/mvccfull/mvccfull.go`): the writer (`histW`, `History.lean`)
appends the revision `(M, chs)`: the state's map and the changes' slice, read-only from now on
(persistent points-tos, which the writer makes of its pending transaction's before the call); the
compactions unchanged.
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
abbrev history.appendRev.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hs : List HRev) (Cs : List w64) (m : GoMap)
    (M : GMap GoString kvRec) (c : GoSlice) (chs : List change),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ isHistory h γ ∗ histW γ Hs Cs ∗ m ↦$□ M ∗ c ↦*□ chs }}
    (App (App (h @!! go.GoType.PointerType history.ty @!! go!"appendRev") (Val #m)) (Val #c))
  {{ RET #(); histW γ (Hs ++ [(M, chs)]) Cs }}

end spec

end mvccfull
end EtcdGrove
end Perennial
