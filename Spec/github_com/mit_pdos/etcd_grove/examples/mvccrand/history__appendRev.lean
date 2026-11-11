/- Lean-first (no Rocq counterpart).

`h.appendRev(st, chs)` (`examples/mvccrand/mvccrand.go`): the writer (`histW`, `History.lean`)
appends the revision `(M, chs)`: the state's map and the changes' slice, read-only from now on
(persistent points-tos, which the writer makes of its pending transaction's before the call).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.History

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev history.appendRev.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hs : List HRev) (m : GoMap) (M : GMap GoString kvRec)
    (c : GoSlice) (chs : List change),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      isHistory h γ ∗ histW γ Hs ∗ m ↦$□ M ∗ c ↦*□ chs }}
    (App (App (Val (h @!! go.GoType.PointerType history.ty @!! go!"appendRev")) (Val #m)) (Val #c))
  {{ RET #(); histW γ (Hs ++ [(M, chs)]) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
