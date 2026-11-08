/- Lean-first (no Rocq counterpart).

`h.seen(floor, cur, what)` (`examples/mvccrand/mvccrand.go`): returns when a read at revision `cur`
is at least at its floor and at a revision the history has (`cur` below the length of a lower bound
`Hlb` the caller holds), with the thread's reader slot (`histRd`, `History.lean`; `snapshot`'s).
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
abbrev history.seen.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hlb : List HRev) (floor cur : w64) (what : GoString),
  sint.Z floor ≤ sint.Z cur → sint.Z cur < Hlb.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      histRd h γ ∗ monoListLbOwn γ.l Hlb }}
    (App (App (App (Val (h @!! go.GoType.PointerType history.ty @!! go!"seen")) (Val #floor))
      (Val #cur)) (Val #what))
  {{ RET #(); histRd h γ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
