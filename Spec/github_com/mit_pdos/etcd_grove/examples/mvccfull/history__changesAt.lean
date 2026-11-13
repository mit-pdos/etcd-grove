/- Lean-first (no Rocq counterpart).

`h.changesAt(r)` (`examples/mvccfull/mvccfull.go`): revision `r`'s changes, under the read lock,
with the thread's reader slot (`histRd`, `History.lean`): for a revision of a lower bound `Hlb` the
caller holds (so the check that `r` is in the history holds), a slice of its changes (persistent:
never changed once appended); mvccrand's.
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
abbrev history.changesAt.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hlb : List HRev) (r : w64),
  0 ≤ sint.Z r → sint.nat r < Hlb.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ histRd h γ ∗ monoListLbOwn γ.l Hlb }}
    (App (h @!! go.GoType.PointerType history.ty @!! go!"changesAt") (Val #r))
  {{ (s : GoSlice), RET #s; histRd h γ ∗
      ∃ chs : List change, s ↦*□ chs ∗ ⌜(Hlb[sint.nat r]?).map Prod.snd = some chs⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
