/- Lean-first (no Rocq counterpart).

`h.snapshot()` (`examples/mvccfull/mvccfull.go`): the states so far, under the read lock, with the
thread's reader slot (`histRd`, `History.lean`): a slice of the states' maps (persistent: a state is
never changed once appended), of revisions `Hs` extending any lower bound `Hlb` the caller held, and
a lower bound of them (mvccrand's).
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
abbrev history.snapshot.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hlb : List HRev),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ histRd h γ ∗ monoListLbOwn γ.l Hlb }}
    (App (h @!! go.GoType.PointerType history.ty @!! go!"snapshot") (Val #()))
  {{ (s : GoSlice), RET #s; histRd h γ ∗
      ∃ (ms : List GoMap) (Hs : List HRev), ⌜Hlb <+: Hs ∧ 2 ≤ Hs.length⌝ ∗ ⌜s.cap = s.len⌝ ∗
        monoListLbOwn γ.l Hs ∗ s ↦*□ ms ∗ statesP ms Hs }}

end spec

end mvccfull
end EtcdGrove
end Perennial
