/- Lean-first (no Rocq counterpart).

`h.snapshot()` (`examples/mvccrand/mvccrand.go`): the states so far, under the read lock, with the
thread's reader slot (`histRd`, `History.lean`): a slice of the states' maps (persistent: a state is
never changed once appended), of revisions `Hs` extending any lower bound `Hlb` the caller held, and
a lower bound of them. (The writer, which knows the revisions exactly, `histW γ Hs'`, passes
`Hlb := Hs'` and gets `Hs = Hs'` back from its own half: `histW_lb`, `mono_list_auth_lb_valid`.)
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
abbrev history.snapshot.spec : Prop :=
  ∀ (h : Loc) (γ : HistNames) (Hlb : List HRev),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      histRd h γ ∗ monoListLbOwn γ.l Hlb }}
    (App (Val (h @!! go.GoType.PointerType history.ty @!! go!"snapshot")) (Val #()))
  {{ (s : GoSlice), RET #s; histRd h γ ∗
      ∃ (ms : List GoMap) (Hs : List HRev), ⌜Hlb <+: Hs ∧ 2 ≤ Hs.length⌝ ∗
        monoListLbOwn γ.l Hs ∗ s ↦*□ ms ∗ statesP ms Hs }}

end spec

end mvccrand
end EtcdGrove
end Perennial
