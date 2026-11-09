/- Lean-first (no Rocq counterpart).

`c.expect(w, upto)` (`examples/mvccrand/mvccrand.go`): the next change in the watcher's range at or
after its position (`w.rev`, `w.index`: the `index`-th in-range change of revision `rev`), up to
revision `upto` (`expRes`, over `expNext`, `WatchModel.lean`), read from the history through
`changesAt` with the thread's reader slot, for a lower bound `Hlb` of the history's revisions that
has `upto` (so `changesAt`'s check holds). Under the position invariant (`posOk`, `WatchModel.lean`),
it is the watcher's next expected change (`expNext_eq_get`). The watcher's struct, its range's
slices and the struct's `h` field are read only.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WatchModel

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
abbrev watchCheck.expect.spec : Prop :=
  ∀ (c h : Loc) (γ : HistNames) (Hlb : List HRev) (w : Loc) (wv : watcher) (kk e : GoString)
    (upto : w64) (dq dqw dqk dqe : DFrac),
  0 ≤ sint.Z wv.rev' → 0 ≤ sint.Z wv.index' → sint.Z upto < Hlb.length →
  sint.Z upto < 2 ^ 63 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      structFieldRef watchCheck go!"h" c ↦{dq} h ∗ w ↦{dqw} wv ∗
      wv.key' ↦*{dqk} kk ∗ wv.end' ↦*{dqe} e ∗ histRd h γ ∗ monoListLbOwn γ.l Hlb }}
    (App (App (Val (c @!! go.GoType.PointerType watchCheck.ty @!! go!"expect")) (Val #w))
      (Val #upto))
  {{ (ch : change) (r : w64) (ok : Bool), RET (PairV (PairV #ch #r) #ok);
      structFieldRef watchCheck go!"h" c ↦{dq} h ∗ w ↦{dqw} wv ∗
      wv.key' ↦*{dqk} kk ∗ wv.end' ↦*{dqe} e ∗ histRd h γ ∗
      ⌜expRes Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
        (sint.nat wv.index') (sint.Z upto) ch r ok⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
