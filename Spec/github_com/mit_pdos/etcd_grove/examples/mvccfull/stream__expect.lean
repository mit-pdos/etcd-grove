/- Lean-first (no Rocq counterpart).

`s.expect(w, upto)` (`examples/mvccfull/mvccfull.go`): the watcher's next expected change at or
after its position (`w.rev`, `w.index`: the `index`-th matching change of revision `rev`), up to
revision `upto` (`expRes`, over `expNext`, `WatchModel.lean`, for the watcher's `matchesM`: its range
and filter), read from the history through `s.x.h.changesAt` with the thread's reader slot, for a
lower bound `Hlb` of the history that has `upto`. The watcher's struct and its range's slices, and
the fields `s.x`, `x.h` are read only.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev stream.expect.spec : Prop :=
  ∀ (s x h : Loc) (γh : HistNames) (Hlb : List HRev) (w : Loc) (wv : watcher) (kk e : GoString)
    (upto : w64) (dqw dqk dqe : DFrac),
  0 ≤ sint.Z wv.rev' → 0 ≤ sint.Z wv.index' → sint.Z upto < Hlb.length →
  sint.Z upto < 2 ^ 63 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ sF go!"x" s ↦□ x ∗ rF go!"h" x ↦□ h ∗
      w ↦{dqw} wv ∗ wv.key' ↦*{dqk} kk ∗ wv.end' ↦*{dqe} e ∗ histRd h γh ∗ monoListLbOwn γh.l Hlb }}
    (App (App (s @!! go.GoType.PointerType stream.ty @!! go!"expect") (Val #w)) (Val #upto))
  {{ (ch : change) (r : w64) (ok : Bool), RET (PairV (PairV #ch #r) #ok);
      w ↦{dqw} wv ∗ wv.key' ↦*{dqk} kk ∗ wv.end' ↦*{dqe} e ∗ histRd h γh ∗
      ⌜expRes Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
        (sint.nat wv.index') (sint.Z upto) ch r ok⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
