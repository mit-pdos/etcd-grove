/- Lean-first (no Rocq counterpart).

`s.covered(w, p, what)` (`examples/mvccfull/mvccfull.go`): returns when the watcher has no expected
change left up to revision `p` (`expNext … p = none`, against a lower bound `Hlb` of the history
that has `p`); otherwise its check fails. The watcher's struct and slices are read only.
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
abbrev stream.covered.spec : Prop :=
  ∀ (s x h : Loc) (γh : HistNames) (Hlb : List HRev) (w : Loc) (wv : watcher) (kk e : GoString)
    (p : w64) (what : GoString) (dqw dqk dqe : DFrac),
  0 ≤ sint.Z wv.rev' → 0 ≤ sint.Z wv.index' → sint.Z p < Hlb.length → sint.Z p < 2 ^ 63 - 1 →
  expNext Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
    (sint.nat wv.index') (sint.Z p) = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ sF go!"x" s ↦□ x ∗ rF go!"h" x ↦□ h ∗
      w ↦{dqw} wv ∗ wv.key' ↦*{dqk} kk ∗ wv.end' ↦*{dqe} e ∗ histRd h γh ∗ monoListLbOwn γh.l Hlb }}
    (App (App (App (s @!! go.GoType.PointerType stream.ty @!! go!"covered") (Val #w)) (Val #p))
      (Val #what))
  {{ RET #(); w ↦{dqw} wv ∗ wv.key' ↦*{dqk} kk ∗ wv.end' ↦*{dqe} e ∗ histRd h γh }}

end spec

end mvccfull
end EtcdGrove
end Perennial
