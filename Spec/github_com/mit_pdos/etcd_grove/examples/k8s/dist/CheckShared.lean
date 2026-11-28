/-
Lean-first (no Rocq counterpart).

# `CheckShared(seeded, revs, ops, timeout)` (`examples/k8s/dist/store.go`; k8s-dist K9 step 5,
`notes/k8s-dist-k9.md` §2.9)

The store history `ops` checked against `SharedModel` in the lazy, eager and full modes in turn, each
with porcupine's `CheckOperationsTimeout`, until one does not answer `Illegal` or the full mode has.
**The triple**: from the seeded store `g0` and history that `seeded` holds, the revisions `R` that `revs`
holds (as `Seeded.SharedModel.spec` takes them: `g0` well formed, its revision and `R`'s below `2^62`,
its items below `2^61`), the history read-only and well formed (`HistOk`), and every operation a boxed
input and output naming revisions below `2^62` (`RevsBelow`, `sharedS`'s `ioOk`), `CheckShared` returns
a verdict and a mode; an `Illegal` verdict is the full mode's (mode 2), and then no linearization of
`ops` is accepted by the full mode's sequential model (`sharedM g0 R 2`). That is all a caller needs:
K12 shows the full mode accepts the history (`searchRun_accepts`), so the verdict is not `Illegal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seeded__SharedModel
public import Spec.github_com.anishathalye.porcupine.CheckOperationsTimeout
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev CheckShared.spec : Prop :=
  ∀ [github_com.mit_pdos.etcd_grove.examples.k8s.dist.Assumptions]
    (s : Seeded) (hs : List mstore) (g0 : HSt) (r : Revs) (R : RevsL) (sl : GoSlice)
    (ops : List github_com.anishathalye.porcupine.Operation) (dur : w64),
  HWf g0 → uint.nat g0.st.rv ≤ 2 ^ 62 → g0.st.items.length < 2 ^ 61 → RevsLBelow R →
  github_com.anishathalye.porcupine.HistOk ops →
  (∀ o ∈ ops, ∃ x y, o.Input' = boxIn x ∧ o.Output' = boxOut y ∧ RevsBelow x y) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.dist ∗
      context.isClosedchanInit ∗
      storeOwn s.st0' g0.st ∗ s.h0' ↦*□ hs ∗ ([∗list] x;g ∈ hs;g0.hist, storeOwn x g) ∗
      revsOwn r R ∗ sl ↦*□ ops }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.dist.CheckShared))
      (Val #s)) (Val #r)) (Val #sl)) (Val #dur))
  {{ (res : GoString) (mode : w64), RET (PairV #res #mode);
      ⌜res = go!"Illegal" → mode = W64 2 ∧
        ¬ github_com.anishathalye.porcupine.Theory.Linearizable (sharedM g0 R 2)
          (github_com.anishathalye.porcupine.histOf ops)⌝ }}

end spec

end k8s_dist
end EtcdGrove
end Perennial
