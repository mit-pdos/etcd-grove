/-
Lean-first (no Rocq counterpart). #33 parity B1: **the driver's `&nodeLogger{n}` meets raft's
`Logger` contract** (`isLogger`, `InvLogger.lean`), from its methods' specs: `Infof` its own
(`nodeLogger.Infof.spec`, the count in `antLogN`), `Debugf`/`Warningf`/`Errorf` promoted from the
embedded `quietLogger` (through `&l.quietLogger`, a load of the field: its points-to read-only).
S4's `antLogger_isLogger` (`git show a90d8f9735:…/antithesis/RunCluster.lean`) is the template.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger__Infof
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger__Debugf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger__Warningf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger__Errorf
public import Proof.go_etcd_io.raft.v3.InvLogger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **`&nodeLogger{n}` is a `Logger`** (raft's `isLogger`): its formatting methods return. -/
theorem nodeLogger_isLogger
    (wp_Infof : nodeLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (l n : Loc) (ql : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis -∗
      l.[H.nodeLogger, go!"quietLogger"] ↦□ ql -∗ l.[H.nodeLogger, go!"n"] ↦□ n -∗
      inv antLogN (∃ k : w64, n.[H.node, go!"autoLeft"] ↦ k) -∗
      isLogger (GF := GF)
        ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger.ty, #l⟩ := by
  iintro #Hpkg #Hq #Hn #Hinv
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl
  · dsimp only
    imodintro
    iintro %Φ - HΦ
    wp_apply wp_Infof l n format args $$ [$Hpkg $Hn $Hinv]
    iapply HΦ
    itrivial
  all_goals
    dsimp only
    imodintro
    iintro %Φ - HΦ
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    first
      | wp_apply wp_Debugf ql format args $$ [$Hpkg]
      | wp_apply wp_Warningf ql format args $$ [$Hpkg]
      | wp_apply wp_Errorf ql format args $$ [$Hpkg]
    iapply HΦ
    itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
