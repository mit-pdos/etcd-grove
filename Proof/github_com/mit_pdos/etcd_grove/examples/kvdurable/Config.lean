/-
Lean-first (no Rocq counterpart).

# The replicas' raft configuration (2026-11-01, the cluster helpers; kvreconf's `Config.lean`)

`kdCfgOk id st applied cv`: `cv` is a configuration `Cluster.config(id, st, applied)` builds
(`Cluster__config.lean`): node `id` on the store's storage `st`, restarted at the applied index
`applied`, the store's `quietLogger`, valid (`ConfigValid`), with every other premise of raft's
`RestartNode.spec` on the configuration but `Applied`'s bound (`Cluster.start` chooses `applied`
within it). `qLogger_isLogger`: the store's `quietLogger{}` is a raft `Logger` (from its four
formatting methods' specs).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.QLogger
public import Proof.go_etcd_io.raft.v3.InvLogger
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.quietLogger__Debugf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.quietLogger__Errorf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.quietLogger__Infof
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.quietLogger__Warningf

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section cfg
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

/-- **A configuration of node `id` on the store's storage `st`, restarted at `applied`** (see the
file header): what `RestartNode.spec` asks of it, with its node id, storage, logger and applied
index. -/
def kdCfgOk (id : w64) (st : Loc) (applied : w64) (cv : Config) : Prop :=
  cv.ID' = id ∧ cv.Storage' = kdStorIface st ∧ cv.Logger' = GoInterface.ok qLogger ∧
  ConfigValid cv ∧ sint.Z cv.MaxInflightMsgs' < 2 ^ 62 ∧ cv.DisableProposalForwarding' = false ∧
  cv.ReadOnlyOption' = W64 0 ∧ cv.DisableConfChangeValidation' = false ∧
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) ∧
  cv.AsyncStorageWrites' = false ∧ cv.Applied' = applied

/-- `quietLogger{}` is a raft `Logger`. -/
theorem qLogger_isLogger
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    ⊢ isLogger (GF := GF) qLogger := by
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Infof format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Debugf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Warningf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Errorf format args) $$ [] HΦ
    itrivial

end cfg

end kvdurable
end EtcdGrove
end Perennial
