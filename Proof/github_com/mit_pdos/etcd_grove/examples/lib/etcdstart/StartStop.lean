/-
**`s.Start()` of a member that will be stopped, or was restarted** (the restart plan's R2a and
R2b-2, 2026-11-02; DRAFT). Lean-first (no Rocq counterpart).

`Start_builtR_spec`: `wp_Start_built`'s triple (`Start.lean`) from a restarted member's built state
(`memberBuiltR`: the apply thread starting at its image's index, not `0`). A statement the restart's
proofs take as a hypothesis: `Start.spec` takes `ai₀ = 0`, and its generalization is R2d's.
(R2b-2) It also gives the right to stop the server (`srvStopRight`): R2c-4, inside `memberUp`, as
a first start's (`wp_Start_built`, from `Start.spec`; `Start_builtS_spec`, the draft hypothesis it
replaces, deleted). A restarted member's right needs its `run` (R2d: `run.spec` covers first starts
only); then this collapses into `wp_Start_built` (one spec per function).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
def Start_builtR_spec : Prop :=
  ∀ (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (dd : GoString) [ReceiptBoundLe GF (N + 1)],
    ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
          memberBuiltR s ρ E₀ lg γn id N sv ∗ srvDataDir s dd ∗
          (∃ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (E : apply.AEnv GF)
            (γrn : RNNames) (γk : GName), srvStop.keep s cfg E γrn γk) ∗ threadTok }}
        (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
      {{ RET #(); memberUp s ρ E₀ lg γn id }}

end defs

end etcdstart
end EtcdGrove
end Perennial
