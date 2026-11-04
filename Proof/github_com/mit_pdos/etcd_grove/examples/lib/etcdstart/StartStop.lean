/-
**`s.Start()` of a member that will be stopped, or was restarted** (the restart plan's R2a and
R2b-2, 2026-11-02; DRAFT). Lean-first (no Rocq counterpart).

`Start_builtR_spec`: `wp_Start_built`'s triple (`Start.lean`) from a restarted member's built state
(`memberBuiltR`: the apply thread starting at its image's index, not `0`). A statement the restart's
proofs take as a hypothesis: `Start.spec` takes `ai₀ = 0`, and its generalization is R2d's.
(R2b-2) It also gives the right to stop the server (`srvStopRight`), as does `Start_builtS_spec`,
a first start's, from what `NewServer` kept for the stop (`srvStopKeep`). A restarted member's
right needs its `run` (R2d: `run.specStop` covers first starts only). When R2b-2's proof is done,
`Start.spec` gives the right and these collapse into it (one spec per function).
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
          memberBuiltR s ρ E₀ lg γn id N sv ∗ srvDataDir s dd ∗ srvStopKeep s ∗ threadTok }}
        (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
      {{ RET #(); memberUp s ρ E₀ lg γn id ∗ srvStopRight s ρ.rd.raft.raft ρ id dd }}

/-- (DRAFT, R2b-2, 2026-11-02) **`Start` of a first start, with the right to stop**:
`wp_Start_built`'s triple, with the server's data directory `dd` recorded (`srvDataDir`,
`BuildServer.specStop`'s), giving also the right to stop the server (`srvStopRight`, at its raft
names `ρ.rd.raft.raft` and request names `ρ`): `start` makes `stop` and `done`, the latter
announcing the image escrowed for the right's claim. A statement `restart3`'s proofs take as a
hypothesis until R2b-2's proof (`start` allocating the escrow, `run`'s shutdown filling it). -/
def Start_builtS_spec : Prop :=
  ∀ (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (dd : GoString) [ReceiptBoundLe GF (N + 1)],
    ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
          memberBuilt s ρ E₀ lg γn id N sv ∗ srvDataDir s dd ∗ srvStopKeep s ∗ threadTok }}
        (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
      {{ RET #(); memberUp s ρ E₀ lg γn id ∗ srvStopRight s ρ.rd.raft.raft ρ id dd }}

end defs

end etcdstart
end EtcdGrove
end Perennial
