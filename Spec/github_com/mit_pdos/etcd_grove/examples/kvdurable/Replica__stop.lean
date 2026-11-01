/- Lean-first (no Rocq counterpart).

`r.stop()` (kv.go): `stopc` closed; `runDone`, `tickDone`, `snapDone` received (the loop's and the
snapshotter's halves of `nodeRunning` with the first and the last), then `node.Stop`, which gives
the id's slot back (`nodeVacant`, 2026-11-01, durability layer 4: the restarter's). It takes the
stopper's share only (`repStopper`; `crash`, which calls it, has given the crasher's token to `dmu`).
It gives back `run`'s claim on its batch, received with `runDone` (2026-11-01, G6: `crash` leaves it
in `dmu` in place of the writer it takes out, once `run` has returned).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.stop.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc),
  {{ repStopper γ vs dir id r }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"stop")) (Val #()))
  {{ RET #(); nodeVacant γ.r.cluster id ∗
      ∃ (n st sts sq : Loc) (ρ : KdRepNames), isReplicaR γ vs dir id r n st sts sq ρ ∗
        ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v }}

end spec

end kvdurable
end EtcdGrove
end Perennial
