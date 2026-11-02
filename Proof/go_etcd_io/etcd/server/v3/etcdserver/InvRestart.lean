/-
**A member's stop and restart: the server's vocabulary, drafted** (the restart plan's R2a,
2026-11-02, `notes/restart-plan.md`). Lean-first (no Rocq counterpart).

R2a states what the example (`examples/restart3`) needs of the server at a stop and a restart, over
the predicates named here. Their content is the later sub-steps': each is an `opaque` placeholder
until then, so that no statement over them can be proved by unfolding them.

* `srvStopRight s γ id` (exclusive): the right to stop the server `s` of member `id` of the cluster
  `γ` once started (`HardStop`). R2b (the stopping server, the membership plan's M6): what
  `NewServer` gives its caller, with the "server open" token the request paths share.
* `srvDiskImage γ ρ id` (exclusive): member `id`'s data directory, as its last incarnation's stop
  left it, that incarnation's request names `ρ` recorded: raft's hard state, log and last snapshot
  record (the WAL), the backend's buckets at its consistent index, the member and cluster ids. R2c
  (L2): the ghost image handed from one incarnation to the next; graceful stops only (the plan's
  Q4). It holds what the restarted member's `NewServer` takes of the ghost state in place of a
  first start's `memberBoot` (`examples/common/Defs.lean`): the node API's restart token in place
  of `nodeBoot` (R2e, raft's restart from a durable state), the cluster's invariants at the
  recorded names. (R2c, 2026-11-02: no id state. A restart makes its incarnation's id share anew,
  at a fresh incarnation key, `idutil/Incarnations.lean`'s `idIncarnation_alloc`, with its new
  store's floor `srvFloorFact E₀'` as the key's claim facts; the ids' freshness across incarnations
  is the trusted `Next`'s assumption, `issues/etcd-request-id-restart-reuse.md`.) R2c and R2d split it between the image and
  `NewServer`'s restart premise. (2026-11-02, `Run`'s glue: until then a separate `srvRestartBoot`
  bundle the example supplied; the restarted member's own names, its wait registry and its store's
  index, are new, so the server allocates them, not the example.)
* `restartNames ρ ρ'` (pure, defined): the restarted incarnation's names `ρ'` agree with the stopped
  one's `ρ` on what the rest of the cluster and its clients see: raft's names, the KV state's ghost
  variable (`etcdKV`, the clients' invariants), the KV model of the committed log, the cluster's
  map of issued request ids and the member's id prefix. Its other names are its own. (Once the
  id state is keyed by incarnation, R2c, the agreement is on the cluster's id maps and the prefix,
  and the key is the one `idIncarnation_alloc` gives.)
* `bootstrapRestartContract cfg U γ id ctxs N dir`: `bootstrap`'s contract on a data directory that
  holds member `id`'s image (`bootstrapContract`'s restart case, L3): with the image, an error or
  the record of a restart (`bootOk`'s restart case). R2c.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The right to stop the started server `s`** (DRAFT, R2b; see the file header). -/
opaque srvStopRight (s : Loc) (γ : SrvRaft) (id : w64) : IProp GF

/-- **Member `id`'s data directory as its last stop left it, at that incarnation's request names
`ρ`** (DRAFT, R2c; see the file header). -/
opaque srvDiskImage (γ : SrvRaft) (ρ : ReqNames) (id : w64) : IProp GF

/-- **`bootstrap`'s contract on a stopped member's data directory** (DRAFT, R2c; see the file
header). -/
opaque bootstrapRestartContract [MemStorReg GF] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat)
    (dir : w64 → List GoString) : IProp GF

end defs

/-- **A restarted incarnation's names agree with the stopped one's where the cluster sees them**
(see the file header). -/
def restartNames [GooseExts] (ρ ρ' : ReqNames) : Prop :=
  ρ'.rd.raft = ρ.rd.raft ∧ ρ'.rd.kv.st = ρ.rd.kv.st ∧ kvModel ρ'.rd.kv = kvModel ρ.rd.kv ∧
    ρ'.ids.issued = ρ.ids.issued ∧ ρ'.ids.pfx = ρ.ids.pfx

end EtcdGrove
end Perennial
