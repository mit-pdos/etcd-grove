/-
**A member's stop and restart: the server's vocabulary, drafted** (the restart plan's R2a,
2026-11-02, `notes/restart-plan.md`). Lean-first (no Rocq counterpart).

R2a states what the example (`examples/restart3`) needs of the server at a stop and a restart, over
three predicates named here. Their content is the later sub-steps': each is an `opaque` placeholder
until then, so that no statement over them can be proved by unfolding them.

* `srvStopRight s γ id` (exclusive): the right to stop the server `s` of member `id` of the cluster
  `γ` once started (`HardStop`). R2b (the stopping server, the membership plan's M6): what
  `NewServer` gives its caller, with the "server open" token the request paths share.
* `srvStartRet s` (pure): `s.Start()` returned. `HardStop` of a server never started blocks forever
  (it sends on `s.stop`, which only `run` receives); R2b.
* `srvDiskImage γ id` (exclusive): member `id`'s data directory, as its last incarnation's stop left
  it: raft's hard state, log and last snapshot record (the WAL), the backend's buckets at its
  consistent index, the member and cluster ids. R2c (L2): the ghost image handed from one
  incarnation to the next; graceful stops only (the plan's Q4).
* `srvRestartBoot γ ctxs ρ E₀ Φs id` (exclusive): what the restarted member's `NewServer` takes of
  the ghost state in place of a first start's `memberBoot` (`examples/common/Defs.lean`): the node
  API's restart token in place of `nodeBoot` (R2e, raft's restart from a durable state), the
  member's new request names, and the id generator's freshness across the restart
  (`issues/etcd-request-id-restart-reuse.md`). R2c and R2d.
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

/-- **`s.Start()` returned** (DRAFT, R2b; see the file header). -/
opaque srvStartRet (s : Loc) : Prop

/-- **Member `id`'s data directory as its last stop left it** (DRAFT, R2c; see the file header). -/
opaque srvDiskImage (γ : SrvRaft) (id : w64) : IProp GF

/-- **The restarted member's boot bundle** (DRAFT, R2c and R2d; see the file header). -/
opaque srvRestartBoot (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) : IProp GF

/-- **`bootstrap`'s contract on a stopped member's data directory** (DRAFT, R2c; see the file
header). -/
opaque bootstrapRestartContract [MemStorReg GF] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat)
    (dir : w64 → List GoString) : IProp GF

end defs

end EtcdGrove
end Perennial
