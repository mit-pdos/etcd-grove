/-
`client.NodeMain(w, c, addr, eps)`: client machine `c` of workload `w`, at `addr`, the members' client
endpoints `eps`.
- `NodeMain.spec` (F8, `notes/etcd-dist-plan.md` §27.3): **every arm**, from the client machine's share
  `wlNodeShare w c addr eps` (`client/Shares.lean`; its kv and writer arms at `Rotate(eps, c)`, its auth arm at
  `eps`, still `False`: F7 S13), its level token, and the pure facts the dispatch and the boot give (`wlPure w`: the client
  count's bound; at most 64 endpoints; the endpoints plain; `nodeMachinePure`). kv: `kvremote.Node`; watch,
  cache: the writer (`NodeMainWatch.spec`); auth: reached with a `False` share (D2); the other kinds have no
  client machine (it returns).
- `NodeMain.specKv` (M1): **the kv arm only**: of a `kv` workload, when `c` is one of its
  client machines and `eps` is not empty, `kvremote.Node(c, addr, Rotate(eps, c))`; otherwise it returns.
Proved for any precondition `NP` of `Node`. `Rotate`'s index
arithmetic needs `c + len(eps)` within `int`, for a `c` that passes the guard (`0 ≤ c < clients`): the
premise (a well-formed deployment's client count is below `2 ^ 31`, its members at most 64).
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Shares
@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

/-- Of a `kv` workload, from `Node`'s precondition at `c`, `addr` and the rotated endpoints, `NodeMain`
does not panic. -/
abbrev NodeMain.specKv (NP : w64 → GoString → List GoString → IProp GF) : Prop :=
  ∀ (w : Workload) (c : w64) (addr : GoString) (eps : GoSlice) (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜w.kind = W64 0 ∧
        (0 ≤ sint.Z c → sint.Z c < sint.Z w.clients → sint.Z c + epsL.length ≤ 2 ^ 63)⌝ ∗ eps ↦*□ epsL ∗ NP c addr (rotateL epsL (sint.nat c)) }}
    (App (App (App (App (Val (@! client.NodeMain)) (Val #w.val)) (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

section specFull
open Net client etcd_dist_client
open github_com.mit_pdos.etcd_grove.examples.lib.remote

variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]


/-- **The machine-level pure facts** a client machine's arms take, which its boot discharges: a watch
environment (its client's `newClient`), the logic's thread bound, and `EtcdError` an `errors.As` target. -/
abbrev nodeMachinePure : Prop :=
  Nonempty (WEnv GF) ∧ threadBound GF ≤ 2 ^ 30 ∧ errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty

/-- Of any workload, from client machine `c`'s share at the members' endpoints (`wlNodeShare` rotates them where its
arm needs it; F7 S13), its level token and the pure facts, `NodeMain` does not panic (see the file header). -/
abbrev NodeMain.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (w : Workload) (c : w64) (addr : GoString) (eps : GoSlice)
    (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜wlPure w ∧ epsL.length ≤ 64 ∧ plainEndpoints epsL ∧ nodeMachinePure (GF := GF)⌝ ∗
      levelTok 0 ∗ eps ↦*□ epsL ∗
      wlNodeShare (Gg := hG.goose_globalGS) w c addr epsL }}
    (App (App (App (App (Val (@! client.NodeMain)) (Val #w.val)) (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end specFull

end etcd_dist
end EtcdGrove
end Perennial
