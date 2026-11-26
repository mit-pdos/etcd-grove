/-
`client.MainReady(w, eps, nodes, ready)`: workload `w`'s orchestrator, against the members' client
endpoints `eps` and its client machines `nodes` (Lean-first, no Rocq counterpart).

- `MainReady.spec` (F8, `notes/etcd-dist-plan.md` §27.3): **every arm**. From the orchestrator's share
  `wlShare w epsL ns` (`client/Shares.lean`), the machine's thread token (`RunCache` takes it whole, every other
  arm its level-`0` token), and the pure facts the dispatch and the boot give (`wlPure w`: the workload's bounds;
  plain endpoints; a watch environment; the thread and receipt bounds (`RunWatch`, `RunCache`: `GenAll`'s receipts); `EtcdError` an `errors.As` target),
  `MainReady` does not panic. The `auth` and `authLease` arms are reached with a `False` share (D2).
- `MainReady.specKv` (N7-kv, M1, `notes/etcd-dist-n7kv.md`): **the kv arm only**, for any precondition `OP` of
  `Orch`: of a `kv` workload (kind 0) the switch reaches `RunKV` alone. M1's `etcd_kv_safe_nocrash` uses it.
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

/-- Of a `kv` workload, from `Orch`'s precondition at `nodes` and `w.ops`, `MainReady` does not panic. -/
abbrev MainReady.specKv (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (w : Workload) (eps nodes : GoSlice) (ns : List GoString) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜w.kind = W64 0⌝ ∗ nodes ↦*□ ns ∗ readySpec ready ∗ OP ns w.ops }}
    (App (App (App (App (Val (@! client.MainReady)) (Val #w.val)) (Val #eps)) (Val #nodes)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

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


/-- **The machine-level pure facts** the orchestrator's arms take, which its boot discharges: a watch
environment (the clients' `newClient`), the logic's thread and receipt bounds, and `EtcdError` an `errors.As`
target. -/
abbrev orchMachinePure : Prop :=
  Nonempty (WEnv GF) ∧ threadBound GF ≤ 2 ^ 30 ∧ receiptBound GF ≤ 2 ^ 56 ∧
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty

/-- Of any workload, from its orchestrator share, `MainReady` does not panic (see the file header). -/
abbrev MainReady.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (w : Workload) (eps nodes : GoSlice) (epsL ns : List GoString)
    (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜wlPure w ∧ plainEndpoints epsL ∧ orchMachinePure (GF := GF)⌝ ∗ threadTok ∗ eps ↦*□ epsL ∗ nodes ↦*□ ns ∗
      readySpec ready ∗ wlShare (Gg := hG.goose_globalGS) w epsL ns }}
    (App (App (App (App (Val (@! client.MainReady)) (Val #w.val)) (Val #eps)) (Val #nodes)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

end specFull

end etcd_dist
end EtcdGrove
end Perennial
