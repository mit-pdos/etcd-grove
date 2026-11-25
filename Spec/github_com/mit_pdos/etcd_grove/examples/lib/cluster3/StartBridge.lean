/-
`StartBridge(addr, client)` (`examples/lib/cluster3/cluster3.go`, until 2026-11-05 package `partition`'s; `notes/client-cut-plan.md` K0/K3): a
listener at `addr` (`net.Listen`) and the bridge on it to `client` (`bridge.New`, a trust-boundary
spec: the bridge is part of the network, D26). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- **`StartBridge(addr, client)`**, the address `addr` the program's (`netAddrFree`), `client` serving
a single-process start's table with `P` at every address of that table (`etcdstart.tableAt`): it
returns either the bridge to `client` (owned, not blackholed) with `addr` serving `P` (its table set to
`client`'s, `bridge.New`) and refusal-free if `client` is, or a non-nil error. (Phase 7's switch, SW1,
2026-11-24: until then it gave `forwards addr client`, the bridge's address reaching the server at
`client`, which `bridge.New`'s spec no longer gives: a registration is read off the dialed address's
own table, so a bridge serves what is stated relative to its target's table.) -/
abbrev StartBridge.spec : Prop :=
  ∀ (addr client : GoString) (P : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 ∗
      netAddrFree (GF := GF) addr ∗ etcdstart.tableAt client P }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartBridge)) (Val #addr))
      (Val #client))
  {{ (br err : GoInterface), RET (PairV #br #err);
      ((⌜err = GoInterface.nil⌝ ∗ bridge.ownBridge br client false ∗ P addr ∗
          ⌜noRefusalAt client → noRefusalAt addr⌝) ∨
        ⌜err ≠ GoInterface.nil⌝) }}

end spec

end cluster3
end EtcdGrove
end Perennial
