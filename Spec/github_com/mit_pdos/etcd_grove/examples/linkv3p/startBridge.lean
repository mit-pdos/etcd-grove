/-
`startBridge(addr, client)` (`examples/linkv3p/linkv3p.go`; `notes/client-cut-plan.md` K0/K3): a
listener at `addr` (`net.Listen`) and the bridge on it to `client` (`bridge.New`, a trust-boundary
spec: the bridge is part of the network, D26). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- **`startBridge(addr, client)`**, the address `addr` the program's (`netAddrFree`): it returns
either the bridge to `client` (owned, not blackholed) with `addr` serving what `client` serves
(`forwards`), or a non-nil error. -/
abbrev startBridge.spec : Prop :=
  ∀ (addr client : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      netAddrFree (GF := GF) addr }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.startBridge)) (Val #addr))
      (Val #client))
  {{ (br err : GoInterface), RET (PairV #br #err);
      ((⌜err = GoInterface.nil⌝ ∗ bridge.ownBridge br client false ∗ forwards addr client) ∨
        ⌜err ≠ GoInterface.nil⌝) }}

end spec

end linkv3p
end EtcdGrove
end Perennial
