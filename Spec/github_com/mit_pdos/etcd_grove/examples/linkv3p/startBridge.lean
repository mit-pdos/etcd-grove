/-
`startBridge(addr, client)` (`examples/linkv3p/linkv3p.go`; `notes/client-cut-plan.md` K0/K3): a
listener at `addr` (`net.Listen`), given up to a relay to `client` (the forwarding fact
`grpc.relay`, `Proof/net/InvRelay.lean`), and the bridge on it (`bridge.New`). Lean-first (no Rocq
counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- **`startBridge(addr, client)`**, the address `addr` the program's (`netAddrFree`), with a
thread token: it returns the token and either the bridge to `client` (owned, not blackholed) with
`addr` serving what `client` serves (`forwards`), or a non-nil error. -/
abbrev startBridge.spec : Prop :=
  ∀ (addr client : GoString),
  threadBound GF + 1 ≤ 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      netAddrFree (GF := GF) addr ∗ threadTok }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.startBridge)) (Val #addr))
      (Val #client))
  {{ (br err : GoInterface), RET (PairV #br #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ bridgeP.ownBridge br client false ∗ forwards addr client) ∨
        ⌜err ≠ GoInterface.nil⌝) }}

end spec

end linkv3p
end EtcdGrove
end Perennial
