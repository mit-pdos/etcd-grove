/-
`newBridge(dialer, listener)` (`third_party/bridge/bridge.go`): makes the bridge (its map and
channels, `pausec` closed: not paused) and starts its accept loop. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI github_com.mit_pdos.etcd_grove.third_party

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **`newBridge(d, l)`**, `d` a TCP dialer to `addr` and `l` a relay's listener to `addr`, with a
thread token (the bound on live goroutines a premise): it returns a bridge to `addr`, not
blackholed, and the thread token. -/
abbrev newBridge.spec : Prop :=
  ∀ (addr : GoString) (l : GoInterfaceOk),
  threadBound GF + 1 ≤ 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      relayListener l addr ∗ threadTok }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.third_party.bridge.newBridge))
      (Val #(interface.mkOk bridge.dialer.ty #(bridge.dialer.mk go!"tcp" addr) : GoInterface)))
      (Val #(interface.ok l : GoInterface)))
  {{ (b : Loc), RET #b; ∃ γ : BridgeNames, isBridge b γ addr ∗ bridgeHoled γ false ∗ threadTok }}

end spec

end bridge
end EtcdGrove
end Perennial
