/-
`New(addr, l)` (`third_party/bridge/dialer.go`): a bridge on the listener `l` to the TCP address
`addr` (`newBridge` with etcd's `dialer`), as the `Bridge` interface. Lean-first (no Rocq
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

/-- **`New(addr, l)`**, `l` a relay's listener to `addr`, with a thread token (the bound on live
goroutines a premise): it returns a bridge to `addr`, not blackholed, and the thread token. -/
abbrev New.spec : Prop :=
  ∀ (addr : GoString) (l : GoInterfaceOk),
  threadBound GF + 1 ≤ 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      relayListener l addr ∗ threadTok }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.third_party.bridge.New)) (Val #addr))
      (Val #(interface.ok l : GoInterface)))
  {{ (br : GoInterface), RET #br; ownBridge br addr false ∗ threadTok }}

end spec

end bridge
end EtcdGrove
end Perennial
