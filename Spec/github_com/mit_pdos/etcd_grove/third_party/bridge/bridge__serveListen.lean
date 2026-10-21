/-
`(*bridge).serveListen()` (`third_party/bridge/bridge.go`): the bridge's accept loop. Per accepted
connection, once the bridge is not paused (and unless it is stopped), it dials the bridge's
address, registers the pair and starts `serveConn` on it; when an accept or a dial fails, it
closes the listener and every registered connection and is `Done`. Lean-first (no Rocq
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

/-- **`b.serveListen()`**, the bridge's one accept loop (its receipt: the flag, `slRunning`), with
a thread token: it returns a thread token. -/
abbrev bridge.serveListen.spec : Prop :=
  ∀ (b : Loc) (γ : BridgeNames) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      isBridge b γ addr ∗ slRunning γ ∗ threadTok }}
    (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"serveListen")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end bridge
end EtcdGrove
end Perennial
