/-
`(*bridge).serveConn(bc)` (`third_party/bridge/bridge.go`): copies the connection's bytes both ways
in two goroutines until both stop, then closes `donec`, closes the connection, removes it from
the map and is `Done`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI github_com.mit_pdos.etcd_grove.third_party

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **`b.serveConn(c)`**, the goroutine of a connection `serveListen` registered (the registry's
entry `(q, γt)`; the receipt of its `Add`), with the closer's view of its `donec`, its share `q`
of `b.blackholec` (at the channel `ch`), and the two directions of the bridged connection,
nothing read or written yet: it returns a thread token (its `Done`'s). -/
abbrev bridge.serveConn.spec : Prop :=
  ∀ (b : Loc) (γ : BridgeNames) (addr : GoString) (c : Loc) (q : Qp) (γt : GName)
    (lo inc outc : GoInterfaceOk) (donec : GoChan) (γd : ChanNames) (ch : GoChan)
    (γbh : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      isBridge b γ addr ∗ wgRunning γ ∗ connFields c inc outc donec ∗ netConnOk inc ∗
      netConnOk outc ∗ ownBroadcastChan donec γd (doneQ b q γt) .Pending ∗ c ↪[γ.reg]□ (q, γt) ∗
      bF b go!"blackholec" ↦{DFrac.own q} ch ∗ ownBroadcastChan ch γbh iprop(True) .Unknown ∗
      relayDir lo inc outc [] [] ∗ relayDir lo outc inc [] [] }}
    (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"serveConn")) (Val #c))
  {{ RET #(); threadTok }}

end spec

end bridgeP
end EtcdGrove
end Perennial
