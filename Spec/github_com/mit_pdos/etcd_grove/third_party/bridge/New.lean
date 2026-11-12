/-
`New(addr, l)` (`third_party/bridge/bridge.go`; `notes/client-cut-plan.md` K1): a trust-boundary spec, the
bridge's code is not verified (`Proof/github_com/mit_pdos/etcd_grove/third_party/bridge/Defs.lean`).
Lean-first (no Rocq counterpart).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **`New(addr, l)`**, `l` a listener bound at `a` (`net.Listen`'s, unused): it returns a bridge
to `addr`, not blackholed, and `a` reaches the server listening at `addr` (per-type stage B, B1b:
`grpcAddrIs`; until then two facts, `a` serves method by method and stream method by stream method
what `addr` serves); and (D29,
2026-10-21) `a` is refusal-free if `addr` is: the bridge relays bytes, so a status from `addr`
reaches the client unchanged, and a cut's (a blackhole's, a dropped connection's) errors are
grpc's own. The bridge relays bytes, so a call or stream on `a` is one on the server at `addr` (D32,
2026-10-21: grpc hands a stream's receiver only whole length-prefixed messages, in order, each
once, so each side receives a prefix of what the other sent, and a cut ends the stream with an
error); `a`'s own listener is consumed (`grpcAddrIs_agree` holds: no server listens at `a`). -/
abbrev New.spec : Prop :=
  ∀ (addr a : GoString) (l : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      netListenerAt l a }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.third_party.bridge.New)) (Val #addr))
      (Val #l))
  {{ (br : GoInterface), RET #br; ownBridge br addr false ∗
      □ (∀ γ : GName, grpcAddrIs addr γ -∗ grpcAddrIs a γ) ∗
      ⌜noRefusalAt addr → noRefusalAt a⌝ }}

end spec

end bridge
end EtcdGrove
end Perennial
