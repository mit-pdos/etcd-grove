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

/-- **`New(addr, l)`**, `l` a listener bound at `a` (`net.Listen`'s, unused), where `a` and `addr`
serve one service table `Svc` (`grpcAddrAt`): it returns a bridge to `addr`, not blackholed; and `a`
is refusal-free if `addr` is: the bridge relays bytes, so a
status from `addr` reaches the client unchanged, and a cut's (a blackhole's, a dropped connection's)
errors are grpc's own. The bridge relays bytes, so a call or stream on `a` is one on the server at
`addr` (grpc hands a stream's receiver only whole length-prefixed messages, in order,
each once, so each side receives a prefix of what the other sent, and a cut ends the stream with an
error); both addresses run grpc's protocols for the same table, so what a client of `a` writes meets
`addr`'s dialer protocol and what `addr`'s server writes meets `a`'s acceptor protocol. `a`'s own
listener is consumed (no server listens at `a`).

The bridge's address serves its target's table: the caller sets `a`'s table to
the target's `Svc` from what `Listen` left (`netAddrLeft a`, spent by `grpc_addr_set` or
`addr_set_proto_tok`), and registrations at `a` are read off `a`'s table, as at any address. Whoever bridges `a` has spent
what sets `a`'s protocols, and set them to the target's table: a program that listened at `a`, set
`a`'s grpc table at specs of its choosing and bridged `a` to a server meeting none of them
(`notes/audit.md`, "`bridge.New` and `netAddrLeft`") cannot meet this precondition, which asks for one
`Svc` at both addresses. -/
abbrev New.spec : Prop :=
  ∀ (addr a : GoString) (l : GoInterface) (Svc : GrpcSvc GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      netListenerAt l a ∗
      (∃ (_ : HasExt Net.netExt) (π : Net.NetProtoGS) (σ : Net.NetSlotGS),
        grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) a Svc ∗
        grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr Svc) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.third_party.bridge.New)) (Val #addr))
      (Val #l))
  {{ (br : GoInterface), RET #br; ownBridge br addr false ∗ ⌜noRefusalAt addr → noRefusalAt a⌝ }}

end spec

end bridge
end EtcdGrove
end Perennial
