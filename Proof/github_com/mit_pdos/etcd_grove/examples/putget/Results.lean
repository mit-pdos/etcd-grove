/-
The adequacy example's results (`examples/putget/putget.go`; item 9), with the trust base of
each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`putget_Main`** (stage 2, 2026-10-18): `Main` -- one etcd member started in process
  (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23790`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), a `Put` of `k` with value `v`, a
  `Get` of `k`, and a panic unless the `Get` returned `v` -- returns: it does not panic. From
  `isPkgInit putget`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`putget.premises`, `BootFacts`, the bounds and the workload premises:
  `Spec/github_com/mit_pdos/etcd_grove/examples/putget/Main.lean`).

`Main`'s callees are linked here, by hand: `putget.Main.wp_proof` applied to their linked results
in the server's, v3rpc's and the client's `Link.lean`s (each in a namespace of its own) and to the
trust-boundary axioms of `zap.NewNop`, `features.NewDefaultServerFeatureGate`, `net.Listen` and
`(*grpc.Server).Serve`, which no `Link.lean` links yet. `etc/gen-link.py` has no mode combining
several packages' Links (each mode links one package, with `@` callees of the Links it imports
under one namespace); a `--putget` mode is the follow-up if more of the example is linked.

**The closed theorem** (stage 3) is not stated: besides `v3rpc.eofVar` (`io.EOF`, for the proposed
Perennial `io` change), five of `Main`'s premises are not of the kinds a closed theorem may assume
(D19a), two of them false of Go as stated (`notes/decisions.md`, D19r).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Main
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Proof.net.Listen
public import Proof.google_golang_org.grpc.Server__Serve
public import Perennial.Proof.context.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget.Assumptions]

/-- **The adequacy example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/putget/Main.lean`), under the semantic premises of
its callees' linked results: `int64(f)` of a `float64` (`Float64ToInt64Semantics`, the server's)
and the client's `dialWithBalancer` body (`DialWithBalancerBody`). -/
theorem putget_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    putget.Main.spec (GF := GF) (hG := hG) :=
  putget.Main.wp_proof zap.NewNop.wp_proof features.NewDefaultServerFeatureGate.wp_proof
    wp_NewServer EtcdServer.wp_Start v3rpc.wp_Server net.Listen.wp_proof
    grpc.Server.Serve.wp_proof client.v3.clientv3.wp_New context.wp_Background

end results

#print axioms putget_Main

end EtcdGrove
end Perennial
