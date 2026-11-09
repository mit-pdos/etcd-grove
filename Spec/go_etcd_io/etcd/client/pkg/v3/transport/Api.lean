/-
# `client/pkg/v3/transport` (batch 1c)

* `errStrOk err` (persistent; slot of the error's package): `err` is a non-`nil` error whose
  `Error()` returns a string without panicking.
* `tlsCfgOk tls` (persistent; slot of `crypto/tls` and grpc's credentials, 2a): a `*tls.Config`
  the client may use read-only (grpc's `credentials.NewTLS` clones it). `TLSInfo.ClientConfig`
  produces it.
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.transport
public import Spec.PkgInit.go_etcd_io.etcd.client.pkg.v3.transport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Transport

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An error whose `Error()` is safe** (persistent). -/
opaque errStrOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) : IProp GF := iprop(True)

def errStrOk_persistent.spec : Prop := ∀ err, Persistent (errStrOk (GF := GF) err)

/-- **A `*tls.Config` the client may use read-only** (persistent). -/
opaque tlsCfgOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tls : Loc) : IProp GF := iprop(True)

def tlsCfgOk_persistent.spec : Prop := ∀ tls, Persistent (tlsCfgOk (GF := GF) tls)

end res

end Transport
end EtcdGrove
end Perennial
