/-
# `client/pkg/v3/transport` (batch 1c)

* `errStrOk err` (persistent; slot of the error's package): `err` is a non-`nil` error whose
  `Error()` returns a string without panicking.
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
opaque errStrOk (err : GoInterface) : IProp GF := iprop(True)

def errStrOk_persistent.spec : Prop := ∀ err, Persistent (errStrOk (GF := GF) err)

end res

end Transport
end EtcdGrove
end Perennial
