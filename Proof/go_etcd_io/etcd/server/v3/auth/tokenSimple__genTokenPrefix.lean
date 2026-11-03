/-
The trust boundary: `tokenSimple.genTokenPrefix` (names only: `crypto/rand`, `math/big`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__genTokenPrefix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom auth.tokenSimple.genTokenPrefix.wp_proof :
  auth.tokenSimple.genTokenPrefix.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
