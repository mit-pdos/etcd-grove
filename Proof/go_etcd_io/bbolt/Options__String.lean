/-
The trust boundary: `Spec/go_etcd_io/bbolt/Options__String.lean` (`Options` is axiomatized:
`Proof/go_etcd_io/bbolt/Options.lean`'s header). True of Go: `String` only reads the 15 fields
and formats them with `fmt.Sprintf`, which cannot fail. It becomes a proof once `Options` is
translated (with a `fmt.Sprintf` spec over arguments with lent resources).
-/
module

public import Spec.go_etcd_io.bbolt.Options__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

axiom Options.String.wp_proof : Options.String.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
