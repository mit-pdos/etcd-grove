/-
The trust boundary of `encoding.json.Marshal` (see its spec).
-/
module

public import Spec.encoding.json.Marshal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]

axiom encoding.json.Marshal.wp_proof : encoding.json.Marshal.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
