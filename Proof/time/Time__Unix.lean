/-
`time.Time.Unix` (untranslated in Perennial's `time`): returns some `int64` (see the spec). An
axiom of the trust boundary (2026-10-13, mvcc unit 5c: the compaction job's metrics).
-/
module

public import Spec.time.Time__Unix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

axiom time.Time.Unix.wp_proof : time.Time.Unix.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
