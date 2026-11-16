/-
The trust boundary: `time.Time.Format` (names-only in Perennial; see `Spec/time/Time__Format.lean`).
**Pending the user's review** (WAL leaf specs, 2026-11-13).
-/
module

public import Spec.time.Time__Format

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

axiom time.Time.Format.wp_proof : time.Time.Format.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
