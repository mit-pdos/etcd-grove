/-
The trust boundary: `zapcore.CheckedEntry.Write` (names only). zap-z1 (2026-11-23) defined its entry
(`zapcore.zapEntry`: not dirty, no hooks, no cores) but could not prove it over zap's code: its last step,
`putCheckedEntry`, calls zap's generic `pool.Pool[T].Put(x)`, whose Goose translation passes `x : T` to
`sync.Pool.Put(any)` without converting it to an interface (`notes/perennial-changes.md`), so the model
gets stuck where Go runs. It goes when the translator converts.
-/
module

public import Spec.go_uber_org.zap.zapcore.CheckedEntry__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom zapcore.CheckedEntry.Write.wp_proof : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
