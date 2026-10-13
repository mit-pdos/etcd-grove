/-
`time.Time.Unix`, of Go's `time` package (not translated in Perennial's `time`: no body, so the
call cannot be stepped): returns some `int64` (the seconds since the epoch; unmodelled). The
compaction job's deferred `dbCompactionLast.Set(float64(time.Now().Unix()))` calls it
(2026-10-13, unit 5c). A trust-boundary axiom, true of Go's `Time.Unix` (it never panics).
-/
module

public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `t.Unix()`: some `int64`. -/
abbrev time.Time.Unix.spec : Prop :=
  ∀ t : time.Time,
  {{ (True : IProp GF) }}
    (App (Val #(methods time.Time.ty go!"Unix" #t)) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end EtcdGrove
end Perennial
