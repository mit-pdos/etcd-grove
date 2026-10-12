/-
`time.Duration.Seconds`: the trust boundary (Perennial translates `time` without `Duration.Seconds`, a float division). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `d.Seconds()`: some `float64` (the duration in seconds; floats are outside the model, so the
value is any `float64`, Perennial's 64-bit word: 2026-10-12, unit 2: a word, not any `val`, so that
the code that binds it steps); it returns. -/
abbrev time.Duration.Seconds.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
    (App (Val (d @!! _root_.Perennial.time.Duration.ty @!! go!"Seconds")) (Val #()))
  {{ (f : w64), RET #f; True }}

end spec

end EtcdGrove
end Perennial
