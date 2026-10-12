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
value is any `val`); it returns. -/
abbrev time.Duration.Seconds.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
    (App (Val (d @!! _root_.Perennial.time.Duration.ty @!! go!"Seconds")) (Val #()))
  {{ (f : val), RET f; True }}

end spec

end EtcdGrove
end Perennial
