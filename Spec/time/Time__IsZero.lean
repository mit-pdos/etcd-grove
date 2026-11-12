/-
`time.Time.IsZero`: the trust boundary (Perennial translates `time` without `Time.IsZero`). Lean-first (no Rocq counterpart); the request path
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.IsZero()`: some boolean (whether `t` is the zero time; `isConnectedSince` only classifies a
connection by it); `t` kept. Unit P1b (2026-10-14). -/
abbrev time.Time.IsZero.spec : Prop :=
  ∀ (p : Loc) (t : _root_.Perennial.time.Time) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ p ↦{dq} t }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.time.Time.ty @!! go!"IsZero")) (Val #()))
  {{ (b : Bool), RET #b; p ↦{dq} t }}

end spec

end EtcdGrove
end Perennial
