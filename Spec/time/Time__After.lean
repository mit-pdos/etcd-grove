/-
`time.Time.After`: the trust boundary (Perennial translates `time` without `Time.After`). Lean-first (no Rocq counterpart); the request path
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

/-- `t.After(u)`: some boolean (`parseProposeCtxErr` only classifies its error by it); `t` kept. -/
abbrev time.Time.After.spec : Prop :=
  ∀ (p : Loc) (t u : _root_.Perennial.time.Time) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ p ↦{dq} t }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.time.Time.ty @!! go!"After")) (Val #u))
  {{ (b : Bool), RET #b; p ↦{dq} t }}

end spec

end EtcdGrove
end Perennial
