/-
`context.TODO()` (Perennial translates `context` but does not specify `TODO`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.TODO()`: the context `todoCtxVal` (a `todoCtx{}`, never canceled; the client
contracts at it are `isEtcdKVTodo`, ...). -/
abbrev context.TODO.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! context.TODO)) (Val #()))
  {{ RET #(GoInterface.ok todoCtxVal); True }}

end spec

end EtcdGrove
end Perennial
