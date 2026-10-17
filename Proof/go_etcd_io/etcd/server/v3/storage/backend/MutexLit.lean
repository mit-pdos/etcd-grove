/-
`sync.Mutex{}`: a gap in Perennial's model, worked around here (2026-10-17, branch `construct`).
Lean-first (no Rocq counterpart).

Perennial models `sync.Mutex` as a boolean (`TrustedCode/sync.lean`: underlying `go.bool`, the
zero value `false`, unlocked), and its semantics has composite-literal rules for structs, arrays,
slices, maps and pointers only (`Golang/Defn`), so the Go expression `sync.Mutex{}` (in
`newBackend`'s `txReadBufferCache{mu: sync.Mutex{}, ...}`) has no step. In Go it is the zero
`Mutex`, unlocked: `wp_mutexLit` states that, a trust-boundary axiom about Go's semantics that
Perennial's model leaves unspecified. The general fix belongs in Perennial (an empty composite
literal of a type whose underlying type is not a struct is its zero value), recorded in
`notes/STATUS.md` (item 6).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI

section ax
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `sync.Mutex{}` is the zero `Mutex` (unlocked: `false` in Perennial's model). -/
axiom wp_mutexLit :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (CompositeLiteral sync.Mutex.ty))) (Val (LiteralValueV [])))
  {{ RET #(false : Bool); True }}

end ax

end backend
end EtcdGrove
end Perennial
