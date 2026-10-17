/-
The client IP a request's context carries (PR etcd#22259, `pr-verify/etcd-22259`: the server's
log interceptor stores `peer.Addr.String()` under the key `auth.ClientIPContextKey{}`, and the
auth store's log lines read it back with `auth.ClientIPFromContext`). Lean-first (no Rocq
counterpart).

* `clientIPValIs v o`: what `ctx.Value(ClientIPContextKey{})` may return for the client IP `o`:
  the string `s` (`o = some s`), or no IP (`o = none`: `nil` or a value that is not a string,
  which `ClientIPFromContext`'s `.(string)` assertion rejects).
* `ctxClientIPIs ctx o` (persistent): the context's `Value(ClientIPContextKey{})`, from any
  goroutine, returns it.
* `ctxClientIPOk ctx` (persistent): `ctx` is a non-nil interface carrying some client IP or none.
  What `AuthInfoFromCtx` needs of its context since the PR (`ClientIPFromContext` calls
  `ctx.Value`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.auth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What a context's `Value(ClientIPContextKey{})` may return, for its client IP `o`. -/
def auth.clientIPValIs (v : GoInterface) : Option GoString → Prop
  | some s => v = interface.mkOk go.string #s
  | none => v = GoInterface.nil ∨ ∃ ii : GoInterfaceOk, v = GoInterface.ok ii ∧ ii.ty ≠ go.string

/-- The key `ClientIPContextKey{}`, as an `any`. -/
abbrev auth.clientIPKeyVal : GoInterface :=
  interface.mkOk auth.ClientIPContextKey.ty #(zero_val auth.ClientIPContextKey)

/-- **The context `ctx` carries the client IP `o`** (persistent): its
`Value(ClientIPContextKey{})`, from any goroutine, returns it (`clientIPValIs`). -/
def auth.ctxClientIPIs (ctx : GoInterfaceOk) (o : Option GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF,
    ▷ (∀ v : GoInterface, ⌜auth.clientIPValIs v o⌝ -∗ Φ #v) -∗
      WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #auth.clientIPKeyVal)) {{ Φ }})

instance auth.ctxClientIPIs_persistent (ctx : GoInterfaceOk) (o : Option GoString) :
    Persistent (auth.ctxClientIPIs (GF := GF) ctx o) := by
  unfold auth.ctxClientIPIs; infer_instance

/-- **`ctx` is a context carrying some client IP, or none** (persistent). -/
def auth.ctxClientIPOk (ctx : GoInterface) : IProp GF :=
  iprop(∃ (ci : GoInterfaceOk) (o : Option GoString), ⌜ctx = GoInterface.ok ci⌝ ∗
    auth.ctxClientIPIs ci o)

instance auth.ctxClientIPOk_persistent (ctx : GoInterface) :
    Persistent (auth.ctxClientIPOk (GF := GF) ctx) := by
  unfold auth.ctxClientIPOk; infer_instance

end defs

end EtcdGrove
end Perennial
