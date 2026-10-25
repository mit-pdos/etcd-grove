/-
The request ID context key of `server/v3/etcdserver/requestid` (PR etcd#21401).

* `ctxReqIDIs ctx o` (persistent): what `ctx.Value(requestIDKey{})` returns: the `uint64` request ID
  `id` (`o = some id`, stored by `requestid.NewContext`) or `nil` (`o = none`: no request ID stored
  in `ctx`, as for `context.TODO()`, `context.Background()`, and raw gRPC request contexts).
  Note that `requestIDKey` is an unexported struct type in `package requestid` whose only writer is
  `NewContext(ctx, requestID uint64)`, and `FromContext` performs an unchecked `val.(uint64)` type
  assertion whenever `val != nil`.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.requestid
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.etcdserver.requestid

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.requestid :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.requestid :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.requestid

end init

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.requestid.Assumptions]

/-- What a context's `Value(requestIDKey{})` returns for its request ID `o`. -/
def requestid.reqIDValIs (v : GoInterface) : Option w64 → Prop
  | some id => v = interface.mkOk go.uint64 #id
  | none => v = GoInterface.nil

/-- The key `requestIDKey{}`, as an `any`. -/
abbrev requestid.reqIDKeyVal : GoInterface :=
  interface.mkOk requestid.requestIDKey.ty #(zero_val requestid.requestIDKey)

/-- **The context `ctx` carries the request ID `o`** (persistent): its `Value(requestIDKey{})`, from
any goroutine, returns `o` (`reqIDValIs`). -/
def requestid.ctxReqIDIs (ctx : GoInterfaceOk) (o : Option w64) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF,
    ▷ (∀ v : GoInterface, ⌜requestid.reqIDValIs v o⌝ -∗ Φ #v) -∗
      WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #requestid.reqIDKeyVal)) {{ Φ }})

instance requestid.ctxReqIDIs_persistent (ctx : GoInterfaceOk) (o : Option w64) :
    Persistent (requestid.ctxReqIDIs (GF := GF) ctx o) := by
  unfold requestid.ctxReqIDIs; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.requestid.Assumptions]

/-- **`context.TODO()` carries no request ID**: its `Value` (`emptyCtx`'s) returns `nil`. -/
theorem requestid.ctxReqIDIs_todo :
    ⊢ requestid.ctxReqIDIs (GF := GF) (interface.mk context.todoCtx.ty #(zero_val context.todoCtx))
      none := by
  iunfold requestid.ctxReqIDIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  ipureintro; rfl

/-- **`context.Background()` carries no request ID**: its `Value` (`emptyCtx`'s) returns `nil`. -/
theorem requestid.ctxReqIDIs_background :
    ⊢ requestid.ctxReqIDIs (GF := GF)
      (interface.mk context.backgroundCtx.ty #(zero_val context.backgroundCtx)) none := by
  iunfold requestid.ctxReqIDIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  ipureintro; rfl

end lemmas

end EtcdGrove
end Perennial
