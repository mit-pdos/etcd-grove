/-
`(*Server).HandleHTTP(rpcPath, debugPath)`: registers the server on `DefaultServeMux` as the handler
of `rpcPath` (`http.Handle(rpcPath, server)`) and its debug page at `debugPath`. On the right to
register (`muxOwn (globalAddr net.http.defaultServeMux) Ps`) and two literal paths not registered yet, distinct, it registers both:
the right covers them, and the mux routes `rpcPath` to an rpc handler (`muxRpc (globalAddr net.http.defaultServeMux) W A rpcPath`) at
every address `a` with `A a`: there the server serves its registrations (`srvServes`) behind
net/http's `CONNECT` handshake (`W.hsAns a = connectAns`), which its `ServeHTTP` answers
(`Server.ServeHTTP.spec`, whose premises this one carries). The debug page (`debugHTTP`, whose
`ServeHTTP` is not modelled) is registered but not routed to by any rpc dialer (a path no
`CONNECT` asks for). Any registry mode (`isServerAny`). The shared rpc-over-HTTP design (L2).
Lean-first.
-/
module

public import Net.Proof.net.rpc.ServerDefs
public import Net.Proof.net.http.MuxDefs
public import Net.Proof.net.http.PkgInit

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.HandleHTTP.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (A : GoString → Prop)
    (Ps : List GoString) (rp dp : GoString),
    net.http.litPattern rp → net.http.litPattern dp → rp ≠ dp → rp ∉ Ps → dp ∉ Ps →
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) Ps ∗ isServerAny s γs ∗
      (□ ∀ a, ⌜A a⌝ → srvServes γs C W a ∗ ⌜W.hs a ≠ [] ∧ W.hsAns a = connectAns⌝) ∗
      srvEnv ∗ codecSet C ∗ globalAddr net.rpc.connected ↦□ connectedStatus }}
    (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"HandleHTTP"))
      (Val #rp)) (Val #dp))
  {{ RET #(); net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) (dp :: rp :: Ps) ∗
      net.http.muxRpc (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) W A rp }}

end spec
end net.rpc
end Perennial
