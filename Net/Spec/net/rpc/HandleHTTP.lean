/-
`rpc.HandleHTTP()`: `DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`
(`Server.HandleHTTP.spec` on `DefaultServer`, `defaultServerAny`). Lean-first.
-/
module

public import Net.Spec.net.rpc.Server__HandleHTTP

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

/-- `DefaultDebugPath`. -/
def defaultDebugPath : GoString := go!"/debug/rpc"

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev HandleHTTP.spec : Prop :=
  ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (A : GoString → Prop)
    (Ps : List GoString),
    defaultRPCPath ∉ Ps → defaultDebugPath ∉ Ps →
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) Ps ∗ defaultServerAny γs ∗
      (□ ∀ a, ⌜A a⌝ → srvServes γs C W a ∗ ⌜W.hs a ≠ [] ∧ W.hsAns a = connectAns⌝) ∗
      srvEnv ∗ codecSet C ∗ globalAddr net.rpc.connected ↦□ connectedStatus }}
    (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
  {{ RET #(); net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) (defaultDebugPath :: defaultRPCPath :: Ps) ∗
      net.http.muxRpc (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) W A defaultRPCPath }}

end spec
end net.rpc
end Perennial
