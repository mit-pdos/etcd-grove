/-
`HandleHTTP()` of the lab's `net/rpc` model (`server.go`): it registers the `DefaultServer` as the
default mux's handler for `rpcPath` (`http.Handle`). The real mux panics on a second
registration of a path, so the spec needs the mux's owner token (`muxOwner R`, http's
`Base.lean`) with `rpcPath` not registered yet.
-/
module

public import Harness.Proof.net.rpc.Server
public import Harness.Proof.net.http.Mux

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]

/-- The `DefaultServer`'s handler: the `*Server` as a `Handler`. -/
abbrev serverHandler (s : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType net.rpc.Server.ty, #s⟩

/-- `HandleHTTP()`: see the file header. -/
abbrev HandleHTTP.spec : Prop :=
  ∀ (R : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ net.http.muxOwner R ∗ ⌜rpcPath ∉ R⌝ }}
    (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
  {{ RET #(); net.http.muxOwner (rpcPath :: R) ∗
      ∃ s : Loc, globalAddr DefaultServer ↦□ s ∗ net.http.muxRoute rpcPath (serverHandler s) }}

set_option goose.wp.extras true

theorem HandleHTTP.wp_proof : HandleHTTP.spec (GF := GF) (hG := hG) := by
  intro R
  wp_start as ⟨Ho, %Hp⟩
  ihave ⟨#Hhttp, -, -, -⟩ := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  icases HDefaultServer with ⟨%s, #Hs, -⟩
  wp_auto
  wp_method_call
  wp_call
  unfold DefaultRPCPath DefaultDebugPath
  wp_auto
  wp_apply net.http.Handle.wp_proof R go!"/_goRPC_" (serverHandler s) $$ [$Hhttp $Ho] as ⟨Ho, #Hr⟩
  · ipureintro; exact ⟨by simp, Hp⟩
  iapply HΦ
  unfold rpcPath
  isplitl [Ho]
  · iexact Ho
  iexists s
  iframe Hs
  iexact Hr

end spec

end net.rpc

end Perennial
