/-
The vr kit's small functions both machine kinds call (`kit.go`; notes/dsv-vr.md): `Addrs()` (the
go-vsr addresses, `VsrWire.addrs`), `RegisterJSON()` (nothing, until jsongen writes the codec:
finding 2), `logger()` (`slog.New(slog.DiscardHandler)`, over its callees' specs
`log.slog.New.spec` and `log.slog.DiscardHandler.load_spec`, `Dsverify/Spec/log/slog/Logger.lean`), and
`kit_frameDecoderSet`: the hook is set for good, `vsrwire`'s package fact (the kit links
`vsrwire`). One copy each (the client's `MkClientProof.lean` and the server's `ServerProof.lean`
had their own).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ConfDefs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.JsonHyps
public import Dsverify.Spec.log.slog.Logger
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Addrs
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__RemoteAddr

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- The hook is set for good: `vsrwire`'s package fact (the kit links `vsrwire`). -/
theorem kit_frameDecoderSet :
    isPkgInit (PROP := IProp GF) kpkg ⊢ pkg.events.frameDecoderSet (GF := GF) := by
  iintro #Hk
  ihave #Hw : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire $$ []
  · iPkgInit
  iapply isPkgInit_access $$ Hw

/-- `Addrs()` returns a new slice of every machine's go-vsr address (`VsrWire.addrs`). -/
theorem wp_Addrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Addrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* VsrWire.addrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) VsrWire.addrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `RegisterJSON()`: nothing (`register.go`, notes/dsv-vr.md finding 2). -/
theorem wp_RegisterJSON :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.RegisterJSON)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  iapply HΦ
  itrivial

/-- `logger()` = `slog.New(slog.DiscardHandler)`: a logger. -/
theorem wp_logger (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.logger)) (Val #()))
    {{ (l : Loc), RET #l; log.slog.isLogger l }} := by
  wp_start as -
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.log.slog $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Discard as %h %Hh
  subst Hh
  wp_apply wp_New as %l #Hl
  iapply HΦ
  iexact Hl

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
