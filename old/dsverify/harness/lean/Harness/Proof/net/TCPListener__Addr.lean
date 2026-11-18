/-
The proof of `Spec/net/TCPListener__Addr.lean`: two loads. Then, from the persistent
`ownListener` alone (no token, no package state): `wp_TCPAddr`, the address is a non-`nil`
`*TCPAddr` (`net.isTCPAddr`, from the listener's `listenerAddr`); `wp_String`, the spec of
`l.Addr().String()`; and the same two through the `net.Listener` interface that `net.Listen`
returns (`net.wp_Listener_Addr`, `net.wp_Listener_Addr_String`), for `ln.Addr()` and
`ln.Addr().String()` in client code. The string is arbitrary (`TrustedCode/net.lean`: Go reports
the kernel's bound address, e.g. `"[::]:port"` for a wildcard `Listen`, not the listened-on
string).
-/
module

public import Harness.Spec.net.TCPListener__Addr

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem net.TCPListener.Addr.wp_proof : net.TCPListener.Addr.spec (GF := GF) (hG := hG) := by
  intro l lid a
  unfold net.ownListener net.ownFD
  wp_start as ⟨%fd, #Hfd, ⟨#Hid, #Hside, %la, %ra, #Hla, #Hra⟩, #Hl, -⟩
  rw [net.netFD_ty_eq, net.TCPListener_ty_eq, net.Addr_ty_eq]
  wp_auto
  iapply HΦ
  itrivial

/-- `l.Addr()` on a `*TCPListener` from `Listen` returns a non-`nil` `*TCPAddr`
(`net.isTCPAddr`): the listener's `listenerAddr`. -/
theorem net.TCPListener.Addr.wp_TCPAddr (l : Loc) (lid : w64) (a : GoString) :
    {{ net.ownListener (GF := GF) l lid a }}
      (App (Val (l @!! go.GoType.PointerType net.TCPListener.ty @!! go!"Addr")) (Val #()))
    {{ (ad : GoInterface), RET #ad; ⌜net.isTCPAddr ad⌝ }} := by
  unfold net.ownListener net.listenerAddr
  wp_start as ⟨%fd, #Hfd, -, -, %la, #Hla, %Hok⟩
  rw [net.netFD_ty_eq, net.TCPListener_ty_eq, net.Addr_ty_eq]
  wp_auto
  iapply HΦ
  ipureintro; exact Hok

/-- `l.Addr().String()` on a `*TCPListener` from `Listen` returns some string (no panic):
`Addr` returns a non-`nil` `*TCPAddr` (`wp_TCPAddr`), and the dynamic `Addr.String` call on it
resolves to `(*TCPAddr).String` (as in `net.wp_Addr_String`). `ownListener` is persistent, so
the caller keeps it. -/
theorem net.TCPListener.Addr.wp_String (l : Loc) (lid : w64) (a : GoString) :
    {{ net.ownListener (GF := GF) l lid a }}
      (App (App (Val (GoInstruction (MethodResolve net.Addr.ty go!"String")))
        (App (Val (l @!! go.GoType.PointerType net.TCPListener.ty @!! go!"Addr")) (Val #())))
        (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start_folded as #Hl
  wp_apply net.TCPListener.Addr.wp_TCPAddr $$ Hl as %ad %Had
  obtain ⟨x, rfl⟩ := Had
  wp_auto
  wp_apply net.wp_TCPAddr_String x as %s -
  iapply HΦ; itrivial

/-- `ln.Addr()` on the `net.Listener` that `net.Listen` returns (`*TCPListener` `l`, as in the
specs of `Listen`): the dynamic call resolves to `(*TCPListener).Addr`, which returns a non-`nil`
`*TCPAddr` (`net.TCPListener.Addr.wp_TCPAddr`). -/
theorem net.wp_Listener_Addr (l : Loc) (lid : w64) (a : GoString) :
    {{ net.ownListener (GF := GF) l lid a }}
      (App (App (Val (GoInstruction (MethodResolve net.Listener.ty go!"Addr")))
        (Val #(interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l))) (Val #()))
    {{ (ad : GoInterface), RET #ad; ⌜net.isTCPAddr ad⌝ }} := by
  wp_start_folded as #Hl
  wp_auto
  wp_apply net.TCPListener.Addr.wp_TCPAddr $$ Hl as %ad %Had
  iapply HΦ; ipureintro; exact Had

/-- `ln.Addr().String()` on the `net.Listener` that `net.Listen` returns: some string (no
panic). -/
theorem net.wp_Listener_Addr_String (l : Loc) (lid : w64) (a : GoString) :
    {{ net.ownListener (GF := GF) l lid a }}
      (App (App (Val (GoInstruction (MethodResolve net.Addr.ty go!"String")))
        (App (App (Val (GoInstruction (MethodResolve net.Listener.ty go!"Addr")))
          (Val #(interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l))) (Val #())))
        (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start_folded as #Hl
  wp_apply net.wp_Listener_Addr $$ Hl as %ad %Had
  obtain ⟨x, rfl⟩ := Had
  wp_auto
  wp_apply net.wp_TCPAddr_String x as %s -
  iapply HΦ; itrivial

end proof

end Perennial
