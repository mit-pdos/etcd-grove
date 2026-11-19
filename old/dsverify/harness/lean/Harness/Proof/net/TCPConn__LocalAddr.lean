/-
The proof of `Spec/net/TCPConn__LocalAddr.lean`: the promoted method, then two loads (the
address from the end's `connAddrs`); and `wp_String`, the spec of `c.LocalAddr().String()`.
-/
module

public import Harness.Spec.net.TCPConn__LocalAddr

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

theorem net.TCPConn.LocalAddr.wp_proof : net.TCPConn.LocalAddr.spec (GF := GF) (hG := hG) := by
  intro c cid side
  unfold net.ownTCPConn net.connAddrs
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, %la, %ra, #Hla, #Hra, %Hok⟩
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  rw [net.netFD_ty_eq, net.Addr_ty_eq]
  wp_auto
  iapply HΦ
  ipureintro; exact Hok.1

/-- `c.LocalAddr().String()` on a `*TCPConn` from `Dial` or `Accept` returns some string (no
panic): `LocalAddr` returns a non-`nil` `*TCPAddr` (`wp_proof`), and the dynamic `Addr.String` call
on it resolves to `(*TCPAddr).String` (as in `net.wp_Addr_String`). `ownTCPConn` is persistent,
so the caller keeps it. -/
theorem net.TCPConn.LocalAddr.wp_String (c : Loc) (cid : w64) (side : Bool) :
    {{ net.ownTCPConn (GF := GF) c cid side }}
      (App (App (Val (GoInstruction (MethodResolve net.Addr.ty go!"String")))
        (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"LocalAddr")) (Val #())))
        (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start_folded as #Hc
  wp_apply net.TCPConn.LocalAddr.wp_proof $$ Hc as %ad %Had
  obtain ⟨x, rfl⟩ := Had
  wp_auto
  wp_apply net.wp_TCPAddr_String x as %s -
  iapply HΦ; itrivial

end proof

end Perennial
