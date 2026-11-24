/-
The proof of `Net/Spec/net/Conn__Read.lean`: the interface call resolves to `conn.Read.impl`
(`*TCPConn`'s promoted `Read`), whose extension `Read` takes the caller's update
(`Net.wp_net_Read`); the bytes are then copied into the buffer.
-/
module

public import Net.Spec.net.Conn__Read
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem Conn.Read.wp_proof : Conn.Read.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs0 eof ed Q
  unfold connAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hat⟩, Hsl, #Heof, #Hed, HAU⟩
  wp_method_call
  (try unfold conn.Read.impl)
  (try unfold model.connId)
  (try unfold model.connErr)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  ihave %Hne := netConnAt_endId_ne _ cn a s $$ Hat
  (try wp_auto)
  (try (rw [show decide (endId cn s = W64 0) = false by simpa using Hne]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Read cn s a b.len $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Hr Hend Hdir
  imod Hk $$ %r %d' %Hr Hend Hdir with HQ
  imodintro
  cases r with
  | bytes bs =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto
    wp_apply wp_string_to_bytes bs as %sl ⟨Hsl2, -⟩
    wp_apply wp_slice_copy b bs0 sl bs (DFrac.own 1) $$ [Hsl Hsl2] as %n ⟨%Hn, Hsl, -⟩
    · iframe
    iapply HΦ
    iexists .bytes bs, _
    iframe HQ Hsl
    isplitr; · ipureintro; exact ⟨Hn, rfl⟩
    unfold ReadErr
    ipureintro; rfl
  | eof =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto
    iapply HΦ
    iexists .eof, bs0
    iframe HQ Hsl
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    unfold ReadErr
    ipureintro; rfl
  | err k =>
    simp only [ReadRes.toVal]
    unfold readRes
    cases k
    · wp_auto
      wp_apply wp_kindErr (c := NetErr.closed.code) .closed (some ed) go!"read" (· = go!"read") rfl rfl $$ [] as %e #He
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists .err .closed, bs0
      iframe HQ Hsl
      isplitr; · ipureintro; exact ⟨rfl, rfl⟩
      unfold ReadErr resErr
      iexists e
      iframe Herr He
    · wp_auto
      wp_apply wp_kindErr (c := NetErr.timeout.code) .timeout (some ed) go!"read" (· = go!"read") rfl rfl $$ [Hed] as %e #He
      · iexact Hed
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists .err .timeout, bs0
      iframe HQ Hsl
      isplitr; · ipureintro; exact ⟨rfl, rfl⟩
      unfold ReadErr resErr
      iexists e
      iframe Herr He
    · wp_auto
      wp_apply wp_kindErr (c := NetErr.sys.code) .sys (some ed) go!"read" (· = go!"read") rfl rfl $$ [] as %e #He
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists .err .sys, bs0
      iframe HQ Hsl
      isplitr; · ipureintro; exact ⟨rfl, rfl⟩
      unfold ReadErr resErr
      iexists e
      iframe Herr He

/-- `Conn.Read.specLc`: the same, with a credit from the steps after the extension's `Read`. -/
theorem Conn.Read.wp_proofLc : Conn.Read.specLc (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs0 eof ed Q
  unfold connAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hat⟩, Hsl, #Heof, #Hed, HAU⟩
  wp_method_call
  (try unfold conn.Read.impl)
  (try unfold model.connId)
  (try unfold model.connErr)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  ihave %Hne := netConnAt_endId_ne _ cn a s $$ Hat
  (try wp_auto)
  (try (rw [show decide (endId cn s = W64 0) = false by simpa using Hne]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Read cn s a b.len $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Hr Hend Hdir
  imod Hk $$ %r %d' %Hr Hend Hdir with HQ
  imodintro
  cases r with
  | bytes bs =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto_lc 2
    wp_apply wp_string_to_bytes bs as %sl ⟨Hsl2, -⟩
    wp_apply wp_slice_copy_int b bs0 sl bs (DFrac.own 1) $$ [Hsl Hsl2] as %n ⟨%Hn, Hsl, -⟩
    · iframe
    iapply HΦ
    iexists .bytes bs, _
    iframe HQ Hsl Hlc1 Hlc2
    isplitr; · ipureintro; exact ⟨Hn, rfl⟩
    unfold ReadErr
    ipureintro; rfl
  | eof =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto_lc 2
    iapply HΦ
    iexists .eof, bs0
    iframe HQ Hsl Hlc1 Hlc2
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    unfold ReadErr
    ipureintro; rfl
  | err k =>
    simp only [ReadRes.toVal]
    unfold readRes
    cases k
    · wp_auto_lc 2
      wp_apply wp_kindErr (c := NetErr.closed.code) .closed (some ed) go!"read" (· = go!"read") rfl rfl $$ [] as %e #He
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists .err .closed, bs0
      iframe HQ Hsl Hlc1 Hlc2
      isplitr; · ipureintro; exact ⟨rfl, rfl⟩
      unfold ReadErr resErr
      iexists e
      iframe Herr He
    · wp_auto_lc 2
      wp_apply wp_kindErr (c := NetErr.timeout.code) .timeout (some ed) go!"read" (· = go!"read") rfl rfl $$ [Hed] as %e #He
      · iexact Hed
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists .err .timeout, bs0
      iframe HQ Hsl Hlc1 Hlc2
      isplitr; · ipureintro; exact ⟨rfl, rfl⟩
      unfold ReadErr resErr
      iexists e
      iframe Herr He
    · wp_auto_lc 2
      wp_apply wp_kindErr (c := NetErr.sys.code) .sys (some ed) go!"read" (· = go!"read") rfl rfl $$ [] as %e #He
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists .err .sys, bs0
      iframe HQ Hsl Hlc1 Hlc2
      isplitr; · ipureintro; exact ⟨rfl, rfl⟩
      unfold ReadErr resErr
      iexists e
      iframe Herr He

end proof

end net
end Perennial
