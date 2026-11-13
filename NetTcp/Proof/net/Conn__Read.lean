/-
The proof of `NetTcp/Spec/net/Conn__Read.lean`: the interface call resolves to `conn.Read.impl`
(`*TCPConn`'s promoted `Read`), whose extension `Read` takes the caller's update
(`Tcp.wp_tcp_Read`); the bytes are then copied into the buffer.
-/
module

public import NetTcp.Spec.net.Conn__Read

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

omit [GooseSemantics] [HasExt tcpExt] sem package_sem' field_sem [go.BasicIntoValInj] in
theorem ReadPost_res (hT : TcpGS GF) (cn : Nat) (s : Bool) (n : w64) (st : TcpEnd) (r : Nat)
    (res : val) :
    ReadPost hT cn s n st r res -∗ ⌜∃ bs code, res = readRes bs code⌝ := by
  unfold ReadPost
  iintro (⟨%h, -⟩ | ⟨%h, -⟩ | ⟨%bs, %sent, %h, -⟩ | ⟨%sent, %h, -⟩)
  · ipureintro; exact ⟨_, _, h⟩
  · ipureintro; exact ⟨_, _, h.2.2⟩
  · ipureintro; exact ⟨_, _, h.2.2.2.2.2⟩
  · ipureintro; exact ⟨_, _, h.2.2⟩

theorem Conn.Read.wp_proof : Conn.Read.spec (GF := GF) (hG := hG) := by
  intro c cn s a b bs0 eof Q
  unfold isConn
  wp_start as ⟨⟨%t, %Hc, #Ht, #Hat⟩, Hsl, #Heof, HAU⟩
  subst Hc
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  unfold conn.Read.impl model.connId
  rw [conn_ty_eq']
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Read cn s a b.len $$ Hat
  imod HAU with ⟨%st, %r, Hend, Hk⟩
  imodintro
  iexists st, r
  iframe Hend
  iintro %res Hpost
  icases ReadPost_res _ cn s b.len st r res $$ Hpost with %Hres
  obtain ⟨bs, code, rfl⟩ := Hres
  imod Hk $$ %_ Hpost with HQ
  imodintro
  unfold readRes
  wp_auto
  by_cases h0 : code = W64 0
  · rw [decide_eq_true h0]
    wp_auto
    wp_apply wp_string_to_bytes bs as %sl ⟨Hsl2, -⟩
    wp_apply wp_slice_copy b bs0 sl bs (DFrac.own 1) $$ [Hsl Hsl2] as %n ⟨%Hn, Hsl, -⟩
    · iframe
    iapply HΦ
    iexists bs, code, _
    iframe HQ Hsl
    ipureintro
    left
    exact ⟨h0, Hn, rfl, rfl⟩
  · rw [decide_eq_false h0]
    wp_auto
    by_cases h1 : code = W64 1
    · rw [decide_eq_true h1]
      wp_auto
      iapply HΦ
      iexists bs, code, bs0
      iframe HQ Hsl
      ipureintro
      right; left
      exact ⟨h1, rfl, rfl, rfl⟩
    · rw [decide_eq_false h1]
      wp_auto
      unfold model.opError
      rw [OpError_ty_eq]
      wp_auto
      iapply HΦ
      iexists bs, code, bs0
      iframe HQ Hsl
      ipureintro
      right; right
      exact ⟨h0, h1, rfl, ⟨_, rfl⟩, rfl⟩

end proof

end net
end Perennial
