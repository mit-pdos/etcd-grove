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

theorem Conn.Read.wp_proof : Conn.Read.spec (GF := GF) (hG := hG) := by
  intro t cn s a b bs0 eof Q
  unfold connAt
  wp_start as ⟨⟨#Ht, #Hat⟩, Hsl, #Heof, HAU⟩
  wp_method_call
  (try unfold conn.Read.impl)
  (try unfold model.connId)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_tcp_Read cn s a b.len $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Hr Hend Hdir
  imod Hk $$ %r %d' %Hr Hend Hdir with HQ
  imodintro
  obtain ⟨-, hw⟩ := Hr
  cases r with
  | wait => exact absurd rfl hw
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
    ipureintro
    exact ⟨Hn, rfl, rfl⟩
  | eof =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto
    iapply HΦ
    iexists .eof, bs0
    iframe HQ Hsl
    ipureintro
    exact ⟨rfl, rfl, rfl⟩
  | err =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto
    unfold model.opError
    rw [OpError_ty_eq]
    wp_auto
    iapply HΦ
    iexists .err, bs0
    iframe HQ Hsl
    ipureintro
    exact ⟨rfl, ⟨_, rfl⟩, rfl⟩

end proof

end net
end Perennial
