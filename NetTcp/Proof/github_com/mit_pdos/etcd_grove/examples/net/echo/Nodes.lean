/-
The proofs of `examples/net/echo`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: a full read of 5 bytes (a prefix of the dialer's), its echo (`server_write_au`,
  with the connection's token), and the close (`server_close_au`).
* `Serve`: `Listen`, then the accept loop (`wire.accept_au`: each accepted connection's protocol).
* `Call`: the dial (`wire.dial_au`, the deposit `echo_deposit`), the write of `"hello"`, the full
  read of the reply, and the check: the reply is a prefix of `"hello"` (`client_check`) of its
  length, so `"hello"`.
* `SendJunk`: as `Call`, without the check.
* `Server`, `Client`, `Junk`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Defs
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : echo.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem wp_serveConn
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn echoInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Htok, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn true srvAddr $$ Hc
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  imod tcpOutLb_nil (G (hG := hG)) cn false srvAddr $$ Hat with #Hlb0
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr buf
      _ TcpEnd.fresh 0 [] eof rfl $$ [Hbuf Hend]
    as %ok ⟨%st', %r', %bs', Hend, Hbuf, %Hlen, Hres⟩
  · simp only [Bool.not_true]
    iframe Hbuf Hend Heof Hlb0
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st' r' $$ HechoInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- echo the request, then close
    simp only [↓reduceIte]
    icases Hres with ⟨%sent, #Hsent, %Hs⟩
    obtain ⟨rfl, rfl, -, hsd⟩ := Hs
    simp only [List.drop_zero] at hsd
    subst hsd
    wp_auto
    wp_apply wp_Write t cn true srvAddr buf sent (DFrac.own 1)
        (fun _ _ => iprop(∃ st'', tcpEnd G cn true st'' (0 + (List.replicate 5 (zero_val w8)).length)))
        $$ [Hbuf Hend Htok]
      as %n %err ⟨%k, %okw, ⟨%st'', Hend⟩, Hbuf, -⟩
    · iframe Hc Hbuf
      iapply server_write_au γm cn γ sent sent TcpEnd.fresh
        (0 + (List.replicate 5 (zero_val w8)).length) (List.prefix_refl _) $$ HechoInv Hname Htok
        Hsent Hend
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st'' _ $$ HechoInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial
