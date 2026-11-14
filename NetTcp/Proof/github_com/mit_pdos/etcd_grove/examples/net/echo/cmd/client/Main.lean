/-
The proof of `examples/net/echo/cmd/client`'s `main`, echo's client node: `echo.Call` (`wp_Call`),
with `io.EOF`'s value from the package's initialization (`eof_init`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Nodes
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The client node's program: from echo's protocol and the plan's entry for `SrvAddr` (at any
host `h`), it makes one call and checks the reply. -/
theorem wp_main
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client ∗
        echoInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hecho : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo) $$ []
  · iPkgInit
  icases eof_init $$ Hecho with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Call wp_Dial wp_ReadFull wp_Write wp_Close γm h eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client
end Perennial
