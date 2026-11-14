/-
The proof of `examples/net/echo/cmd/server`'s `main`, echo's server node: `echo.Serve`
(`wp_Serve`), with `io.EOF`'s value from the package's initialization (`eof_init`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Nodes
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The server node's program: from echo's protocol and the plan's entry for `SrvAddr` at the
node's own host, it listens there and serves. -/
theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server ∗
        echoInvs γm ∗ tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hecho : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo) $$ []
  · iPkgInit
  icases eof_init $$ Hecho with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close γm eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server
end Perennial
