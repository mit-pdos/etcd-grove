/-
The proof of `examples/net/framed/cmd/server`'s `main`, the server node's program: it calls
`framed.Serve` (`wp_Serve`), with `io.EOF`'s value from the package's initialization.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.server.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.Nodes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.framed (framedInvs srvAddr wp_Serve eof_init)

namespace github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.server ∗
        framedInvs γm ∗ tcpPlan wire.G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hfr : (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.framed)
    $$ []
  · iPkgInit
  icases eof_init $$ Hfr with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close γm eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.server
end Perennial
