/-
The proof of `examples/net/shutdown/cmd/node`, the node's command: its `main` calls `shutdown.Run`
(`shutdown.wp_Run`), with the package's `isPkgInit` from the command's and `io.EOF`'s value from
the package's (`shutdown.eof_init`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Nodes
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.shutdown (addr shutInvs wp_Run eof_init)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The node's `main`: `Run`, from the protocol's invariants and the plan's entry for `Addr` at
the node's host. -/
theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_LClose : net.Listener.Close.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node ∗
        shutInvs (GF := GF) γm ∗
        tcpPlan G addr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hp : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.shutdown) $$ []
  · iPkgInit
  iunfold shutInvs at Hinvs
  icases Hinvs with ⟨#Ha, #Hdown⟩
  icases eof_init $$ Hp with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Run wp_Listen wp_Accept wp_LClose wp_Dial wp_Read wp_Write wp_Close γm eof $$ []
  · iframe Ha Hdown Hplan Heof
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node
end Perennial
