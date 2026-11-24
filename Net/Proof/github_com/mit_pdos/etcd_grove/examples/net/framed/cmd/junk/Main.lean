/-
The proof of `examples/net/framed/cmd/junk`'s `main`, the junk node's program: it calls
`framed.SendJunk` (`wp_SendJunk`), with `poll.ErrDeadlineExceeded`'s value from the package's
initialization (through `wire`'s, `wire.ed_init`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.junk.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.Nodes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.framed (framedInvs srvAddr wp_SendJunk)

namespace github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.junk

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Assumptions]
variable [go.BasicIntoValInj]

theorem wp_main
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.junk ∗
        framedInvs γm ∗ ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hfr : (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.framed)
    $$ []
  · iPkgInit
  ihave #Hwi : (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire)
    $$ []
  · iPkgInit
  icases wire.ed_init $$ Hwi with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply wp_SendJunk wp_Dial wp_Write wp_Close γm ed $$ []
  · iframe Hinvs Hplan Hed
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.junk
end Perennial
