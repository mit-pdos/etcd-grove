/-
The proof of `examples/net/duplex/cmd/client`'s `main`, the client node's program: it calls
`duplex.Call` (`wp_Call`, `Nodes.lean`), with the example package's initialization from the
command's (`iPkgInit`) and the values of `io.EOF` and `poll.ErrDeadlineExceeded` from it
(`eof_init`, `wire.ed_init`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Nodes
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.duplex (dupInvs srvAddr eof_init wp_Call)

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : client.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The client node's program, over the protocol's invariants and the plan's entry for `SrvAddr`
(at any host `h`). -/
theorem wp_main
    (wp_RandomInt : wire.RandomInt.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client ∗
        dupInvs γm ∗ ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hdup : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex) $$ []
  · iPkgInit
  icases eof_init $$ Hdup with ⟨%eof, #Heof⟩
  ihave #Hwire : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire) $$ []
  · iPkgInit
  icases wire.ed_init $$ Hwire with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply wp_Call wp_RandomInt wp_Dial wp_ReadFull wp_Write wp_Close γm eof ed $$ []
  · iframe Hinvs Hplan Heof Hed
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client
end Perennial
