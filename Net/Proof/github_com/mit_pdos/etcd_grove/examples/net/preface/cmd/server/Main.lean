/-
The proof of `examples/net/preface/cmd/server`'s `main`, preface's server node: `preface.Serve`
(`wp_Serve`), with `io.EOF`'s and `poll.ErrDeadlineExceeded`'s values from the package's initialization
(`eof_init`, `wire.ed_init`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Nodes
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.preface (srvAddr pfInvs)

namespace github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Assumptions]
variable [go.BasicIntoValInj]

/-- The server node: given preface's protocol and the plan's entry for `SrvAddr` at this node's
host, it listens and serves (`wp_Serve`). -/
theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Add : time.Time.Add.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server ∗
        pfInvs γm ∗
        ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan⟩
  ihave #Hpf : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.preface) $$ []
  · iPkgInit
  icases preface.eof_init $$ Hpf with ⟨%eof, #Heof⟩
  ihave #Hwire : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire) $$ []
  · iPkgInit
  icases wire.ed_init $$ Hwire with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply preface.wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close wp_SetDeadline wp_Now
    wp_Add γm eof ed $$ []
  · iframe Hinvs Heof Hed
    ipureintro; exact Hplan
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server
end Perennial
