/-
The SwiftPaxos kit's thirteen commands' `main`s (`examples/swiftnet/cmd/*`), each its kit function
on its constant (`Orch()`, `Client(c)`, `Server(id)`), from the kit functions' specs
(`ClientNodeDefs.lean`, `ServeDefs.lean`), as dsv-epaxos's `Mains.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.orch.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server6.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServeDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.imdea_software.swiftpaxos
  github_com.imdea_software.swiftpaxos.cnode EtcdGrove EtcdGrove.linkv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.orch

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.orch.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory in
theorem wp_main [ρ : RemoteGS] (wp_Orch : cnode.Orch.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) (γp : PendNames) (hrb : receiptBound netDistGF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.orch ∗
        conf.writer γ ∗ common γ ∗
        ([∗list] a ∈ clientAddrs,
          remoteAddr (Gg := hG.goose_globalGS) (swRK (G := hG.goose_globalGS) γk) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (swRK (G := hG.goose_globalGS) γk) (swS0 (GF := netDistGF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (swS0 (GF := netDistGF)) γp (swS0 (GF := netDistGF)).M.init ∗
        [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 24 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hw, #Hc, #Has, #Hm, #Hp, Hlib, Hbud⟩
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γk γp hrb $$ [Hw Hlib Hbud]
  · iframe
    iframe #
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.orch

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.client0.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main [ρ : RemoteGS] (wp_Client : cnode.Client.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0 ∗
        clientRes γ γk 0 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ γk 0 (by decide) $$ [Hr] as %hf
  · iframe
  exact hf.elim


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client1

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.client1.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main [ρ : RemoteGS] (wp_Client : cnode.Client.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client1 ∗
        clientRes γ γk 1 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ γk 1 (by decide) $$ [Hr] as %hf
  · iframe
  exact hf.elim


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client1

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client2

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.client2.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main [ρ : RemoteGS] (wp_Client : cnode.Client.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client2 ∗
        clientRes γ γk 2 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ γk 2 (by decide) $$ [Hr] as %hf
  · iframe
  exact hf.elim


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client2

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client3

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.client3.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main [ρ : RemoteGS] (wp_Client : cnode.Client.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client3 ∗
        clientRes γ γk 3 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ γk 3 (by decide) $$ [Hr] as %hf
  · iframe
  exact hf.elim


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client3

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client4

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.client4.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main [ρ : RemoteGS] (wp_Client : cnode.Client.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client4 ∗
        clientRes γ γk 4 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ γk 4 (by decide) $$ [Hr] as %hf
  · iframe
  exact hf.elim


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client4

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client5

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.client5.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main [ρ : RemoteGS] (wp_Client : cnode.Client.spec (hG := hG))
    (γ : SwiftNames netDistGF) (γk : GName) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client5 ∗
        clientRes γ γk 5 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ γk 5 (by decide) $$ [Hr] as %hf
  · iframe
  exact hf.elim


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client5

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server1

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.server1.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main (wp_Server : Server.spec (hG := hG)) (γ : SwiftNames netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server1 ∗
        serverRes γ 0 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 0 (by decide) $$ [Hr]
  · iframe
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server1

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.server2.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main (wp_Server : Server.spec (hG := hG)) (γ : SwiftNames netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2 ∗
        serverRes γ 1 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 1 (by decide) $$ [Hr]
  · iframe
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server3

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.server3.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main (wp_Server : Server.spec (hG := hG)) (γ : SwiftNames netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server3 ∗
        serverRes γ 2 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 2 (by decide) $$ [Hr]
  · iframe
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server3

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server4

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.server4.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main (wp_Server : Server.spec (hG := hG)) (γ : SwiftNames netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server4 ∗
        serverRes γ 3 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 3 (by decide) $$ [Hr]
  · iframe
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server4

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server5

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.server5.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main (wp_Server : Server.spec (hG := hG)) (γ : SwiftNames netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server5 ∗
        serverRes γ 4 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 4 (by decide) $$ [Hr]
  · iframe
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server5

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server6

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
variable [net.http.Assumptions] [client.Assumptions] [package_sem' : cmd.server6.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]


theorem wp_main (wp_Server : Server.spec (hG := hG)) (γ : SwiftNames netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server6 ∗
        serverRes γ 5 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hr
  ihave #Hkp : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 5 (by decide) $$ [Hr]
  · iframe
  iapply HΦ
  itrivial


end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server6

end Perennial
