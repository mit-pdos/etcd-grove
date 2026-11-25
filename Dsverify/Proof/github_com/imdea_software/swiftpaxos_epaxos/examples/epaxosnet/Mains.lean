/-
The EPaxos kit's seventeen commands' `main`s (`examples/epaxosnet/cmd/*`), each its kit function on
its constant (`Orch()`, `Client(c)`, `Server(id)`), from the kit functions' specs (`KitSpecs.lean`,
`ServerSpecs.lean`), as craq's and paxos's `Mains.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.KitSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerSpecs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.imdea_software.swiftpaxos_epaxos
  github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet EtcdGrove EtcdGrove.linkv

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Orch : epaxosnet.Orch.spec (GF := GF) (hG := hG))
    (γ : EpNames) (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (epR γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (epR γ) (epS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (epS0 (GF := GF)) γp (epS0 (GF := GF)).M.init ∗
        [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 6 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Has, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γp hrb $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 0 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 0) (by decide) as %hf
  · rw [show uint.nat (W64 0) = 0 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 1 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 1) (by decide) as %hf
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 2 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 2) (by decide) as %hf
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 3 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 3) (by decide) as %hf
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client4.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 4 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 4) (by decide) as %hf
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client5.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 5 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 5) (by decide) as %hf
  · rw [show uint.nat (W64 5) = 5 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client6.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 6 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 6) (by decide) as %hf
  · rw [show uint.nat (W64 6) = 6 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client7.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 7 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 7) (by decide) as %hf
  · rw [show uint.nat (W64 7) = 7 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client8.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 8 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 8) (by decide) as %hf
  · rw [show uint.nat (W64 8) = 8 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client9.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] (wp_Client : epaxosnet.Client.spec (GF := GF) (hG := hG))
    (γ : EpNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9 ∗ clientInvs γ ∗
        remoteAddr (Gg := hG.goose_globalGS) (epR γ) (clientAddrs.getD 9 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := EIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 9) (by decide) as %hf
  · rw [show uint.nat (W64 9) = 9 from rfl]
    iframe #
  exact hf.elim

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
    [RpcHttpAddr GF] [RpcHttpHyp GF] (wp_Server : epaxosnet.Server.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1 ∗ codecFresh ∗ muxOwner [] ∗
        defaultSrvFresh ∗ threadTok ∗
        net.rpc.srvEnv ∗ dialEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverRes γ W 1 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, Hds, Htok, #Henv, #Hde, %Hb, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ W (W64 1) (by decide) (by decide) $$ [Hcf Hmux Hds Htok Hres]
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe Hcf Hmux Hds Htok Hres
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
    [RpcHttpAddr GF] [RpcHttpHyp GF] (wp_Server : epaxosnet.Server.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2 ∗ codecFresh ∗ muxOwner [] ∗
        defaultSrvFresh ∗ threadTok ∗
        net.rpc.srvEnv ∗ dialEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverRes γ W 2 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, Hds, Htok, #Henv, #Hde, %Hb, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ W (W64 2) (by decide) (by decide) $$ [Hcf Hmux Hds Htok Hres]
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe Hcf Hmux Hds Htok Hres
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
    [RpcHttpAddr GF] [RpcHttpHyp GF] (wp_Server : epaxosnet.Server.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3 ∗ codecFresh ∗ muxOwner [] ∗
        defaultSrvFresh ∗ threadTok ∗
        net.rpc.srvEnv ∗ dialEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverRes γ W 3 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, Hds, Htok, #Henv, #Hde, %Hb, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ W (W64 3) (by decide) (by decide) $$ [Hcf Hmux Hds Htok Hres]
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe Hcf Hmux Hds Htok Hres
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
    [RpcHttpAddr GF] [RpcHttpHyp GF] (wp_Server : epaxosnet.Server.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4 ∗ codecFresh ∗ muxOwner [] ∗
        defaultSrvFresh ∗ threadTok ∗
        net.rpc.srvEnv ∗ dialEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverRes γ W 4 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, Hds, Htok, #Henv, #Hde, %Hb, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ W (W64 4) (by decide) (by decide) $$ [Hcf Hmux Hds Htok Hres]
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
    iframe Hcf Hmux Hds Htok Hres
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server5.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
    [RpcHttpAddr GF] [RpcHttpHyp GF] (wp_Server : epaxosnet.Server.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5 ∗ codecFresh ∗ muxOwner [] ∗
        defaultSrvFresh ∗ threadTok ∗
        net.rpc.srvEnv ∗ dialEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverRes γ W 5 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, Hds, Htok, #Henv, #Hde, %Hb, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ W (W64 5) (by decide) (by decide) $$ [Hcf Hmux Hds Htok Hres]
  · rw [show uint.nat (W64 5) = 5 from rfl]
    iframe #
    iframe Hcf Hmux Hds Htok Hres
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server6.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
    [RpcHttpAddr GF] [RpcHttpHyp GF] (wp_Server : epaxosnet.Server.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6 ∗ codecFresh ∗ muxOwner [] ∗
        defaultSrvFresh ∗ threadTok ∗
        net.rpc.srvEnv ∗ dialEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverRes γ W 6 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, Hds, Htok, #Henv, #Hde, %Hb, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ W (W64 6) (by decide) (by decide) $$ [Hcf Hmux Hds Htok Hres]
  · rw [show uint.nat (W64 6) = 6 from rfl]
    iframe #
    iframe Hcf Hmux Hds Htok Hres
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6

end Perennial

