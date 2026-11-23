/-
The gryff kit's eleven commands' `main`s (`examples/gryffnet/cmd/*`), each its kit function on its
constant (`Orch()`, `Client(c)`, `Server(id)`), from the kit functions' specs (`KitSpecs.lean`,
`KitServer.lean`), as dsv-epaxos's and paxos's `Mains.lean`.
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.cmd.orch.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client0.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client1.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client2.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client3.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client4.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client5.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server1.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server2.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server3.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server4.Base
public import Dsverify.Proof.gryff.examples.gryffnet.KitSpecs
public import Dsverify.Proof.gryff.examples.gryffnet.ServerSpec

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.gryff

namespace gryff.examples.gryffnet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Orch : gryffnet.Orch.spec (GF := GF) (hG := hG))
    (γ : ProtoNames) (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.orch ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (casR γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) ∗
        pendCtx (Gg := hG.goose_globalGS) (casR γ) (casS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (casS0 (GF := GF)) γp (casS0 (GF := GF)).M.init }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Has, #Hmap, #Hpend, Hlib⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γp hrb $$ [Hlib]
  · iframe #
    iframe Hlib
  iapply HΦ
  itrivial

end proof

end gryff.examples.gryffnet.cmd.orch

namespace gryff.examples.gryffnet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Client : gryffnet.Client.spec (GF := GF) (hG := hG))
    (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client0 ∗ □ protoInvs γ ∗
        replicaLises γ ∗ clientStartRes γ 0 ∗
        remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD 0 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpi, #Hrl, Hst, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 0 (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end gryff.examples.gryffnet.cmd.client0

namespace gryff.examples.gryffnet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Client : gryffnet.Client.spec (GF := GF) (hG := hG))
    (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client1 ∗ □ protoInvs γ ∗
        replicaLises γ ∗ clientStartRes γ 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD 1 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpi, #Hrl, Hst, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 1 (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end gryff.examples.gryffnet.cmd.client1

namespace gryff.examples.gryffnet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Client : gryffnet.Client.spec (GF := GF) (hG := hG))
    (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client2 ∗ □ protoInvs γ ∗
        replicaLises γ ∗ clientStartRes γ 2 ∗
        remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD 2 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpi, #Hrl, Hst, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 2 (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end gryff.examples.gryffnet.cmd.client2

namespace gryff.examples.gryffnet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Client : gryffnet.Client.spec (GF := GF) (hG := hG))
    (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client3 ∗ □ protoInvs γ ∗
        replicaLises γ ∗ clientStartRes γ 3 ∗
        remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD 3 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpi, #Hrl, Hst, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 3 (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end gryff.examples.gryffnet.cmd.client3

namespace gryff.examples.gryffnet.cmd.client4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Client : gryffnet.Client.spec (GF := GF) (hG := hG))
    (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client4 ∗ □ protoInvs γ ∗
        replicaLises γ ∗ clientStartRes γ 4 ∗
        remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD 4 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpi, #Hrl, Hst, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 4 (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end gryff.examples.gryffnet.cmd.client4

namespace gryff.examples.gryffnet.cmd.client5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client5.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [ρ : RemoteGS] [AllG GF] (wp_Client : gryffnet.Client.spec (GF := GF) (hG := hG))
    (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client5 ∗ □ protoInvs γ ∗
        replicaLises γ ∗ clientStartRes γ 5 ∗
        remoteAddr (Gg := hG.goose_globalGS) (casR γ.proto) (clientAddrs.getD 5 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := In) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpi, #Hrl, Hst, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 5 (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end gryff.examples.gryffnet.cmd.client5

namespace gryff.examples.gryffnet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]
    (wp_Server : gryffnet.Server.spec (GF := GF) (hG := hG)) (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.server1 ∗
        serverBoot (GF := GF) ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverShare γ 0 ∗ (if 0 = 0 then iprop(True) else iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph)) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hboot, %Hb, Hsh, Hx⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  ihave #Hrpc : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hhttp : (isPkgInit (PROP := IProp GF) pkg_id.net.http) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 0 (by decide) $$ [Hboot Hsh Hx]
  · iframe #
    iframe Hboot Hsh Hx
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end gryff.examples.gryffnet.cmd.server1

namespace gryff.examples.gryffnet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]
    (wp_Server : gryffnet.Server.spec (GF := GF) (hG := hG)) (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.server2 ∗
        serverBoot (GF := GF) ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverShare γ 1 ∗ (if 1 = 0 then iprop(True) else iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph)) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hboot, %Hb, Hsh, Hx⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  ihave #Hrpc : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hhttp : (isPkgInit (PROP := IProp GF) pkg_id.net.http) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 1 (by decide) $$ [Hboot Hsh Hx]
  · iframe #
    iframe Hboot Hsh Hx
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end gryff.examples.gryffnet.cmd.server2

namespace gryff.examples.gryffnet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]
    (wp_Server : gryffnet.Server.spec (GF := GF) (hG := hG)) (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.server3 ∗
        serverBoot (GF := GF) ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverShare γ 2 ∗ (if 2 = 0 then iprop(True) else iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph)) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hboot, %Hb, Hsh, Hx⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  ihave #Hrpc : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hhttp : (isPkgInit (PROP := IProp GF) pkg_id.net.http) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 2 (by decide) $$ [Hboot Hsh Hx]
  · iframe #
    iframe Hboot Hsh Hx
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end gryff.examples.gryffnet.cmd.server3

namespace gryff.examples.gryffnet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]
    (wp_Server : gryffnet.Server.spec (GF := GF) (hG := hG)) (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet.cmd.server4 ∗
        serverBoot (GF := GF) ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
        serverShare γ 3 ∗ (if 3 = 0 then iprop(True) else iprop(gryff.boot.gryffGlobals ∗ gryff.boot.bootProph)) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hboot, %Hb, Hsh, Hx⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet) $$ []
  · iPkgInit
  ihave #Hrpc : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hhttp : (isPkgInit (PROP := IProp GF) pkg_id.net.http) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ 3 (by decide) $$ [Hboot Hsh Hx]
  · iframe #
    iframe Hboot Hsh Hx
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end gryff.examples.gryffnet.cmd.server4

end Perennial
