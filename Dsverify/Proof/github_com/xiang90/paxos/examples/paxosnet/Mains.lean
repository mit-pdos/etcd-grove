/-
The paxos kit's ten commands' `main`s (`examples/paxosnet/cmd/*`), each its kit function on its
constants, from the kit functions' specs (`Kit.lean`).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.orch.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.client0.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.client1.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.client2.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.client3.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.server1.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.server2.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.server3.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.server4.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.cmd.server5.Base
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.xiang90.paxos
  github_com.xiang90.paxos.examples.paxosnet

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Orch : paxosnet.Orch.spec (GF := GF) (hG := hG)) (Γ : Names)
    (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.orch ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (woR Γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) ∗
        pendCtx (Gg := hG.goose_globalGS) (woR Γ) (woS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (woS0 (GF := GF)) γp (woS0 (GF := GF)).M.init }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Has, #Hmap, #Hpend, Hlib⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch Γ γp hrb $$ [Hlib]
  · iframe #
    iframe Hlib
  iapply HΦ
  itrivial

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.orch

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Client : paxosnet.Client.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.client0 ∗ isPaxos Γ ∗ allProtos Γ ∗
        clientTok Γ (W64 0) ∗
        remoteAddr (Gg := hG.goose_globalGS) (woR Γ) (clientAddrs.getD 0 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Htok, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client Γ (W64 0) (by decide) $$ [Htok] as %hf
  · rw [show uint.nat (W64 0) = 0 from rfl]
    iframe #
    iframe Htok
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.client0

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Client : paxosnet.Client.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.client1 ∗ isPaxos Γ ∗ allProtos Γ ∗
        clientTok Γ (W64 1) ∗
        remoteAddr (Gg := hG.goose_globalGS) (woR Γ) (clientAddrs.getD 1 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Htok, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client Γ (W64 1) (by decide) $$ [Htok] as %hf
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe Htok
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.client1

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Client : paxosnet.Client.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.client2 ∗ isPaxos Γ ∗ allProtos Γ ∗
        clientTok Γ (W64 2) ∗
        remoteAddr (Gg := hG.goose_globalGS) (woR Γ) (clientAddrs.getD 2 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Htok, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client Γ (W64 2) (by decide) $$ [Htok] as %hf
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe Htok
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.client2

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Client : paxosnet.Client.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.client3 ∗ isPaxos Γ ∗ allProtos Γ ∗
        clientTok Γ (W64 3) ∗
        remoteAddr (Gg := hG.goose_globalGS) (woR Γ) (clientAddrs.getD 3 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Htok, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client Γ (W64 3) (by decide) $$ [Htok] as %hf
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe Htok
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.client3

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Server : paxosnet.Server.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.server1 ∗ isPaxos Γ ∗ allProtos Γ ∗
        (if uint.nat (W64 1) ≤ 3 then stOwn Γ (W64 1) AccState.init else True) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server Γ (W64 1) (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.server1

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Server : paxosnet.Server.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.server2 ∗ isPaxos Γ ∗ allProtos Γ ∗
        (if uint.nat (W64 2) ≤ 3 then stOwn Γ (W64 2) AccState.init else True) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server Γ (W64 2) (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.server2

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Server : paxosnet.Server.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.server3 ∗ isPaxos Γ ∗ allProtos Γ ∗
        (if uint.nat (W64 3) ≤ 3 then stOwn Γ (W64 3) AccState.init else True) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server Γ (W64 3) (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.server3

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Server : paxosnet.Server.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.server4 ∗ isPaxos Γ ∗ allProtos Γ ∗
        (if uint.nat (W64 4) ≤ 3 then stOwn Γ (W64 4) AccState.init else True) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server Γ (W64 4) (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.server4

namespace github_com.xiang90.paxos.examples.paxosnet.cmd.server5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server5.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Server : paxosnet.Server.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet.cmd.server5 ∗ isPaxos Γ ∗ allProtos Γ ∗
        (if uint.nat (W64 5) ≤ 3 then stOwn Γ (W64 5) AccState.init else True) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server Γ (W64 5) (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim

end proof

end github_com.xiang90.paxos.examples.paxosnet.cmd.server5

end Perennial
