/-
The vr kit's twelve commands' `main`s (`examples/vsrnet/cmd/*`, notes/dsv-vr.md), each its kit
function on its constant, from the kit functions' specs (`Orch.spec`, `Client.spec`,
`Server.spec`), as paxos's `Mains.lean`. Each `wp_main`'s precondition is its function's, which the
start (`Start.lean`) gives, and, for a client or a server, encoding/json's fresh registry
(`codecFresh`, which the machine's boot returns: `BootCmdsLinked.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ClientProofDefs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ServerProofDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost
open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.tangledbytes.go_vsr.examples.vsrnet

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Orch : vsrnet.Orch.spec (GF := GF) (hG := hG)) (γ : Names) (γp : PendNames)
    (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch ∗
        sysInv (G := hG.goose_globalGS) γ ∗ sizeTok γ ∗ confProtos (G := hG.goose_globalGS) γ ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (kvR γ.gn) (kvS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
        [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 24 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hsys, Hsize, #Hcp, #Has, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γp hrb $$ [Hsize Hlib Hbud]
  · iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Client : vsrnet.Client.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0 ∗
        confProtos (G := hG.goose_globalGS) γ ∗ pkg.network.netProtos γ ∗
        sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
        nextReq (G := hG.goose_globalGS) γ (0 + 1) 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD 0 []) ∗
        ⌜ρ.bud (clientAddrs.getD 0 []) = some 24⌝ ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcp, #Hnp, #Hsys, #Hreg, Hnext, #Hra, #Hbud, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 0 (by decide) $$ [Hnext Hfr] as %hf
  · iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Client : vsrnet.Client.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1 ∗
        confProtos (G := hG.goose_globalGS) γ ∗ pkg.network.netProtos γ ∗
        sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
        nextReq (G := hG.goose_globalGS) γ (1 + 1) 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD 1 []) ∗
        ⌜ρ.bud (clientAddrs.getD 1 []) = some 24⌝ ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcp, #Hnp, #Hsys, #Hreg, Hnext, #Hra, #Hbud, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 1 (by decide) $$ [Hnext Hfr] as %hf
  · iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Client : vsrnet.Client.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2 ∗
        confProtos (G := hG.goose_globalGS) γ ∗ pkg.network.netProtos γ ∗
        sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
        nextReq (G := hG.goose_globalGS) γ (2 + 1) 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD 2 []) ∗
        ⌜ρ.bud (clientAddrs.getD 2 []) = some 24⌝ ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcp, #Hnp, #Hsys, #Hreg, Hnext, #Hra, #Hbud, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 2 (by decide) $$ [Hnext Hfr] as %hf
  · iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Client : vsrnet.Client.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3 ∗
        confProtos (G := hG.goose_globalGS) γ ∗ pkg.network.netProtos γ ∗
        sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
        nextReq (G := hG.goose_globalGS) γ (3 + 1) 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD 3 []) ∗
        ⌜ρ.bud (clientAddrs.getD 3 []) = some 24⌝ ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcp, #Hnp, #Hsys, #Hreg, Hnext, #Hra, #Hbud, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 3 (by decide) $$ [Hnext Hfr] as %hf
  · iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Client : vsrnet.Client.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4 ∗
        confProtos (G := hG.goose_globalGS) γ ∗ pkg.network.netProtos γ ∗
        sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
        nextReq (G := hG.goose_globalGS) γ (4 + 1) 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD 4 []) ∗
        ⌜ρ.bud (clientAddrs.getD 4 []) = some 24⌝ ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcp, #Hnp, #Hsys, #Hreg, Hnext, #Hra, #Hbud, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 4 (by decide) $$ [Hnext Hfr] as %hf
  · iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client5.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Client : vsrnet.Client.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5 ∗
        confProtos (G := hG.goose_globalGS) γ ∗ pkg.network.netProtos γ ∗
        sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
        nextReq (G := hG.goose_globalGS) γ (5 + 1) 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD 5 []) ∗
        ⌜ρ.bud (clientAddrs.getD 5 []) = some 24⌝ ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcp, #Hnp, #Hsys, #Hreg, Hnext, #Hra, #Hbud, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ 5 (by decide) $$ [Hnext Hfr] as %hf
  · iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Server : vsrnet.Server.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1 ∗
        srvShare (G := hG.goose_globalGS) γ 1 ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 1) (by decide) $$ [Hsh Hfr] as %hf
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Server : vsrnet.Server.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2 ∗
        srvShare (G := hG.goose_globalGS) γ 2 ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 2) (by decide) $$ [Hsh Hfr] as %hf
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Server : vsrnet.Server.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3 ∗
        srvShare (G := hG.goose_globalGS) γ 3 ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 3) (by decide) $$ [Hsh Hfr] as %hf
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Server : vsrnet.Server.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4 ∗
        srvShare (G := hG.goose_globalGS) γ 4 ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 4) (by decide) $$ [Hsh Hfr] as %hf
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4

namespace github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server5.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

theorem wp_main (wp_Server : vsrnet.Server.spec (GF := GF) (hG := hG)) (γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5 ∗
        srvShare (G := hG.goose_globalGS) γ 5 ∗ encoding.json.codecFresh (GF := GF) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hfr⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 5) (by decide) $$ [Hsh Hfr] as %hf
  · rw [show uint.nat (W64 5) = 5 from rfl]
    iframe #
    iframe
  exact hf.elim

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5

end Perennial
