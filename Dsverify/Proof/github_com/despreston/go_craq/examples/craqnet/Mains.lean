/-
The craq kit's twelve commands' `main`s (`examples/craqnet/cmd/*`), each its kit function on its
constant, from the kit functions' specs (`KitSpecs.lean`), as paxos's `Mains.lean`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.orch.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client0.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client1.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client2.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client3.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client4.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server1.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server2.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server3.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server4.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server5.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server6.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitSpecs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.despreston.go_craq
  github_com.despreston.go_craq.examples.craqnet

namespace github_com.despreston.go_craq.examples.craqnet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main (wp_Orch : craqnet.Orch.spec (GF := GF) (hG := hG)) (γ : CraqNames)
    (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.orch ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (kvR γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
        [∗list] a ∈ confAddrs, addrProto (Gg := hG.goose_globalGS) a confProto confProto }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Has, #Hmap, #Hpend, Hlib, #Hcp⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γp hrb $$ [Hlib]
  · iframe #
    iframe Hlib
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.orch

namespace github_com.despreston.go_craq.examples.craqnet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main (wp_Client : craqnet.Client.spec (GF := GF) (hG := hG)) (cfg : Cfg GF)
    (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client0 ∗ craqCtx cfg ∗ codecFresh ∗
        addrProto (Gg := hG.goose_globalGS) (confAddrs.getD 0 []) confProto confProto ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR cfg.γ) (clientAddrs.getD 0 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hctx, Hcf, #Hca, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client cfg (W64 0) hcfg (by decide) $$ [Hcf] as %hf
  · rw [show uint.nat (W64 0) = 0 from rfl]
    iframe #
    iframe Hcf
  exact hf.elim

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.client0

namespace github_com.despreston.go_craq.examples.craqnet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main (wp_Client : craqnet.Client.spec (GF := GF) (hG := hG)) (cfg : Cfg GF)
    (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client1 ∗ craqCtx cfg ∗ codecFresh ∗
        addrProto (Gg := hG.goose_globalGS) (confAddrs.getD 1 []) confProto confProto ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR cfg.γ) (clientAddrs.getD 1 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hctx, Hcf, #Hca, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client cfg (W64 1) hcfg (by decide) $$ [Hcf] as %hf
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe Hcf
  exact hf.elim

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.client1

namespace github_com.despreston.go_craq.examples.craqnet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main (wp_Client : craqnet.Client.spec (GF := GF) (hG := hG)) (cfg : Cfg GF)
    (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client2 ∗ craqCtx cfg ∗ codecFresh ∗
        addrProto (Gg := hG.goose_globalGS) (confAddrs.getD 2 []) confProto confProto ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR cfg.γ) (clientAddrs.getD 2 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hctx, Hcf, #Hca, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client cfg (W64 2) hcfg (by decide) $$ [Hcf] as %hf
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe Hcf
  exact hf.elim

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.client2

namespace github_com.despreston.go_craq.examples.craqnet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main (wp_Client : craqnet.Client.spec (GF := GF) (hG := hG)) (cfg : Cfg GF)
    (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client3 ∗ craqCtx cfg ∗ codecFresh ∗
        addrProto (Gg := hG.goose_globalGS) (confAddrs.getD 3 []) confProto confProto ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR cfg.γ) (clientAddrs.getD 3 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hctx, Hcf, #Hca, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client cfg (W64 3) hcfg (by decide) $$ [Hcf] as %hf
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe Hcf
  exact hf.elim

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.client3

namespace github_com.despreston.go_craq.examples.craqnet.cmd.client4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main (wp_Client : craqnet.Client.spec (GF := GF) (hG := hG)) (cfg : Cfg GF)
    (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client4 ∗ craqCtx cfg ∗ codecFresh ∗
        addrProto (Gg := hG.goose_globalGS) (confAddrs.getD 4 []) confProto confProto ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR cfg.γ) (clientAddrs.getD 4 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hctx, Hcf, #Hca, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client cfg (W64 4) hcfg (by decide) $$ [Hcf] as %hf
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
    iframe Hcf
  exact hf.elim

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.client4

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main [RpcHttpServe GF] (wp_Server : craqnet.Server.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server1 ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg 1 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server cfg (W64 1) hcfg (by decide) (by decide) $$ [Hcf Hmux Hres]
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.server1

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main [RpcHttpServe GF] (wp_Server : craqnet.Server.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server2 ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg 2 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server cfg (W64 2) hcfg (by decide) (by decide) $$ [Hcf Hmux Hres]
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.server2

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main [RpcHttpServe GF] (wp_Server : craqnet.Server.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server3 ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg 3 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server cfg (W64 3) hcfg (by decide) (by decide) $$ [Hcf Hmux Hres]
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.server3

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main [RpcHttpServe GF] (wp_Server : craqnet.Server.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server4 ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg 4 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server cfg (W64 4) hcfg (by decide) (by decide) $$ [Hcf Hmux Hres]
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.server4

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server5.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main [RpcHttpServe GF] (wp_Server : craqnet.Server.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server5 ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg 5 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server cfg (W64 5) hcfg (by decide) (by decide) $$ [Hcf Hmux Hres]
  · rw [show uint.nat (W64 5) = 5 from rfl]
    iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.server5

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server6

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server6.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [ra : RpcHttpAddr GF]

theorem wp_main [RpcHttpServe GF] (wp_Server : craqnet.Server.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server6 ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
        net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg 6 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hcf, Hmux, #Henv, #Hctx, Hres⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server cfg (W64 6) hcfg (by decide) (by decide) $$ [Hcf Hmux Hres]
  · rw [show uint.nat (W64 6) = 6 from rfl]
    iframe #
    iframe
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet.cmd.server6

end Perennial
