/-
The QuePaxa kit's twelve commands' `main`s (`examples/quepaxanet/cmd/*`: `Orch()`, `Client(c)`,
`Server(k)`), each its kit function on its constant, from the kit functions' specs (`Kit.lean`).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.orch.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client0.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client1.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client2.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client3.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client4.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client5.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server1.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server2.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server3.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server4.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server5.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote raxos raxos.pure raxos.examples.quepaxanet

namespace raxos.examples.quepaxanet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Orch : quepaxanet.Orch.spec (GF := GF) (hG := hG)) (γ : QNames)
    (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.orch ∗
        orchRes (Gg := hG.goose_globalGS) γ ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (qR γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) ∗
        pendCtx (Gg := hG.goose_globalGS) (qR γ) (qS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (qS0 (GF := GF)) γp (qS0 (GF := GF)).M.init ∗
        [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 60 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Ho, #Has, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Orch γ γp hrb $$ [Ho Hlib Hbud]
  · iframe #
    iframe Ho Hlib Hbud
  iapply HΦ
  itrivial

end proof

end raxos.examples.quepaxanet.cmd.orch

namespace raxos.examples.quepaxanet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Client : quepaxanet.Client.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client0 ∗
        clientRes (Gg := hG.goose_globalGS) γ 0 ∗
        remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD 0 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hc, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 0) (by decide) $$ [Hc] as %hf
  · rw [show uint.nat (W64 0) = 0 from rfl]
    iframe #
    iframe Hc
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.client0

namespace raxos.examples.quepaxanet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Client : quepaxanet.Client.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client1 ∗
        clientRes (Gg := hG.goose_globalGS) γ 1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD 1 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hc, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 1) (by decide) $$ [Hc] as %hf
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe Hc
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.client1

namespace raxos.examples.quepaxanet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Client : quepaxanet.Client.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client2 ∗
        clientRes (Gg := hG.goose_globalGS) γ 2 ∗
        remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD 2 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hc, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 2) (by decide) $$ [Hc] as %hf
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe Hc
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.client2

namespace raxos.examples.quepaxanet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Client : quepaxanet.Client.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client3 ∗
        clientRes (Gg := hG.goose_globalGS) γ 3 ∗
        remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD 3 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hc, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 3) (by decide) $$ [Hc] as %hf
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe Hc
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.client3

namespace raxos.examples.quepaxanet.cmd.client4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client4.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Client : quepaxanet.Client.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client4 ∗
        clientRes (Gg := hG.goose_globalGS) γ 4 ∗
        remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD 4 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hc, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 4) (by decide) $$ [Hc] as %hf
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
    iframe Hc
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.client4

namespace raxos.examples.quepaxanet.cmd.client5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client5.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Client : quepaxanet.Client.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client5 ∗
        clientRes (Gg := hG.goose_globalGS) γ 5 ∗
        remoteAddr (Gg := hG.goose_globalGS) (qR γ) (clientAddrs.getD 5 []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := QIn) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hc, #Hra, #Hmap⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γ (W64 5) (by decide) $$ [Hc] as %hf
  · rw [show uint.nat (W64 5) = 5 from rfl]
    iframe #
    iframe Hc
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.client5

namespace raxos.examples.quepaxanet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Server : quepaxanet.Server.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.server1 ∗
        serverRes (Gg := hG.goose_globalGS) γ 1 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 1) (by decide) $$ [Hs] as %hf
  · rw [show uint.nat (W64 1) = 1 from rfl]
    iframe #
    iframe Hs
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.server1

namespace raxos.examples.quepaxanet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Server : quepaxanet.Server.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.server2 ∗
        serverRes (Gg := hG.goose_globalGS) γ 2 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 2) (by decide) $$ [Hs] as %hf
  · rw [show uint.nat (W64 2) = 2 from rfl]
    iframe #
    iframe Hs
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.server2

namespace raxos.examples.quepaxanet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Server : quepaxanet.Server.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.server3 ∗
        serverRes (Gg := hG.goose_globalGS) γ 3 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 3) (by decide) $$ [Hs] as %hf
  · rw [show uint.nat (W64 3) = 3 from rfl]
    iframe #
    iframe Hs
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.server3

namespace raxos.examples.quepaxanet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Server : quepaxanet.Server.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.server4 ∗
        serverRes (Gg := hG.goose_globalGS) γ 4 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 4) (by decide) $$ [Hs] as %hf
  · rw [show uint.nat (W64 4) = 4 from rfl]
    iframe #
    iframe Hs
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.server4

namespace raxos.examples.quepaxanet.cmd.server5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server5.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

theorem wp_main (wp_Server : quepaxanet.Server.spec (GF := GF) (hG := hG)) (γ : QNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.server5 ∗
        serverRes (Gg := hG.goose_globalGS) γ 5 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γ (W64 5) (by decide) $$ [Hs] as %hf
  · rw [show uint.nat (W64 5) = 5 from rfl]
    iframe #
    iframe Hs
  exact hf.elim

end proof

end raxos.examples.quepaxanet.cmd.server5

end Perennial
