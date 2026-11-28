/-
The hraft kit's twelve commands' `main`s (`examples/hraftnet/cmd/*`), each its kit function on its
constant (`Orch()`, `Client(c)`, `Server(j)`), from the kit functions' specs, as craq's `Mains.lean`:
each from its share of the start (`Start.lean`) and net/rpc's codec unregistered (its boot's,
`BootCmdsLinked.lean`); a server's also from its main thread's token. The packages' facts the
callees take (`hraftnet`'s, `sync`'s, net/rpc's mutex and server variables, `log`'s) follow from the
command's.
-/
module
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.orch.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.client0.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.client1.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.client2.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.client3.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.client4.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.server1.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.server2.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.server3.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.server4.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.server5.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.cmd.server6.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Start
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Orch
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Client
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Server
public import Net.Proof.net.rpc.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.hashicorp.raft.examples.hraftnet

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.orch

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions]
variable [π : NetProtoGS]

variable [ρ : RemoteGS] [hRB : ReceiptBoundLe GF (2 ^ 62)]

theorem wp_main (wp_Orch : github_com.hashicorp.raft.examples.hraftnet.Orch.spec (GF := GF) (hG := hG)) (K : HK GF) (γp : PendNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.orch ∗ orchShare K γp ∗ net.rpc.codecUnset }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, -, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Orch K γp $$ [Hsh Hcu]
  · iframe #
    iframe Hcu Hsh
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.orch

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.client0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client0.Assumptions]
variable [π : NetProtoGS]

variable [ρ : RemoteGS]

theorem wp_main (wp_Client : github_com.hashicorp.raft.examples.hraftnet.Client.spec (GF := GF) (hG := hG)) (K : HK GF)
    (hrb : receiptBound GF ≤ 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.client0 ∗ cliShare K 0 ∗ net.rpc.codecUnset }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, -, -, #Hmu⟩
  iunfold cliShare at Hsh
  icases Hsh with ⟨%hss, #Hdi, #Hid, Hseq, #Hra, #Hrem, %hbud⟩
  (try wp_auto)
  wp_apply wp_Client K 0 orchBud (by decide) (by decide) $$ [Hseq Hcu] as %hF
  · iframe #
    iframe Hcu Hseq
    ipureintro; exact ⟨hss, hbud, hrb⟩
  exact hF.elim

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.client0

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.client1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions]
variable [π : NetProtoGS]

variable [ρ : RemoteGS]

theorem wp_main (wp_Client : github_com.hashicorp.raft.examples.hraftnet.Client.spec (GF := GF) (hG := hG)) (K : HK GF)
    (hrb : receiptBound GF ≤ 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.client1 ∗ cliShare K 1 ∗ net.rpc.codecUnset }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, -, -, #Hmu⟩
  iunfold cliShare at Hsh
  icases Hsh with ⟨%hss, #Hdi, #Hid, Hseq, #Hra, #Hrem, %hbud⟩
  (try wp_auto)
  wp_apply wp_Client K 1 orchBud (by decide) (by decide) $$ [Hseq Hcu] as %hF
  · iframe #
    iframe Hcu Hseq
    ipureintro; exact ⟨hss, hbud, hrb⟩
  exact hF.elim

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.client1

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.client2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client2.Assumptions]
variable [π : NetProtoGS]

variable [ρ : RemoteGS]

theorem wp_main (wp_Client : github_com.hashicorp.raft.examples.hraftnet.Client.spec (GF := GF) (hG := hG)) (K : HK GF)
    (hrb : receiptBound GF ≤ 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.client2 ∗ cliShare K 2 ∗ net.rpc.codecUnset }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, -, -, #Hmu⟩
  iunfold cliShare at Hsh
  icases Hsh with ⟨%hss, #Hdi, #Hid, Hseq, #Hra, #Hrem, %hbud⟩
  (try wp_auto)
  wp_apply wp_Client K 2 orchBud (by decide) (by decide) $$ [Hseq Hcu] as %hF
  · iframe #
    iframe Hcu Hseq
    ipureintro; exact ⟨hss, hbud, hrb⟩
  exact hF.elim

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.client2

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.client3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client3.Assumptions]
variable [π : NetProtoGS]

variable [ρ : RemoteGS]

theorem wp_main (wp_Client : github_com.hashicorp.raft.examples.hraftnet.Client.spec (GF := GF) (hG := hG)) (K : HK GF)
    (hrb : receiptBound GF ≤ 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.client3 ∗ cliShare K 3 ∗ net.rpc.codecUnset }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, -, -, #Hmu⟩
  iunfold cliShare at Hsh
  icases Hsh with ⟨%hss, #Hdi, #Hid, Hseq, #Hra, #Hrem, %hbud⟩
  (try wp_auto)
  wp_apply wp_Client K 3 orchBud (by decide) (by decide) $$ [Hseq Hcu] as %hF
  · iframe #
    iframe Hcu Hseq
    ipureintro; exact ⟨hss, hbud, hrb⟩
  exact hF.elim

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.client3

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.client4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client4.Assumptions]
variable [π : NetProtoGS]

variable [ρ : RemoteGS]

theorem wp_main (wp_Client : github_com.hashicorp.raft.examples.hraftnet.Client.spec (GF := GF) (hG := hG)) (K : HK GF)
    (hrb : receiptBound GF ≤ 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.client4 ∗ cliShare K 4 ∗ net.rpc.codecUnset }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, -, -, #Hmu⟩
  iunfold cliShare at Hsh
  icases Hsh with ⟨%hss, #Hdi, #Hid, Hseq, #Hra, #Hrem, %hbud⟩
  (try wp_auto)
  wp_apply wp_Client K 4 orchBud (by decide) (by decide) $$ [Hseq Hcu] as %hF
  · iframe #
    iframe Hcu Hseq
    ipureintro; exact ⟨hss, hbud, hrb⟩
  exact hF.elim

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.client4

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.server1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server1.Assumptions]
variable [π : NetProtoGS]

theorem wp_main (wp_Server : github_com.hashicorp.raft.examples.hraftnet.Server.spec (GF := GF) (hG := hG))
    [htb : ThreadBoundLe GF (2 ^ 28)] (K : HK GF)
    (hb : receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.server1 ∗ srvShare K 1 ∗ net.rpc.codecUnset ∗
        threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu, Htok⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hse, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Server htb K 1 (by omega) (by omega) $$ [Hsh Hcu Htok]
  · iframe #
    iframe Hsh Htok
    isplitl [Hcu]
    · unfold srvBoot
      iframe Hmu Hcu Hse Hlog
    ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.server1

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.server2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server2.Assumptions]
variable [π : NetProtoGS]

theorem wp_main (wp_Server : github_com.hashicorp.raft.examples.hraftnet.Server.spec (GF := GF) (hG := hG))
    [htb : ThreadBoundLe GF (2 ^ 28)] (K : HK GF)
    (hb : receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.server2 ∗ srvShare K 2 ∗ net.rpc.codecUnset ∗
        threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu, Htok⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hse, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Server htb K 2 (by omega) (by omega) $$ [Hsh Hcu Htok]
  · iframe #
    iframe Hsh Htok
    isplitl [Hcu]
    · unfold srvBoot
      iframe Hmu Hcu Hse Hlog
    ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.server2

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.server3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server3.Assumptions]
variable [π : NetProtoGS]

theorem wp_main (wp_Server : github_com.hashicorp.raft.examples.hraftnet.Server.spec (GF := GF) (hG := hG))
    [htb : ThreadBoundLe GF (2 ^ 28)] (K : HK GF)
    (hb : receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.server3 ∗ srvShare K 3 ∗ net.rpc.codecUnset ∗
        threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu, Htok⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hse, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Server htb K 3 (by omega) (by omega) $$ [Hsh Hcu Htok]
  · iframe #
    iframe Hsh Htok
    isplitl [Hcu]
    · unfold srvBoot
      iframe Hmu Hcu Hse Hlog
    ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.server3

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.server4

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server4.Assumptions]
variable [π : NetProtoGS]

theorem wp_main (wp_Server : github_com.hashicorp.raft.examples.hraftnet.Server.spec (GF := GF) (hG := hG))
    [htb : ThreadBoundLe GF (2 ^ 28)] (K : HK GF)
    (hb : receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.server4 ∗ srvShare K 4 ∗ net.rpc.codecUnset ∗
        threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu, Htok⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hse, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Server htb K 4 (by omega) (by omega) $$ [Hsh Hcu Htok]
  · iframe #
    iframe Hsh Htok
    isplitl [Hcu]
    · unfold srvBoot
      iframe Hmu Hcu Hse Hlog
    ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.server4

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.server5

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server5.Assumptions]
variable [π : NetProtoGS]

theorem wp_main (wp_Server : github_com.hashicorp.raft.examples.hraftnet.Server.spec (GF := GF) (hG := hG))
    [htb : ThreadBoundLe GF (2 ^ 28)] (K : HK GF)
    (hb : receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.server5 ∗ srvShare K 5 ∗ net.rpc.codecUnset ∗
        threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu, Htok⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hse, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Server htb K 5 (by omega) (by omega) $$ [Hsh Hcu Htok]
  · iframe #
    iframe Hsh Htok
    isplitl [Hcu]
    · unfold srvBoot
      iframe Hmu Hcu Hse Hlog
    ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.server5

namespace github_com.hashicorp.raft.examples.hraftnet.cmd.server6

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server6.Assumptions]
variable [π : NetProtoGS]

theorem wp_main (wp_Server : github_com.hashicorp.raft.examples.hraftnet.Server.spec (GF := GF) (hG := hG))
    [htb : ThreadBoundLe GF (2 ^ 28)] (K : HK GF)
    (hb : receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.cmd.server6 ∗ srvShare K 6 ∗ net.rpc.codecUnset ∗
        threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hsh, Hcu, Htok⟩
  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hrp : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hse, -, #Hmu⟩
  (try wp_auto)
  wp_apply wp_Server htb K 6 (by omega) (by omega) $$ [Hsh Hcu Htok]
  · iframe #
    iframe Hsh Htok
    isplitl [Hcu]
    · unfold srvBoot
      iframe Hmu Hcu Hse Hlog
    ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet.cmd.server6

end Perennial
