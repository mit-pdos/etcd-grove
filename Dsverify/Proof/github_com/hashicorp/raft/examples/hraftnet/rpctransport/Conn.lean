/-
The vocabulary of `rpctransport.Conn`'s specs (the hraft kit transport, notes/dsv-hraft.md, S4): a
connection to the net/rpc server at an address `a` of the rpc world `W` (`isConn`), whose mutex
holds its client (`connInv`: none, or a client of `a`, Net's `isClient`); and the package
variables the dial reads (`dialEnv`), from the package's facts.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Base
public import Net.Proof.net.rpc.ClientDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- The mutex of the `*Conn` `p` holds its client: none, or a client of `a` in `W`. -/
def connInv (W : net.rpc.RpcWorld GF) (a : GoString) (p : Loc) : IProp GF :=
  iprop(∃ c : Loc, structFieldRef Conn go!"c" p ↦ c ∗ (⌜c = null⌝ ∨ net.rpc.isClient c W a))

/-- `p` is a connection to the net/rpc server at `a` of the rpc world `W` (persistent): its
address, its mutex, the address's rpc protocol (`rpcAddr`, for the dial) and the receipt bound
`NewClient` needs. -/
def isConn (p : Loc) (W : net.rpc.RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(structFieldRef Conn go!"addr" p ↦□ a ∗
    sync.isMutex (structFieldRef Conn go!"mu" p) (connInv W a p) ∗
    net.rpc.rpcAddr (Gg := hG.goose_globalGS) W a ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝)

instance isConn_persistent (p : Loc) (W : net.rpc.RpcWorld GF) (a : GoString) :
    Persistent (isConn (GF := GF) p W a) := by
  unfold isConn; infer_instance

/-- The package variables a dial reads (persistent): `net`'s `errTimeout` and
`poll.ErrDeadlineExceeded`, net/rpc's client variables (`cliEnv`), and the packages' facts. -/
def dialEnv : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.time ∗ net.rpc.cliEnv ∗
    (∃ et : GoInterface, globalAddr net.errTimeout ↦□ et) ∗
    (∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed))

instance dialEnv_persistent : Persistent (dialEnv (GF := GF)) := by
  unfold dialEnv; infer_instance

/-- Two `isChan` of one channel agree on its capacity (as in Net's `Client.Call` proof). -/
theorem isChan_cap_agree (ch : Loc) (γ1 γ2 : ChanNames) :
    isChan (GF := GF) ch γ1 Loc ∗ isChan ch γ2 Loc ⊢ ⌜γ1.chanCap = γ2.chanCap⌝ := by
  rw [isChan_unseal]
  unfold isChanDef
  iintro ⟨⟨%m1, #Hc1, -⟩, ⟨%m2, #Hc2, -⟩⟩
  icombine Hc1 Hc2 gives %H
  ipureintro; exact H

variable [package_sem : Assumptions]

/-- The dial's environment, from the package's facts (its imports': net/rpc's `srvEnv`, `net`'s). -/
theorem dialEnv_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ⊢
      dialEnv (GF := GF) := by
  iintro #Hpkg
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · iPkgInit
  ihave #Hi := net.rpc.rpcInit_access $$ Hrpc
  iunfold net.rpc.rpcInit at Hi
  icases Hi with ⟨-, #Hse, -, -⟩
  iunfold net.rpc.srvEnv at Hse
  icases Hse with ⟨#Hce, -⟩
  ihave #Hni : net.isInit $$ []
  · with_unfolding_all iapply isPkgInit_access (PROP := IProp GF) pkg_id.net $$ Hnet
  icases Hni with ⟨-, -, %et, #Het⟩
  ihave #Hce' := Hce
  iunfold net.rpc.cliEnv at Hce'
  icases Hce' with ⟨%eof, %ueof, %ed, -, -, -, -, #Hed, -⟩
  unfold dialEnv
  iframe Hnet Hsync Htime Hce
  isplitr
  · iexists _; iexact Het
  · iexists _; iexact Hed

end defs

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
