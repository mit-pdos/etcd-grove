/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/MasterDefs.lean (run gryff-bump-1,
lab master 915f964; notes/dsv-gryff.md).

The master's representation (U2): the lock invariant of a `*masterlib.Master` (its registration
lists, the registry's authority half) and the persistent facts of a master serving
registrations (`masterReg`).

**The lock invariant** (`masterLockInv δ m`): the registered replica nodes `ks` (distinct, each
below 3, in registration order); `nodeList`, `addrList`, `portList` hold `ks`' `"addr:port"`s,
IPs and ports, in slices of capacity 3 (made with `make(..., 0, 3)`) whose capacity the
invariant owns; the registry's authority half over `ks.map addrOf`. Once the three replicas are
registered (`ks.length = 3`), the fields and the slices are persistent (`dqOf ks`): no
registration changes them any more (every later call finds its address), so the master's `Run`
reads `addrList` and `portList` without the lock, and every `Ready` reply shares `nodeList`.

Port (`Net/`): `masterOkDef` is what `(*Master).Serve`'s `http.Serve(l, nil)` asks
(`RpcHttpHyp.Serve_spec`): the master's listener at `masterRpcLis` (`isListener`, `netLisOn`,
`lisInv`), its rpc protocols (`rpcLisP`) and `DefaultServeMux`'s route of `defaultRPCPath` to the
master's server (`muxHas`, from `Server.HandleHTTP`). `runPre`'s rpc addresses are the replicas'
net/rpc addresses behind the HTTP handshake (`rpcAddrP … (connectReq defaultRPCPath)
connectAns`), with `DialHTTP`'s environment (`dialEnv`), and the codec registered (`codecSet
gryffCodec`).
-/
module

public import Dsverify.Proof.gryff.Server.Deploy
public import Dsverify.Proof.gryff.Shares
public import Dsverify.Proof.gryff.Server.RpcEnv
public import Dsverify.Proof.gryff.Rpc.Codec
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The fraction of the master's registration state: persistent once all three replicas are
registered. -/
def dqOf (ks : List Nat) : DFrac := if ks.length = 3 then DFrac.discard else DFrac.own 1

theorem dqOf_full (ks : List Nat) (h : ks.length = 3) : dqOf ks = DFrac.discard := by
  unfold dqOf; rw [if_pos h]

theorem dqOf_open (ks : List Nat) (h : ks.length ≠ 3) : dqOf ks = DFrac.own 1 := by
  unfold dqOf; rw [if_neg h]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The ownership of the slices' capacity, while a registration may still append. -/
def capOwn (ks : List Nat) (nl al pl : GoSlice) : IProp GF :=
  if ks.length = 3 then iprop(True)
  else iprop(ownSliceCap GoString nl (DFrac.own 1) ∗ ownSliceCap GoString al (DFrac.own 1) ∗
    ownSliceCap w64 pl (DFrac.own 1))

theorem capOwn_open (ks : List Nat) (nl al pl : GoSlice) (h : ks.length ≠ 3) :
    capOwn (GF := GF) ks nl al pl ⊣⊢ (ownSliceCap GoString nl (DFrac.own 1) ∗
      ownSliceCap GoString al (DFrac.own 1) ∗ ownSliceCap w64 pl (DFrac.own 1)) := by
  unfold capOwn; rw [if_neg h]; exact .rfl

theorem capOwn_full (ks : List Nat) (nl al pl : GoSlice) (h : ks.length = 3) :
    ⊢ capOwn (GF := GF) ks nl al pl := by
  unfold capOwn; rw [if_pos h]; exact BI.true_intro

/-- The master's lock invariant (see the file header). -/
def masterLockInv (δ : DeployNames) (m : Loc) : IProp GF :=
  iprop(∃ (ks : List Nat) (nl al pl : GoSlice),
    "Hnlf" ∷ structFieldRef src.masterlib.Master go!"nodeList" m ↦{dqOf ks} nl ∗
    "Half" ∷ structFieldRef src.masterlib.Master go!"addrList" m ↦{dqOf ks} al ∗
    "Hplf" ∷ structFieldRef src.masterlib.Master go!"portList" m ↦{dqOf ks} pl ∗
    "Hnl" ∷ nl ↦*{dqOf ks} (ks.map addrOf) ∗
    "Hal" ∷ al ↦*{dqOf ks} (ks.map ipOf) ∗
    "Hpl" ∷ pl ↦*{dqOf ks} (ks.map portNum) ∗
    "Hcap" ∷ capOwn ks nl al pl ∗
    "Hreg" ∷ regAuth δ (1 : Qp).half (ks.map addrOf) ∗
    "%Hks" ∷ ⌜ks.Nodup ∧ (∀ k ∈ ks, k < 3) ∧ sint.Z nl.cap = 3 ∧ sint.Z al.cap = 3 ∧
      sint.Z pl.cap = 3⌝)

/-- A master serving registrations (persistent): `N` is 3, its lock guards `masterLockInv`,
and the registry's invariant. -/
def masterReg (γ : GryffNames GF) (m : Loc) : IProp GF :=
  iprop(∃ lk : Loc,
    "#HN" ∷ structFieldRef src.masterlib.Master go!"N" m ↦□ (W64 3) ∗
    "#Hlk" ∷ structFieldRef src.masterlib.Master go!"lock" m ↦□ lk ∗
    "#Hmu" ∷ sync.isMutex lk (masterLockInv γ.deploy m) ∗
    "#Hdep" ∷ inv deployN (deployInv γ.deploy γ.proto) ∗
    "#Hg" ∷ gryffInv2 γ.proto)

instance masterReg_persistent (γ : GryffNames GF) (m : Loc) :
    Persistent (masterReg γ m) := by
  unfold masterReg; infer_instance

variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]

/-- A master serving registrations on its listener (persistent): what `(*Master).Serve` needs
(see the file header). -/
def masterOkDef (γ : GryffNames GF) (m : Loc) : IProp GF :=
  iprop(∃ (li : GoInterface) (l : w64),
    "#Hreg" ∷ masterReg γ m ∗
    "#Hl" ∷ structFieldRef src.masterlib.Master go!"l" m ↦□ li ∗
    "#Hlis" ∷ net.isListener (GF := GF) li l ∗
    "#Hon" ∷ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l masterRpcLis ∗
    "#Hli" ∷ lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l
      masterRpcLis ∗
    "#Hrl" ∷ RA.rpcLisP γ.rpc masterRpcLis (net.rpc.connectReq net.rpc.defaultRPCPath)
      net.rpc.connectAns ∗
    "#Hmux" ∷ H.muxHas γ.rpc (lisAccepts masterRpcLis) net.rpc.defaultRPCPath ∗
    "#Hhttp" ∷ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
    "%Hth" ∷ ⌜threadBound GF ≤ 2 ^ 31⌝)

instance masterOkDef_persistent (γ : GryffNames GF) (m : Loc) :
    Persistent (masterOkDef γ m) := by
  unfold masterOkDef; infer_instance

/-- Replica node `k`'s net/rpc address as the master dials it (persistent): behind net/rpc's
HTTP handshake. -/
def replicaRpcOk (γ : GryffNames GF) (k : Nat) : IProp GF :=
  net.rpc.rpcAddrP (Gg := hG.goose_globalGS) γ.rpc (replicaRpcAddr k)
    (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns

instance replicaRpcOk_persistent (γ : GryffNames GF) (k : Nat) :
    Persistent (replicaRpcOk γ k) := by
  unfold replicaRpcOk; infer_instance

/-- What the master's `Run` goroutine owns: the replicas' clients, the leader and liveness
flags (`nodes`, `leader`, `alive`: `Run` alone touches them), and what it needs to dial the
replicas' rpc addresses and call their methods. -/
def runPre (γ : GryffNames GF) (m : Loc) : IProp GF :=
  iprop(∃ (nsl lsl asl : GoSlice),
    "#Hreg" ∷ masterReg γ m ∗
    "Hnodes" ∷ structFieldRef src.masterlib.Master go!"nodes" m ↦ nsl ∗
    "Hleader" ∷ structFieldRef src.masterlib.Master go!"leader" m ↦ lsl ∗
    "Halive" ∷ structFieldRef src.masterlib.Master go!"alive" m ↦ asl ∗
    "Hnsl" ∷ nsl ↦* (List.replicate 3 (null : Loc)) ∗
    "Hlsl" ∷ lsl ↦* (List.replicate 3 false) ∗
    "Hasl" ∷ asl ↦* (List.replicate 3 false) ∗
    "#Hcs" ∷ net.rpc.codecSet gryffCodec ∗
    "#Hde" ∷ dialEnv (GF := GF) ∗
    "#Hras" ∷ (□ [∗list] k ∈ [0, 1, 2], replicaRpcOk γ k) ∗
    "%Hw" ∷ ⌜worldOk γ⌝)

end defs

end Perennial.gryff
