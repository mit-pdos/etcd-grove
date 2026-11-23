/-
The kit's net/rpc services as Net's `MethodSpec`s (`Net/Proof/net/rpc/Proto.lean`), over rpcgen's
bytes (`NetRpc/Wire.lean`): the master's `"Master"` service (`Register`, and `GetLeader`,
`GetReplicaList`, which no node of the kit calls) and a replica's `"Replica"` service
(`BeTheLeader`, `Ping`), and the run's rpc world `rpcSS` (the lab's `Interface/MasterSpec.lean`,
"Method specs", restated: the lab's `RpcVal` bytes are rpcgen's here, and the ports the kit's).

Each method spec also accepts any error answer (`∀ msg, msg ≠ [] → Φ [] msg`, a conjunct the
server chooses): no caller in the kit needs anything from a failed call (the master's `run`
marks a replica dead or logs, `register` dials again), and so each service meets Net's `errOk`
(`masterSvc_errOk`, `replicaSvc_errOk`) as it stands (every non-empty message), not only its
coming restriction to the server's own messages (`srvErrMsg`, #24).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Codec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Registry
public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos

/-- Replica node `k`'s port (server `k` at `7500 + k`), as `serve` passes it to `register`. -/
def portOf (k : Nat) : w64 := W64 (7500 + (k : Int))

/-- The arguments replica node `k` registers (`register(ip, port, ...)`'s `RegisterArgs`). -/
def regArgsOf (k : Nat) : List w8 := encRegisterArgs (replicaIp k) (portOf k)

/-- What the master sends for `BeTheLeader` (`&defs.BeTheLeaderArgs{}`). -/
def btlArgsBytes : List w8 := encBtlArgs

/-- What `Replica.BeTheLeader` replies: the zero `BeTheLeaderReply` (`NewReply()`'s; the method
sets no field). -/
def btlReplyBytes : List w8 := encBtlReply (W32 0) (W32 0)

/-- What the master sends for `Ping` (`&defs.PingArgs{}`). -/
def pingArgsBytes : List w8 := encPingArgs (W8 0)

/-- What `Replica.Ping` replies. -/
def pingReplyBytes : List w8 := encPingReply

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What a reply to replica node `k`'s registration says: when `Ready`, the final list is its
`NodeList` and `peerAddrOf k` is at its `ReplicaId`. -/
def regReplyOk (γ : EpNames) (k : Nat) (id : w64) (nl : List GoString) (ready : Bool) :
    IProp GF :=
  if ready then
    iprop(listFinal γ nl ∗ ⌜nl[uint.nat id]? = some (peerAddrOf k)⌝)
  else iprop(True)

instance regReplyOk_persistent (γ : EpNames) (k : Nat) (id : w64) (nl : List GoString)
    (ready : Bool) : Persistent (regReplyOk (GF := GF) γ k id nl ready) := by
  unfold regReplyOk; split <;> infer_instance

/-- An error answer: any non-empty message. -/
def errAns (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg)

/-- `Master.Register`: the caller is replica node `k` with its configured address; the master
answers a reply as `regReplyOk` says (or an error). -/
def registerSpec (γ : EpNames) (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    IProp GF :=
  iprop(∃ k : Nat, ⌜k ∈ replicaNodes ∧ args = regArgsOf k⌝ ∗
    ((∀ (id : w64) (nl : List GoString) (ready il : Bool), regReplyOk γ k id nl ready -∗
        Φ (encRegisterReply id nl ready il) []) ∧ errAns Φ))

/-- A method no node calls (`GetLeader`, `GetReplicaList`): on its (empty) arguments `a0` (the
receiver decodes only bytes of the argument's type: `rpcDecode` panics on another type's), any
reply, any message. -/
def anySpec (a0 args : List w8) (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(⌜args = a0⌝ ∗ ∀ (rep : List w8) (msg : GoString), Φ rep msg)

/-- The `Master` service. -/
def masterSvc (γ : EpNames) : net.rpc.MethodSpec GF := fun m args Φ =>
  if m = go!"Register" then registerSpec γ args Φ
  else if m = go!"GetLeader" then anySpec encGetLeaderArgs args Φ
  else if m = go!"GetReplicaList" then anySpec encGetReplicaListArgs args Φ
  else iprop(False)

/-- `Replica.BeTheLeader`: on the master's (empty) arguments, the zero reply (or an error). -/
def btlSpec (args : List w8) (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(⌜args = btlArgsBytes⌝ ∗ (Φ btlReplyBytes [] ∧ errAns Φ))

/-- `Replica.Ping`: on the master's (zero) arguments, the empty reply (or an error). -/
def pingSpec (args : List w8) (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(⌜args = pingArgsBytes⌝ ∗ (Φ pingReplyBytes [] ∧ errAns Φ))

/-- The `Replica` service (the same at every replica's rpc address). -/
def replicaSvc : net.rpc.MethodSpec GF := fun m args Φ =>
  if m = go!"BeTheLeader" then btlSpec args Φ
  else if m = go!"Ping" then pingSpec args Φ
  else iprop(False)

/-- The services of the run's rpc addresses: `"Master"` at the master's, `"Replica"` at each
replica's rpc address. -/
def rpcSS (γ : EpNames) (a svc : GoString) : Option (net.rpc.MethodSpec GF) :=
  if a = masterAddr ∧ svc = go!"Master" then some (masterSvc γ)
  else if a ∈ replicaRpcAddrs ∧ svc = go!"Replica" then some replicaSvc
  else none

theorem rpcSS_master (γ : EpNames) :
    rpcSS (GF := GF) γ masterAddr go!"Master" = some (masterSvc γ) := by
  simp [rpcSS]

/-- The replicas' rpc addresses, spelled out. -/
theorem replicaRpcAddrs_lit :
    replicaRpcAddrs = [go!"127.0.0.1:8502", go!"127.0.0.1:8503", go!"127.0.0.1:8504",
      go!"127.0.0.1:8505", go!"127.0.0.1:8506"] := by
  simp [replicaRpcAddrs, replicaNodes, rpcAddrOf, replicaIp, fmt.decimal, fmt.decimalNat_of_ge,
    fmt.decimalNat_of_lt, fmt.digitByte]

theorem rpcAddrOf_mem (k : Nat) (hk : k ∈ replicaNodes) : rpcAddrOf k ∈ replicaRpcAddrs :=
  List.mem_map_of_mem hk

theorem masterAddr_not_replicaRpc : masterAddr ∉ replicaRpcAddrs := by
  rw [replicaRpcAddrs_lit]; decide

theorem rpcSS_replica (γ : EpNames) (k : Nat) (hk : k ∈ replicaNodes) :
    rpcSS (GF := GF) γ (rpcAddrOf k) go!"Replica" = some replicaSvc := by
  have hm := rpcAddrOf_mem k hk
  have hne : rpcAddrOf k ≠ masterAddr := fun h => masterAddr_not_replicaRpc (h ▸ hm)
  simp [rpcSS, hne, hm]

/-- The master's address offers only `"Master"`, a replica's rpc address only `"Replica"`
(what `srvServes` asks of a server's registrations). -/
theorem rpcSS_only (γ : EpNames) (a svc : GoString) (S : net.rpc.MethodSpec GF)
    (h : rpcSS γ a svc = some S) :
    (a = masterAddr ∧ svc = go!"Master" ∧ S = masterSvc γ) ∨
    (a ∈ replicaRpcAddrs ∧ svc = go!"Replica" ∧ S = replicaSvc) := by
  unfold rpcSS at h
  by_cases h1 : a = masterAddr ∧ svc = go!"Master"
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at h
    left; exact ⟨h1.1, h1.2, (Option.some.inj h).symm⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
    by_cases h2 : a ∈ replicaRpcAddrs ∧ svc = go!"Replica"
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at h
      right; exact ⟨h2.1, h2.2, (Option.some.inj h).symm⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at h
      exact absurd h (by simp)

end specs

/-! ## Error answers (Net's `errOk`) -/

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem masterSvc_errOk (γ : EpNames) : ⊢ net.rpc.errOk (GF := GF) (masterSvc γ) := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %hmsg HS
  unfold masterSvc
  split
  · unfold registerSpec errAns
    icases HS with ⟨%k, %_, ⟨-, HE⟩⟩
    imodintro
    iapply HE
    ipureintro; exact hmsg
  · split
    · unfold anySpec
      icases HS with ⟨-, HS⟩
      imodintro
      iapply HS
    · split
      · unfold anySpec
        icases HS with ⟨-, HS⟩
        imodintro
        iapply HS
      · iexfalso; iexact HS

theorem replicaSvc_errOk : ⊢ net.rpc.errOk (GF := GF) replicaSvc := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %hmsg HS
  unfold replicaSvc
  split
  · unfold btlSpec errAns
    icases HS with ⟨%_, ⟨-, HE⟩⟩
    imodintro
    iapply HE
    ipureintro; exact hmsg
  · split
    · unfold pingSpec errAns
      icases HS with ⟨%_, ⟨-, HE⟩⟩
      imodintro
      iapply HE
      ipureintro; exact hmsg
    · iexfalso; iexact HS

end errs

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial
