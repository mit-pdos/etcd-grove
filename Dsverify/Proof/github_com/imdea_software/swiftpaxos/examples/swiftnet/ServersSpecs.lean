/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ServersSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The internal specs of the server nodes' code in the test package (kit.go): `Addrs`, `host`,
`port`, `at`, `nodeConfig`, `register`, and the hypotheses the server proof takes for callees
with no frozen spec (the test package's initialization; the store to `swift.MaxDescRoutines`,
HUB-REQUEST 2). Internal to the swiftnet group (not frozen).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitLike

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256


/-! ## The deployment's addresses, as kit.go computes them -/

/-- Node `i`'s host, `"10.77.0.(10+i)"` (`i < 13`: two digits). -/
def nodeHost (_i : Nat) : GoString := go!"127.0.0.1"

/-- Node `i`'s first port: `6100 + i` for the orchestrator and the client nodes (`i ≤ 6`),
`7000 + k` for server node `k = i - 6`. -/
def nodePort (i : Nat) : Nat := if i ≤ 6 then 6100 + i else 6994 + i

/-- `at(addrs, i, off)`: node `i`'s host and its first port plus `off`. -/
def atStr (i : Nat) (off : w64) : GoString :=
  nodeHost i ++ go!":" ++ fmt.decimal (uint.Z (W64 (nodePort i) + off))

/-- Server node `j + 1`'s configuration port (node `7 + j`, port `9001 + j`). -/
theorem atStr_conf : ∀ j, j < 6 → confAddrs[j]? = some (atStr (7 + j) (W64 2000)) := by
  intro j h
  match j, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [atStr, nodeHost, nodePort, fmt.decimal, fmt.decimalNat, fmt.digitByte, confAddrs]

/-- Replica node `k`'s rpc port (server node `k + 2`, node `8 + k`, port `8002 + k`). -/
theorem atStr_rpc : ∀ k, k < 5 → replicaRpcAddrs[k]? = some (atStr (8 + k) (W64 1000)) := by
  intro k h
  match k, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [atStr, nodeHost, nodePort, fmt.decimal, fmt.decimalNat, fmt.digitByte, replicaRpcAddrs]

/-- Client node `c`'s start port (node `1 + c`, port `9101 + c`). -/
theorem atStr_cstart : ∀ c, c < 6 → clientStartAddrs[c]? = some (atStr (1 + c) (W64 3000)) := by
  intro c h
  match c, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [atStr, nodeHost, nodePort, fmt.decimal, fmt.decimalNat, fmt.digitByte, clientStartAddrs]

/-- Client node `c`'s configuration port (node `1 + c`, port `8101 + c`). -/
theorem atStr_cconf : ∀ c, c < 6 → clientConfAddrs[c]? = some (atStr (1 + c) (W64 2000)) := by
  intro c h
  match c, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [atStr, nodeHost, nodePort, fmt.decimal, fmt.decimalNat, fmt.digitByte, clientConfAddrs]

section specs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF] [examples.swiftnet.Assumptions]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `Addrs()`: a new slice of the nodes' first addresses. -/
abbrev Addrs.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.Addrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* addrs }}

/-- `host(addrs[i])` (any node `i`). -/
abbrev host.spec : Prop :=
  ∀ (i : Nat) (a : GoString), addrs[i]? = some a →
  {{ isPkgInit (PROP := IProp GF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.host)) (Val #a))
  {{ RET #(nodeHost i); True }}

/-- `port(addrs[i])`. -/
abbrev port.spec : Prop :=
  ∀ (i : Nat) (a : GoString), addrs[i]? = some a →
  {{ isPkgInit (PROP := IProp GF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.port)) (Val #a))
  {{ RET #(W64 (nodePort i)); True }}

/-- `at(addrs, id, off)` on the deployment's addresses (any node `id`). -/
abbrev at.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (id off : w64), uint.nat id < 13 →
  {{ isPkgInit (PROP := IProp GF) swiftnetPkg ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.at'')) (Val #sl)) (Val #id)) (Val #off))
  {{ RET #(atStr (uint.nat id) off); sl ↦*{dq} addrs }}

/-- `nodeConfig(id, port, conf)`: a fresh `*config.Config`, plain (`config.plain`: no quorum
file, no proxies, no fixed leader, fast reads as `conf` says), with its `Alias`. -/
abbrev nodeConfig.spec : Prop :=
  ∀ (id port : w64) (v : examples.swiftnet.Conf),
  {{ isPkgInit (PROP := IProp GF) swiftnetPkg }}
    (App (App (App (Val (@! examples.swiftnet.nodeConfig)) (Val #id)) (Val #port)) (Val #v))
  {{ (p : Loc) (cv : config.Config), RET #p; config.plain p (decide (v.FastRead' = W64 1)) ∗
      p ↦□ cv }}

end specs

section register
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [examples.swiftnet.Assumptions] [net.FieldAssumptions]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr netDistGF]
  [H : RpcHttpHyp netDistGF]

/-- `register(ip, port, maddr)` (runReplica's registration, retried): from replica node `k`
of the configuration `c` (`k < c.n`), at the master's rpc address with its service: the
replica's id and the membership, as the master's `Register` answers once ready. -/
abbrev register.spec : Prop :=
  ∀ (γ : SwiftNames netDistGF) (ip : GoString) (port : w64) (k : Nat) (c : Conf),
    replicaAddrs[k]? = some (sp.addrPort ip port) → k < c.n →
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      conf.is γ c ∗ ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
      rpcHttp γ.W masterAddr ∗ net.rpc.codecSet net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk }}
    (App (App (App (Val (@! examples.swiftnet.register)) (Val #ip)) (Val #port))
      (Val #masterAddr))
  {{ (id : w64) (nl : GoSlice) (nodes : List GoString) (fr : Bool), RET (PairV #id #nl);
      nl ↦* nodes ∗ sp.cfg γ.conf γ.mem nodes.length fr nodes ∗
      ⌜nodes[id.toNat]? = some (sp.addrPort ip port)⌝ }}

end register

section maxDesc
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF]

/-- `serve`'s store of a valid configuration's `Desc` into `swift.MaxDescRoutines` (run.go's
`swift.MaxDescRoutines = 100`) before `swift.New`, with the global's exclusive points-to, which
the boot thread of a replica node owns (change log C14: a Go store is not atomic in Perennial). -/
abbrev setMaxDesc.spec : Prop :=
  ∀ (d d0 : w64), (uint.Z d = 0 ∨ uint.Z d = 2 ∨ uint.Z d = 100) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      globalAddr swift.MaxDescRoutines ↦ d0 }}
    (App (Val (GoInstruction (GoStore go.int)))
      (Val (PairV #(globalAddr swift.MaxDescRoutines) #d)))
  {{ RET #(); globalAddr swift.MaxDescRoutines ↦ d }}

end maxDesc

end Perennial.github_com.imdea_software.swiftpaxos
