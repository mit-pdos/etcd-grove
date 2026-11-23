/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swiftnet/Base.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The vocabulary the hubs share with the SwiftPaxos slot (`Spec/swift/Inv.lean`), below
`Spec/swiftnet/Interface.lean` so that both can use it:

* `Conf`, the leader changes and their wire encoding (the adapter's `Conf.encode`, nine bytes);
* the deployment's addresses;
* the configuration and membership slots over their ghost names (`confIs`, `memIs`: write-once
  mono-lists; `Interface.lean`'s `conf.is`, `mem.is` are these at `SwiftNames`' names);
* the abstract key-value state (`linOwn`, the client spec's `own_state`; the other half is in
  `sp.inv`), the key names (`lin.keyName`: SwiftPaxos's integer key as the model's string key)
  and a command's effect on the abstract state (`lin.apply`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.Model
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## The configuration -/

/-- A configuration `New` can choose (`kit.go`'s `Conf`, as `decode` accepts it). -/
structure Conf where
  n : Nat
  fastRead : Nat
  pool : Nat
  desc : Nat
  deriving DecidableEq

instance Conf.countable : Pos.Countable Conf :=
  .ofInjective (fun c => Pos.Countable.encode (c.n, c.fastRead, c.pool, c.desc))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- `decode`'s validity: the configurations `choose` picks. -/
def Conf.valid (c : Conf) : Prop :=
  (c.n = 3 ∨ c.n = 5) ∧ c.fastRead ≤ 1 ∧ c.pool ≤ 2 ∧ (c.desc = 0 ∨ c.desc = 2 ∨ c.desc = 100)

/-- A planned leader change as a client node gets it (`kit.go`'s `change` less its `Client`):
once `after` of the node's client's operations returned, the node asks server node `node` (a
replica) `BeTheLeader`. -/
structure Change where
  node : Nat
  after : Nat
  deriving DecidableEq

/-- `decode`'s check of a change for the configuration `c` (`K` = 8 operations). -/
def Change.valid (c : Conf) (ch : Change) : Prop :=
  2 ≤ ch.node ∧ ch.node ≤ c.n + 1 ∧ 1 ≤ ch.after ∧ ch.after < 8

/-- `MaxChanges`. -/
def maxChanges : Nat := 2

/-- `ConfLen`: the message's length. -/
def confLen : Nat := 5 + 2 * maxChanges

/-- `Conf.encode(cs)`: `ConfLen` (nine) bytes: N, FastRead, Pool, Desc, the number of changes,
then each change's Node and After, zero bytes for the ones missing (at most `maxChanges`). -/
def Conf.encodeC (c : Conf) (cs : List Change) : List w8 :=
  [W8 c.n, W8 c.fastRead, W8 c.pool, W8 c.desc, W8 cs.length] ++
    (List.range maxChanges).flatMap (fun i =>
      match cs[i]? with
      | some ch => [W8 ch.node, W8 ch.after]
      | none => [W8 0, W8 0])

/-- The message a server node gets: no change. -/
def Conf.encode (c : Conf) : List w8 := c.encodeC []

/-- A client node's changes are valid for `c` (what `decode` accepts). -/
def Conf.changesOk (c : Conf) (cs : List Change) : Prop :=
  cs.length ≤ maxChanges ∧ ∀ ch ∈ cs, ch.valid c

/-- `confAck`, the server's one-byte answer. -/
def confAck : w8 := W8 0x6b

/-! ## The addresses

Node 0 is the orchestrator, nodes 1..6 the client nodes (client `c` on node `1 + c`), node 7 the
master (server node 1), nodes 8..12 the replicas (server node `k + 2` on node `8 + k`). All on
loopback (`127.0.0.1`), told apart by port (kit.go's `Addrs()`; the server nodes keep the lab's ports). -/

/-- The orchestrator's address (`Addrs()[0]`): nobody listens on it or dials it. -/
def orchAddr : GoString := go!"127.0.0.1:6100"
/-- The client nodes' first addresses (`Addrs()[1 + c]`, ports 6101..6106): their clients only dial. -/
def clientNodeAddrs : List GoString :=
  [go!"127.0.0.1:6101", go!"127.0.0.1:6102", go!"127.0.0.1:6103", go!"127.0.0.1:6104",
   go!"127.0.0.1:6105", go!"127.0.0.1:6106"]
/-- The client nodes' configuration ports (`ConfOff` above node `1 + c`'s first: 8101..8106). -/
def clientConfAddrs : List GoString :=
  [go!"127.0.0.1:8101", go!"127.0.0.1:8102", go!"127.0.0.1:8103", go!"127.0.0.1:8104",
   go!"127.0.0.1:8105", go!"127.0.0.1:8106"]
/-- The client nodes' start ports (`StartOff` above node `1 + c`'s first: 9101..9106): the
orchestrator's second message, once every node acknowledged its configuration. -/
def clientStartAddrs : List GoString :=
  [go!"127.0.0.1:9101", go!"127.0.0.1:9102", go!"127.0.0.1:9103", go!"127.0.0.1:9104",
   go!"127.0.0.1:9105", go!"127.0.0.1:9106"]
/-- The master's rpc address (`Addrs()[7]`). -/
def masterAddr : GoString := go!"127.0.0.1:7001"
/-- The server nodes' configuration ports (`9000 + i`, server node i = 1..6). -/
def confAddrs : List GoString :=
  [go!"127.0.0.1:9001", go!"127.0.0.1:9002", go!"127.0.0.1:9003", go!"127.0.0.1:9004",
   go!"127.0.0.1:9005", go!"127.0.0.1:9006"]
/-- The replicas' rpc ports (`8000 + i`, server node i = 2..6). -/
def replicaRpcAddrs : List GoString :=
  [go!"127.0.0.1:8002", go!"127.0.0.1:8003", go!"127.0.0.1:8004", go!"127.0.0.1:8005",
   go!"127.0.0.1:8006"]
/-- The replicas' peer and client ports (`7000 + i`, server node i = 2..6): SwiftPaxos's wire
format. Server node `k + 2` is "node `k`" of the SwiftPaxos slot (`k < 5`). -/
def replicaAddrs : List GoString :=
  [go!"127.0.0.1:7002", go!"127.0.0.1:7003", go!"127.0.0.1:7004", go!"127.0.0.1:7005",
   go!"127.0.0.1:7006"]
/-- Every node's first address (`Addrs()`), by node id. -/
def addrs : List GoString :=
  [go!"127.0.0.1:6100", go!"127.0.0.1:6101", go!"127.0.0.1:6102", go!"127.0.0.1:6103",
   go!"127.0.0.1:6104", go!"127.0.0.1:6105", go!"127.0.0.1:6106", go!"127.0.0.1:7001",
   go!"127.0.0.1:7002", go!"127.0.0.1:7003", go!"127.0.0.1:7004", go!"127.0.0.1:7005",
   go!"127.0.0.1:7006"]
/-- The rpc addresses (the rpc world's: `rpcAddr_set`). -/
def rpcAddrs : List GoString := masterAddr :: replicaRpcAddrs
/-- The other addresses the run sets (`addrs_set_proto`): all but the rpc addresses and the
client nodes' request addresses (`ClientAddrs()`, 7101..7106, remote's). -/
def plainAddrs : List GoString :=
  orchAddr :: clientNodeAddrs ++ clientConfAddrs ++ clientStartAddrs ++ confAddrs ++ replicaAddrs

/-- The replica node (index into `replicaAddrs`) of replica id `r` in the membership `l`. -/
def nodeOf (l : List GoString) (r : Nat) : Option Nat :=
  (l[r]?).bind (fun a => replicaAddrs.idxOf? a)

section slots
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-! ## The configuration slot -/

/-- The configuration is `c` (persistent). -/
def confIs (γc : GName) (c : Conf) : IProp netDistGF :=
  iprop(monoListLbOwn (A := Conf) γc [c] ∗ ⌜c.valid⌝)

/-! ## The membership slot -/

/-- The replicas' addresses, by replica id, are `l` (persistent; the master's `NodeList`, the
`"ip:port"` of each replica's first port: distinct addresses of `replicaAddrs`). -/
def memIs (γm : GName) (l : List GoString) : IProp netDistGF :=
  iprop(monoListLbOwn (A := List GoString) γm [l] ∗ ⌜l.Nodup ∧ ∀ a ∈ l, a ∈ replicaAddrs⌝)

/-! ## The abstract state -/

/-- The key-value state after the puts `ps` (oldest first). -/
def lin.stateOf (ps : List (GoString × GoString)) : (kv GoString GoString).State :=
  ps.foldl (fun s p => fun k => if k = p.1 then some p.2 else s k) (kv GoString GoString).init

/-- The key-value state, as the client spec's `own_state` (the atomic updates' half): the
linearized puts so far, a ghost variable whose other half is in `sp.inv`. -/
def linOwn (γl : GName) (σ : (kv GoString GoString).State) : IProp netDistGF :=
  iprop(∃ ps : List (GoString × GoString), ghostVar γl (1 : Qp).half ps ∗
    ⌜σ = lin.stateOf ps⌝)

/-! ## Laws of the configuration and membership slots -/

instance confIs_persistent (γc : GName) (c : Conf) : Persistent (confIs γc c) := by
  unfold confIs; infer_instance

instance memIs_persistent (γm : GName) (l : List GoString) : Persistent (memIs γm l) := by
  unfold memIs; infer_instance

/-- The configuration is written once: two of its facts agree. -/
theorem confIs_agree (γc : GName) (c1 c2 : Conf) :
    confIs γc c1 ∗ confIs γc c2 ⊢ ⌜c1 = c2⌝ := by
  unfold confIs
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  icases mono_list_lb_valid γc [c1] [c2] $$ H1 H2 with %H
  ipureintro
  rcases H with ⟨t, ht⟩ | ⟨t, ht⟩ <;> simp at ht <;> simp [ht.1]

/-- A configuration fact is a valid one (`decode`'s). -/
theorem confIs_valid (γc : GName) (c : Conf) : confIs γc c ⊢ ⌜c.valid⌝ := by
  unfold confIs
  iintro ⟨-, %H⟩
  ipureintro; exact H

/-- The membership is written once: two of its facts agree. -/
theorem memIs_agree (γm : GName) (l1 l2 : List GoString) :
    memIs γm l1 ∗ memIs γm l2 ⊢ ⌜l1 = l2⌝ := by
  unfold memIs
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  icases mono_list_lb_valid γm [l1] [l2] $$ H1 H2 with %H
  ipureintro
  rcases H with ⟨t, ht⟩ | ⟨t, ht⟩ <;> simp at ht <;> simp [ht.1]

/-- A membership's addresses are distinct replica addresses. -/
theorem memIs_ok (γm : GName) (l : List GoString) :
    memIs γm l ⊢ ⌜l.Nodup ∧ ∀ a ∈ l, a ∈ replicaAddrs⌝ := by
  unfold memIs
  iintro ⟨-, %H⟩
  ipureintro; exact H

/-- The writer (the orchestrator's `conf.writer`, an empty mono-list's authority) writes a valid
configuration, once: the fact, and the authority, which can write nothing else. -/
theorem confIs_write (γc : GName) (c : Conf) :
    ⌜c.valid⌝ ∗ monoListAuthOwn (A := Conf) γc 1 [] ⊢
      |==> (confIs γc c ∗ monoListAuthOwn (A := Conf) γc 1 [c]) := by
  -- (HUB-REQUEST 1 applied, change log C1: the update now covers both conjuncts)
  iintro ⟨%Hv, H⟩
  imod monoListAuthOwn_update (γ := γc) [c] List.nil_prefix $$ H with ⟨Ha, #Hlb⟩
  imodintro
  unfold confIs
  iframe Ha Hlb
  ipureintro; exact Hv

/-- The master's writer token writes the membership once. -/
theorem memIs_write (γm : GName) (l : List GoString) :
    ⌜l.Nodup ∧ ∀ a ∈ l, a ∈ replicaAddrs⌝ ∗ monoListAuthOwn (A := List GoString) γm 1 [] ⊢
      |==> (memIs γm l ∗ monoListAuthOwn (A := List GoString) γm 1 [l]) := by
  iintro ⟨%Hv, H⟩
  imod monoListAuthOwn_update (γ := γm) [l] List.nil_prefix $$ H with ⟨Ha, #Hlb⟩
  imodintro
  unfold memIs
  iframe Ha Hlb
  ipureintro; exact Hv

/-- Before the write, no configuration fact exists (the writer's authority is empty). -/
theorem confIs_unwritten (γc : GName) (c : Conf) :
    monoListAuthOwn (A := Conf) γc 1 [] ∗ confIs γc c ⊢ False := by
  unfold confIs
  iintro ⟨Ha, ⟨Hlb, -⟩⟩
  icases mono_list_auth_lb_valid γc 1 [] [c] $$ Ha Hlb with %H
  ipureintro
  simp at H

end slots

/-- The model's key of SwiftPaxos's key `k`: its eight bytes, little-endian (the adapter's
`key` reads the model's 8-byte key so, as `state.Key`'s `Marshal` writes it; injective). -/
def lin.keyName (k : w64) : GoString :=
  (List.range 8).map (fun i => W8 ((k.toNat / 2 ^ (8 * i)) % 256 : Nat))

end Perennial.github_com.imdea_software.swiftpaxos
