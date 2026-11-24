/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Rpc/Defs.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md), restated over `Net/`'s net/rpc (models-rpc-server,
models-rpc-http) and the kit's generated codec.

The rpc subsystem's definitions (U2): the bytes of the kit's generated codec
(`examples/gryffnet/rpc_gen.go`, by `models/net/rpc/rpcgen.py`) for the values the deployment
sends, the master's registry (`DeployNames.registry`, a mono-list of `"addr:port"` strings in
registration order), the method specs of the master's and the replicas' services, and the rpc
world's services per address.

**Encodings** (rpcgen's, not the lab's kitgen codec): a top-level value is its type's name
(`rpcPutTag`: the name's length, 8 bytes little-endian, then its bytes) and the value; a string is
its length and its bytes; an `int` or `uint8` 8 bytes little-endian; a `bool` one byte; a slice its
count and its elements; a struct the byte 1, then per field the byte 1 and the field's value if
the field is sent (not its zero value: gob's rule), else the byte 0. `encRegArgs addr port`
(`masterproto.RegisterArgs`), `encRegReply id nodes ready` (`masterproto.RegisterReply`),
`encPingArgs a`, `encPingReply`, `encBTLArgs`, `encBTLReply`.

**The registry** (`regAuth`, `regLb`): the mono-list `δ.registry` (over `[AllG GF]`; the lab put it
at a fixed slot of its `netDistGF`).

**Method specs** (`Net/`'s `MethodSpec`: over argument bytes, with the caller's continuation):
* `masterSvc δ R`: `"Register"` with the arguments of replica node `k` (`"127.0.0.1"`,
  `portNum k`) and what the registering node carries, `R k` (D13: its recorded prediction,
  `regCarry`, `Server/Deploy.lean`; persistent, as a request may be sent several times); the
  answer is `encRegReply 0 [] false` (not every replica registered yet) or `encRegReply id nodes
  true` with `regReady δ k id nodes`. The master's receiver also has `GetLeader` and
  `GetReplicaList` (rpcgen lists every exported method): no one calls them (`False`).
* `replicaSvc`: `"Ping"` and `"BeTheLeader"`, whose answers carry nothing.
Both accept error answers (`withErr`): `Net/`'s server answers a request it cannot dispatch or
decode with its own error, and `srvServes` asks `errOk` (today: every non-empty message) of every
service. When upamanyus lands `errOk`'s restriction to the server's own messages (`srvErrMsg`,
answer A2/C3 on #24), `withErr`'s second half shrinks to those.

**Addresses** (the kit's, `kit.go`): the master's net/rpc at `127.0.0.1:7501` (listener `":7501"`),
replica node `k`'s port `portAddr k` = `127.0.0.1:750(2+k)` (`Proto/Wire.lean`) and its net/rpc at
`127.0.0.1:850(2+k)` (listener `":850(2+k)"`, `serverlib.Serve(port + 1000)`). The listeners are
wildcards, so the world's services are stated at every address a listener takes (`lisAccepts`).
Port: the lab's `portOf k` is `portNum k` here (`Net`'s `portOf` is opened everywhere).
-/
module

public import Dsverify.Proof.gryff.Names
public import Dsverify.Proof.gryff.Proto.Wire
public import Perennial.Ghost.MonoList
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-! ## Byte encodings (rpcgen's) -/

/-- An `int` or a `uint64`: 8 bytes little-endian. -/
def encU64 (x : w64) : List w8 := u64Le x

/-- A string: its length and its bytes. -/
def encStr (s : GoString) : List w8 := u64Le (W64 s.length) ++ s

/-- A `[]string`: its count and its elements. -/
def encStrs (l : List GoString) : List w8 := u64Le (W64 l.length) ++ (l.map encStr).flatten

/-- A `bool`. -/
def encBool (b : Bool) : List w8 := [if b then W8 1 else W8 0]

/-- A struct field: sent (`1` and its value) or not (`0`). -/
def fld (sent : Bool) (body : List w8) : List w8 := if sent then W8 1 :: body else [W8 0]

def fStr (s : GoString) : List w8 := fld (decide (s ≠ [])) (encStr s)
def fU64 (x : w64) : List w8 := fld (decide (x ≠ W64 0)) (encU64 x)
def fU8 (x : w8) : List w8 := fld (decide (x ≠ W8 0)) (encU64 (W64 (uint.Z x)))
def fStrs (l : List GoString) : List w8 := fld (decide (l ≠ [])) (encStrs l)
def fBool (b : Bool) : List w8 := fld b (encBool b)

/-- A struct of the fields `fs`. -/
def strct (fs : List (List w8)) : List w8 := W8 1 :: fs.flatten

/-- A top-level value of the type named `t`. -/
def tagged (t : GoString) (body : List w8) : List w8 := encStr t ++ body

/-- `masterproto.RegisterArgs{addr, port}`. -/
def encRegArgs (addr : GoString) (port : w64) : List w8 :=
  tagged go!"gryff/src/masterproto.RegisterArgs" (strct [fStr addr, fU64 port])

/-- `masterproto.RegisterReply{id, nodes, ready}`. -/
def encRegReply (id : w64) (nodes : List GoString) (ready : Bool) : List w8 :=
  tagged go!"gryff/src/masterproto.RegisterReply" (strct [fU64 id, fStrs nodes, fBool ready])

/-- `genericsmrproto.PingArgs{a}`. -/
def encPingArgs (a : w8) : List w8 :=
  tagged go!"gryff/src/genericsmrproto.PingArgs" (strct [fU8 a])

/-- `genericsmrproto.PingReply{}`. -/
def encPingReply : List w8 := tagged go!"gryff/src/genericsmrproto.PingReply" (strct [])

/-- `genericsmrproto.BeTheLeaderArgs{}`. -/
def encBTLArgs : List w8 := tagged go!"gryff/src/genericsmrproto.BeTheLeaderArgs" (strct [])

/-- `genericsmrproto.BeTheLeaderReply{}`. -/
def encBTLReply : List w8 := tagged go!"gryff/src/genericsmrproto.BeTheLeaderReply" (strct [])

/-! ## The replicas' registration arguments and the addresses -/

/-- Replica node `k`'s IP (`RegisterWithMaster`'s `myAddr`: `kit.go`'s `hp[0]`). -/
def ipOf (_k : Nat) : GoString := go!"127.0.0.1"

/-- Replica node `k`'s port (`RegisterWithMaster`'s `portnum`); the lab's `portOf`. -/
def portNum (k : Nat) : w64 := W64 (7502 + k)

/-! ## The arguments' sizes (`Client.Call.spec`'s frame bound, `maxFrameN` = `2 ^ 30`) -/

theorem encPingArgs_length (a : w8) : (encPingArgs a).length ≤ 2 ^ 30 := by
  unfold encPingArgs tagged encStr strct fU8 fld encU64
  split <;> simp [u64Le_length]

theorem encBTLArgs_length : encBTLArgs.length ≤ 2 ^ 30 := by
  unfold encBTLArgs tagged encStr strct
  simp [u64Le_length]

theorem encRegArgs_ipOf_length (k : Nat) (port : w64) :
    (encRegArgs (ipOf k) port).length ≤ 2 ^ 30 := by
  unfold encRegArgs tagged encStr strct fStr fU64 fld encStr encU64 ipOf
  split <;> split <;> simp [u64Le_length]

/-- Replica node `k`'s `"addr:port"`, as the master formats it (`portAddr k`). -/
def addrOf (k : Nat) : GoString := portAddr k

/-- The master's rpc address (what the replicas dial). -/
def masterRpcAddr : GoString := go!"127.0.0.1:7501"

/-- The master's rpc listener (`masterlib.NewMaster`'s `Listen(":7501")`). -/
def masterRpcLis : GoString := go!":7501"

/-- Replica node `k`'s rpc address (what the master dials: its address, port + 1000). -/
def replicaRpcAddr (k : Nat) : GoString :=
  [go!"127.0.0.1:8502", go!"127.0.0.1:8503", go!"127.0.0.1:8504"].getD k go!""

/-- Replica node `k`'s rpc listener (`serverlib.Serve(port + 1000)`'s `Listen(":p")`). -/
def replicaRpcLis (k : Nat) : GoString :=
  [go!":8502", go!":8503", go!":8504"].getD k go!""

/-- The replicas' rpc addresses. -/
def replicaRpcAddrs : List GoString := [replicaRpcAddr 0, replicaRpcAddr 1, replicaRpcAddr 2]

/-! ## The registry -/

section reg
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- The registry's authority (fraction `q`) over the list `L`. -/
def regAuth (δ : DeployNames) (q : Qp) (L : List GoString) : IProp GF :=
  monoListAuthOwn δ.registry q L

/-- The registry holds at least `L` (persistent). -/
def regLb (δ : DeployNames) (L : List GoString) : IProp GF :=
  monoListLbOwn δ.registry L

instance regLb_persistent (δ : DeployNames) (L : List GoString) :
    Persistent (regLb (GF := GF) δ L) := by
  unfold regLb; infer_instance

instance regLb_timeless (δ : DeployNames) (L : List GoString) : Timeless (regLb (GF := GF) δ L) := by
  unfold regLb; infer_instance

instance regAuth_timeless (δ : DeployNames) (q : Qp) (L : List GoString) :
    Timeless (regAuth (GF := GF) δ q L) := by
  unfold regAuth; infer_instance

/-- A `Ready` registration of replica node `k`: the full list `nodes` (a permutation of the
replicas' addresses, a witness of the registry) and `k`'s index `id` in it. -/
def regReady (δ : DeployNames) (k : Nat) (id : w64) (nodes : List GoString) : IProp GF :=
  iprop(regLb δ nodes ∗ ⌜nodes.Perm [addrOf 0, addrOf 1, addrOf 2] ∧
    nodes[uint.nat id]? = some (addrOf k)⌝)

instance regReady_persistent (δ : DeployNames) (k : Nat) (id : w64) (nodes : List GoString) :
    Persistent (regReady (GF := GF) δ k id nodes) := by
  unfold regReady; infer_instance

theorem regReady_length (δ : DeployNames) (k : Nat) (id : w64) (nodes : List GoString) :
    regReady (GF := GF) δ k id nodes ⊢ ⌜nodes.length = 3⌝ := by
  unfold regReady
  iintro ⟨-, %h⟩
  ipureintro; exact h.1.length_eq

end reg

/-! ## Method specs -/

section specs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- A method spec that also accepts error answers (see the file header). -/
def withErr (S : net.rpc.MethodSpec GF) : net.rpc.MethodSpec GF := fun m args Φ =>
  iprop(S m args Φ ∧ ∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg)

/-- `Master.Register` (see the file header), without error answers. -/
def masterSvc0 (δ : DeployNames) (R : Nat → IProp GF) : net.rpc.MethodSpec GF :=
  fun m args Φ =>
  iprop(⌜m = go!"Register"⌝ ∗ ∃ k : Nat, ⌜k < 3 ∧ args = encRegArgs (ipOf k) (portNum k)⌝ ∗
    R k ∗ (Φ (encRegReply (W64 0) [] false) [] ∧
      ∀ (id : w64) (nodes : List GoString),
        regReady δ k id nodes -∗ Φ (encRegReply id nodes true) []))

/-- `Replica.Ping`, `Replica.BeTheLeader` (see the file header), without error answers. -/
def replicaSvc0 : net.rpc.MethodSpec GF := fun m args Φ =>
  iprop((⌜m = go!"Ping"⌝ ∗ (∃ a : w8, ⌜args = encPingArgs a⌝) ∗ Φ encPingReply []) ∨
    (⌜m = go!"BeTheLeader" ∧ args = encBTLArgs⌝ ∗ Φ encBTLReply []))

/-- The master's service. -/
def masterSvc (δ : DeployNames) (R : Nat → IProp GF) : net.rpc.MethodSpec GF :=
  withErr (masterSvc0 δ R)

/-- The replicas' service. -/
def replicaSvc : net.rpc.MethodSpec GF := withErr replicaSvc0

open Classical in
/-- The services of each rpc address: `"Master"` at every address the master's listener takes,
`"Replica"` at every address a replica's rpc listener takes. -/
def rpcServicesDef (δ : DeployNames) (R : Nat → IProp GF) :
    GoString → GoString → Option (net.rpc.MethodSpec GF) := fun a svc =>
  if lisAccepts masterRpcLis a ∧ svc = go!"Master" then some (masterSvc δ R)
  else if (∃ k, k < 3 ∧ lisAccepts (replicaRpcLis k) a) ∧ svc = go!"Replica" then some replicaSvc
  else none

end specs

end Perennial.gryff
