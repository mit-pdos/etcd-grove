/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Client/{Base,Defs}.lean (run gryff-bump-1,
lab master 915f964; notes/dsv-gryff.md), restated for the kit's client on remote and `Net/`.

The client machines' Gryff client (`kit.go`'s `Sys`, `client`, `op`): its state, as the lock
`Sys.mu` holds it (remote's `ServeClient` reaches it only through a persistent token, `sysTok`).
* `replicaOf c`: client `c`'s replica's port (`ServerAddrs()[1 + c mod 3]` = `portAddr (c % 3)`).
* `connOk γ c v`: client `c`'s open connection (`v.conn'`, a `*TCPConn` `tc`, the dialer's end of
  connection `cn` to `replicaOf c`): its bufio reader over `recvTokL cn false (gryffWireQ γ a)`
  (whole replies read so far, `repliesOk`), its bufio writer (healthy, with room for a byte; the
  stream so far the handshake `u32Le hs` and whole requests `clientReqsOk` of Gryff client
  `hs = c + 6 (gen - 1)`, bound to the connection), the writer's contract (`net.conn_streamWriterOk`'s),
  and the turn token of `hs`. Port: the lab's `net.ownTCPConn`/`recvTok`/`addrP`/`addrQ` are
  `Net/`'s `connAt`/`recvTokL` and Gryff's wire protocols of the replica's port.
* `clientSt γ c v`: the `*client`'s state at the start of an operation: the generations used and
  request ids issued are bounded by the operations done (`ops`), the unused ids, the connection if
  open.
* `sysSt γ c sp`: what `Sys.mu` guards: `started`, `ops` (at most `K = 4`), the `*client`, the
  remaining budget units (`4 - ops`, lab D14).
* `sysTok γ c sys`: the persistent token: `sys` is a `*Sys` whose fixed fields are client `c`'s,
  with its lock.
-/
module

public import Dsverify.Proof.gryff.Shares
public import Dsverify.Proof.gryff.Client.Bufio
public import Dsverify.Proof.gryff.N.ConnLaws
public import Dsverify.Proof.gryff.Proto.WireLaws
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Client `c`'s replica's peer-and-client port. -/
def replicaOf (c : Nat) : GoString := portAddr (c % 3)

theorem replicaOf_mem (c : Nat) : replicaOf c ∈ replicaAddrs := by
  unfold replicaOf replicaAddrs
  have : c % 3 < 3 := Nat.mod_lt _ (by decide)
  rcases h : c % 3 with _ | _ | _ | n
  · simp
  · simp
  · simp
  · omega

/-- The server machines' addresses (`ServerAddrs()`): the master, then the replicas' ports. -/
def serverAddrs : List GoString :=
  [go!"127.0.0.1:7501", portAddr 0, portAddr 1, portAddr 2]

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- The connection's writer bundle (`Net/`'s contract for a `*TCPConn`'s writes). -/
abbrev connWSt (tc : Loc) (la ra ed : GoInterface) : wire.WSt GF :=
  ⟨Perennial.net.connIface tc, Perennial.net.connWriteE la ra ed, 4096⟩

/-- The connection's reader bundle. -/
abbrev connRSt (tc : Loc) (la ra eof ed : GoInterface) : wire.RSt GF :=
  ⟨Perennial.net.connIface tc, Perennial.net.connReadE eof la ra ed⟩

/-- `m` is one reply as a replica writes it to a client: an opcode and the message (the lab's
`Client/Base.lean`). -/
def replyShape (m : List w8) : Prop :=
  (∃ r : wire.gryffproto.ReadReply.Msg, m = gryffReadReply :: wire.gryffproto.ReadReply.enc r) ∨
  (∃ r : wire.gryffproto.WriteReply.Msg, m = gryffWriteReply :: wire.gryffproto.WriteReply.enc r) ∨
  (∃ r : wire.gryffproto.RMWReply.Msg, m = gryffRMWReply :: wire.gryffproto.RMWReply.enc r)

/-- `R` is whole replies: messages a replica wrote to a client (`clientReplyOk`'s shapes). -/
def repliesOk (R : List w8) : Prop :=
  ∃ ms : List (List w8), R = ms.flatten ∧ ∀ m ∈ ms, replyShape m

/-- Client `c`'s open connection, in its `*client`'s state `v`: see the file header. -/
def connOk (γ : GryffNames GF) (c : Nat) (v : examples.gryffnet.client) : IProp GF :=
  iprop(∃ (tc : Loc) (cn : Nat) (a : GoString) (la ra eof ed : GoInterface)
      (R body sent pend : List w8) (r : Int),
    ⌜v.conn' = interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc ∧
      a = replicaOf c ∧ 1 ≤ uint.nat v.gen' ∧ v.id' = gid c (uint.nat v.gen' - 1) ∧
      sent ++ pend = u32Le v.id' ++ body ∧ r ≤ sint.Z v.seq' + 1 ∧ repliesOk R⌝ ∗
    Perennial.net.connAt tc cn false a la ra ∗ globalAddr io.EOF ↦□ eof ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
    wire.ownReader v.r' (connRSt tc la ra eof ed)
      (recvTokL (Gg := hG.goose_globalGS) cn false (gryffWireQ γ a)) R ∗
    wire.writerOk (connWSt tc la ra ed) (sendTok (Gg := hG.goose_globalGS) cn false (gryffWireP γ a))
      (gryffWireP γ a cn) ∗
    wire.writerRoom v.w' (connWSt tc la ra ed)
      (sendTok (Gg := hG.goose_globalGS) cn false (gryffWireP γ a)) (gryffWireP γ a cn) sent pend 1 ∗
    clientConnAt γ v.id' cn ∗ clientReqsOk γ v.id' (sint.Z v.seq') body ∗
    turnTok (GF := GF) γ.proto (sint.Z v.id') r)

/-- Client `c`'s `*client` state `v` after `j` operations: see the file header. -/
def clientSt (γ : GryffNames GF) (c : Nat) (v : examples.gryffnet.client) (j : Nat) : IProp GF :=
  iprop(⌜uint.nat v.gen' ≤ j ∧ 0 ≤ sint.Z v.seq' ∧ sint.Z v.seq' ≤ j⌝ ∗
    unusedIds γ c (uint.nat v.gen') ∗
    (⌜v.conn' = interface.nil⌝ ∨ connOk γ c v))

/-- What `Sys.mu` guards (client `c`'s `*Sys` `sp`, its `*client` `cl`). -/
def sysSt (γ : GryffNames GF) (c : Nat) (sp cl : Loc) : IProp GF :=
  iprop(∃ (started : Bool) (ops : w64) (v : examples.gryffnet.client),
    sp.[examples.gryffnet.Sys, go!"started"] ↦ started ∗
    sp.[examples.gryffnet.Sys, go!"ops"] ↦ ops ∗ ⌜uint.nat ops ≤ 4⌝ ∗
    cl ↦ v ∗ clientSt γ c v (uint.nat ops) ∗ budget (GF := GF) γ.proto (4 - uint.nat ops))

/-- The persistent fields of client `c`'s `*Sys` `sp`. -/
def sysFixed (c : Nat) (sp mu cl : Loc) : IProp GF :=
  iprop(∃ ads : GoSlice,
    sp.[examples.gryffnet.Sys, go!"mu"] ↦□ mu ∗ sp.[examples.gryffnet.Sys, go!"c"] ↦□ W64 c ∗
    sp.[examples.gryffnet.Sys, go!"addrs"] ↦□ ads ∗ ads ↦*□ serverAddrs ∗
    sp.[examples.gryffnet.Sys, go!"cl"] ↦□ cl)

instance sysFixed_persistent (c : Nat) (sp mu cl : Loc) :
    Persistent (sysFixed (GF := GF) c sp mu cl) := by
  unfold sysFixed; infer_instance

/-- **Client `c`'s token** for remote's `ServeClient` (persistent): `sys` is client `c`'s `*Sys`,
its state under its lock. -/
def sysTok (γ : GryffNames GF) (c : Nat) (sys : GoInterface) : IProp GF :=
  iprop(∃ (sp mu cl : Loc),
    ⌜sys = interface.mkOk (go.GoType.PointerType examples.gryffnet.Sys.ty) #sp⌝ ∗
    sysFixed c sp mu cl ∗ sync.isMutex mu (sysSt γ c sp cl))

instance sysTok_persistent (γ : GryffNames GF) (c : Nat) (sys : GoInterface) :
    Persistent (sysTok γ c sys) := by
  unfold sysTok; infer_instance

end preds

end Perennial.gryff
