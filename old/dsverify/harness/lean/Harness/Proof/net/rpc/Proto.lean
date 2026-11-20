/-
The protocol of the lab's model of `net/rpc` (`harness/rpcmodel/src/net/rpc`, `notes/craq-net.md`,
"rpc specs"): the wire format, the kit's codec as the specs see it, the address-level service
specs, and the per-connection ghost state that ties each execution of a method at a server to
exactly one request a client wrote.

**Wire format** (`wire.go`): a request stream is `rpcHead` (`connectHead "/_goRPC_"`) and then
frames; a response stream is `connectedBytes` and then frames; a frame is `frameOf p` (`p`'s
length, 8 bytes little-endian, then `p`); a request's payload is `msgOf seq sm body` (the
sequence number, `"Service.Method"`, the codec's encoding of the argument), a response's
`msgOf seq msg reply` (the error message, `""` for none, the encoded reply).

**The codec** (`RpcCodec`, a type class: the kit's, generated per kit by kitgen from kit.toml's
`[rpc]`, keyed on the kit's types; never a predicate a proof chooses). The model's `Codec`
struct holds four functions; `isCodec c` says the registered `*Codec` `c` holds functions meeting
the class's predicate transformers:
* `enc v Ψ`: `Encode(v)` returns a fresh byte slice holding `bs` with `Ψ bs`;
* `dec data ptr Ψ`: `Decode(data, ptr)` returns `nil` with `Ψ true`, or an error (with an
  `Error()` method) with `Ψ false`;
* `call rcvr m body Ψ`: `Call(rcvr, m, body)` returns `(reply, msg, found)` with `Ψ reply msg
  found` (the dispatch: decode `body` as `m`'s argument, run the method, encode its reply);
* `methods rcvr`: `Methods(rcvr)` returns (does not panic).

**Service specs.** A method spec (`MethodSpec`) is a precondition with the caller's continuation,
over encodings: `S m args Φ` is what a caller deposits for
method `m` on argument bytes `args`, and `Φ reply msg` is what it gets back with the reply bytes
and the error message (`""` for success; a method's error message otherwise, which the client
sees as `rpc.ServerError(msg)`). An address's services are fixed with the address
(`RpcWorld.SS a svc`, part of the address's protocol, set once from the start resources; no
party can use another). A receiver meets `S` (`rcvrOk rcvr S`, `Defs.lean`) when the codec's
dispatch, from `S m args Φ`, finds the method and returns `Φ reply msg` for its reply and
message, whatever the message.

**The world** (`RpcWorld`): the address specs and the name of a global ghost map from
connection ids to their names (`regInv`): the dialer registers a connection with the token
`connFresh cid false` that its `Dial` returned, so the names of a connection are unique and every
party agrees on them (`regElem`).

**A connection** (`RpcConnNames`, `connInv`): its requests in the order written (a mono-list
`reqs` of `RpcReq`: sequence number, `"Service.Method"`, argument bytes, the saved continuation
`Φ` (over the pair of the reply and the message) and the client's token `col` for collecting the
answer), the server reader's count `k` of requests it has taken (`ctr`, half with the reader),
and the answers (a ghost map `ans` from a request's index to `none` while its run is pending,
`some (msg, reply)` once answered). The invariant holds the deposit of every request not taken
yet, and for every answered request (whatever its message), `Φ reply msg` until the client
trades its `col` token for it (`answerRes`). The reader's half of `ctr` starts in the
invariant, claimed once with `connFresh cid true` (the acceptor's token). So a deposit goes to
at most one run (the reader takes request `k` once and moves on), `Φ reply msg` comes back only
from that run's answer, and a client's error other than a `ServerError` leaves its deposit with
the connection.

**Protocols** (`reqProto W a`, `respProto W a`): what the dialer writes is `httpReqP
"/_goRPC_"` of frames of requests in `reqs` (lower bound); what the acceptor writes is a prefix
of `connectedBytes`, then frames answering distinct indices of `reqs`, each with its persistent
answer. Readers parse frames from a stream that may end mid-frame, so the protocols speak of
prefixes; they also bound each payload's length (below `2 ^ 63`, as a Go slice's), so a frame's
length prefix determines it.
-/
module

public import Harness.GeneratedProof.net.rpc
public import Harness.Proof.net.http.Proto
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn

namespace net.rpc

/-! ## The wire format -/

/-- A frame: `p`'s length (8 bytes, little-endian) and `p` (`writeFrame`). -/
def frameOf (p : List w8) : List w8 := u64Le (W64 p.length) ++ p

/-- Frames of each payload, in order. -/
def framesOf (ps : List (List w8)) : List w8 := (ps.map frameOf).flatten

/-- A message: the sequence number, the string's length and bytes, the body (`encodeMsg`). -/
def msgOf (seq : w64) (s : GoString) (body : List w8) : List w8 :=
  u64Le seq ++ u64Le (W64 s.length) ++ s ++ body

/-- The path net/rpc serves on (`DefaultRPCPath`). -/
def rpcPath : GoString := go!"/_goRPC_"

/-- The head of a request stream (`DialHTTP`'s CONNECT request). -/
def rpcHead : GoString := net.http.connectHead rpcPath

/-- The head of a response stream (the server's reply to CONNECT, `connected`). -/
def connectedBytes : GoString := go!"HTTP/1.0 200 Connected to Go RPC\n\n"

/-- The index of the last `'.'` of `s` (`lastDot`). -/
def lastDotIdx (s : GoString) : Option Nat :=
  ((List.range s.length).reverse.find? (fun i => s[i]? = some (W8 46)))

/-- `"Service.Method"` split at its last dot (`Server.call`). -/
def splitSM (sm : GoString) : Option (GoString × GoString) :=
  (lastDotIdx sm).map fun i => (sm.take i, sm.drop (i + 1))

/-! ## Requests and connection names -/

/-- A request as the ghost state records it: sequence number, `"Service.Method"`, argument
bytes, the saved continuation's name `post` and the client's collection token `col`. -/
abbrev RpcReq := w64 × GoString × List w8 × GName × GName

namespace RpcReq
abbrev seq (r : RpcReq) : w64 := r.1
abbrev sm (r : RpcReq) : GoString := r.2.1
abbrev body (r : RpcReq) : List w8 := r.2.2.1
abbrev post (r : RpcReq) : GName := r.2.2.2.1
abbrev col (r : RpcReq) : GName := r.2.2.2.2
end RpcReq

/-- A request's payload (its frame's contents). -/
def reqMsg (r : RpcReq) : List w8 := msgOf r.seq r.sm r.body

/-- An answer `(i, msg, reply)` to request `i` of `L`, as a response payload. -/
def respMsg (L : List RpcReq) (x : Nat × GoString × List w8) : List w8 :=
  msgOf ((L[x.1]?.map RpcReq.seq).getD (W64 0)) x.2.1 x.2.2

/-- The names of a connection: its requests (mono-list), the server reader's count of requests
taken (ghost variable), its answers (ghost map). -/
abbrev RpcConnNames := GName × GName × GName

namespace RpcConnNames
abbrev reqs (n : RpcConnNames) : GName := n.1
abbrev ctr (n : RpcConnNames) : GName := n.2.1
abbrev ans (n : RpcConnNames) : GName := n.2.2
end RpcConnNames

/-! ## Specs -/

/-- A method spec: `S m args Φ` is the deposit for method `m` on argument bytes `args` with
continuation `Φ` (over the reply bytes and the error message, `""` for success). -/
abbrev MethodSpec (GF : BundledGFunctors) :=
  GoString → List w8 → (List w8 → GoString → IProp GF) → IProp GF

/-- The kit's codec, as the specs see it (see the file header). An instance is generated per
kit, keyed on the kit's types. -/
class RpcCodec [GooseExts] (GF : BundledGFunctors) where
  enc : GoInterface → (List w8 → IProp GF) → IProp GF
  dec : List w8 → GoInterface → (Bool → IProp GF) → IProp GF
  call : GoInterface → GoString → List w8 → (List w8 → GoString → Bool → IProp GF) → IProp GF
  methods : GoInterface → IProp GF

/-- The service names of the kit's receivers, as `Register` sees them (`Codec.Name`, generated
per kit by kitgen: the name of the receiver's type, as `reflect` gives it, for each service type
of kit.toml's `[rpc]`; `""` for any other value). A class of its own, apart from `RpcCodec`, so
that a kit that does not call `Register` need not define it. -/
class RpcNames [GooseExts] where
  name : GoInterface → GoString

/-- The rpc world: the services of each address (`SS a svc`, the spec of service `svc` at
address `a`, if it offers it) and the name of the registry of connections. -/
structure RpcWorld (GF : BundledGFunctors) where
  SS : GoString → GoString → Option (MethodSpec GF)
  reg : GName

def rpcN : Namespace := ndot nroot "net.rpc"
def regN : Namespace := ndot rpcN "reg"
def connN : Namespace := ndot rpcN "conn"

section proto
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The registry: every registered connection's dialer gave up its fresh token. -/
def regInv (W : RpcWorld GF) : IProp GF :=
  iprop(∃ M : GMap w64 RpcConnNames, ghostMapAuth W.reg 1 M ∗
    [∗map] cid ↦ _n ∈ M, connFresh cid false)

/-- Connection `cid`'s names are `γ` (persistent). -/
def regElem (W : RpcWorld GF) (cid : w64) (γ : RpcConnNames) : IProp GF :=
  ghostMapElem W.reg cid .discard γ

/-- The deposit of request `r` at address `a`: its service is one `a` offers, with spec `S`,
and the caller's deposit `S m body Φ` for its saved continuation `Φ` (saved uncurried, over the
pair of the reply and the message). -/
def reqDeposit (W : RpcWorld GF) (a : GoString) (r : RpcReq) : IProp GF :=
  iprop(∃ (svc m : GoString) (S : MethodSpec GF) (Φ : List w8 → GoString → IProp GF),
    ⌜splitSM r.sm = some (svc, m) ∧ W.SS a svc = some S⌝ ∗
    savedPredOwn r.post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ S m r.body Φ)

/-- The answer's continuation for request `r`: `Φ reply msg` for its saved `Φ`. -/
def replyEscrow (r : RpcReq) (reply : List w8) (msg : GoString) : IProp GF :=
  iprop(∃ Φ : List w8 → GoString → IProp GF,
    savedPredOwn r.post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ Φ reply msg)

/-- What the invariant holds for answer `o` of request `i` of `L`: for every answer, the
continuation of its reply and message, or the client's token (once collected). -/
def answerRes (L : List RpcReq) (i : Nat) (o : Option (GoString × List w8)) : IProp GF :=
  match o with
  | some (msg, reply) => iprop(∃ r, ⌜L[i]? = some r⌝ ∗ (replyEscrow r reply msg ∨ token r.col))
  | none => iprop(True)

/-- The invariant of connection `cid` (to address `a`) with names `γ`; see the file header. -/
def connInv (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) : IProp GF :=
  iprop(∃ (L : List RpcReq) (k : Nat) (A : GMap Nat (Option (GoString × List w8))),
    monoListAuthOwn γ.reqs (1 : Qp).half L ∗ ghostVar γ.ctr (1 : Qp).half k ∗
    ghostMapAuth γ.ans 1 A ∗
    (ghostVar γ.ctr (1 : Qp).half 0 ∨ connFresh cid true) ∗
    ⌜k ≤ L.length ∧ ∀ i, (A !! i).isSome → i < k⌝ ∗
    ([∗list] r ∈ L.drop k, reqDeposit W a r) ∗
    ([∗map] i ↦ o ∈ A, answerRes L i o))

/-- Connection `cid` to address `a` has names `γ` and its invariant (persistent). -/
def isRpcConn (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) : IProp GF :=
  iprop(regElem W cid γ ∗ inv connN (connInv W a cid γ))

/-- The body of a request stream after its head: a prefix of the frames of requests `L` of the
connection (persistent lower bound). -/
def reqBodyProto (W : RpcWorld GF) (a : GoString) : Proto GF := fun cid bs =>
  iprop(∃ (γ : RpcConnNames) (L : List RpcReq), isRpcConn W a cid γ ∗
    monoListLbOwn γ.reqs L ∗
    ⌜(∀ q ∈ L.map reqMsg, q.length < 2 ^ 63) ∧ bs <+: framesOf (L.map reqMsg)⌝)

/-- What a dialer of `a` writes: `rpcHead`, then frames of requests. -/
def reqProto (W : RpcWorld GF) (a : GoString) : Proto GF :=
  net.http.httpReqP rpcPath (reqBodyProto W a)

/-- What an acceptor at `a` writes: a prefix of `connectedBytes`, then frames answering distinct
requests of the connection. -/
def respProto (W : RpcWorld GF) (a : GoString) : Proto GF := fun cid bs =>
  iprop(⌜bs <+: connectedBytes⌝ ∨
    ∃ (γ : RpcConnNames) (L : List RpcReq) (Rs : List (Nat × GoString × List w8)),
      isRpcConn W a cid γ ∗ monoListLbOwn γ.reqs L ∗
      ([∗list] x ∈ Rs, ghostMapElem γ.ans x.1 .discard (some x.2)) ∗
      ⌜(Rs.map Prod.fst).Nodup ∧ (∀ x ∈ Rs, x.1 < L.length) ∧
        (∀ q ∈ Rs.map (respMsg L), q.length < 2 ^ 63) ∧
        bs <+: connectedBytes ++ framesOf (Rs.map (respMsg L))⌝)

/-- Address `a` serves rpc in world `W`: its protocols, and the registry (persistent). Made once
per address from its unset protocols (`rpcAddr_set`). -/
def rpcAddr (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(addrProto a (reqProto W a) (respProto W a) ∗ inv regN (regInv W))

end proto

end net.rpc

end Perennial
