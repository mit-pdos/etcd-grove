/-
The protocol of the lab's grpc model (`harness/rpcmodel/grpc`, `notes/grpc-model.md`): the wire
format, the address-level method specs, and the per-connection ghost state that ties each run of
a handler at a server to exactly one call a client wrote.

**Wire format** (`wire.go`): both streams are frames (`net.rpc.frameOf p`: `p`'s length, 8
bytes little-endian, then `p`, as the net/rpc model's); a payload is `msgOf tag seq s body`
(`encodeMsg`). The client's frames are numbered from 0 in the order written (`CFrame`): a call
(`CFrame.call`: tag 0, its own number as the sequence number, the full method name, the encoded
request) or a cancellation (`CFrame.cancel`: tag 1, the number of the call given up). The
server's frames are answers (`Ans`: the number of the call answered, the status code as the tag,
the status message, the encoded reply).

**Method specs.** A unary spec (`UnarySpec`) is a precondition with the caller's continuation,
over encodings: `S req Φ` is what a caller deposits for a call with request bytes `req`, and
`Φ rep` is what it gets back with the reply bytes when the call succeeds (status OK). A failed
call gives nothing back (its deposit is lost: at most one run). An address's method specs are
fixed with the address (`GrpcWorld.MS a fm`, by full method name `"/service/method"`, part of the
address's protocol, set once from the start resources; no party can use another).

**The world** (`GrpcWorld`): the method specs of each address and the name of a global ghost map
from connection ids to their names (`regInv`): the dialer registers a connection with the token
`connFresh cid false` that its `Dial` returned.

**A connection** (`GConnNames`, `connInv`): the client's frames in the order written (a
mono-list `reqs` of `CFrame`), the server reader's count `k` of frames it has taken (`ctr`, half
with the reader), and the answers (a ghost map `ans` from a call's number to `none` while its run
is pending, `some (code, msg, reply)` once answered). The invariant holds the deposit of every
call not taken yet, and for every answered call with status OK, the continuation `Φ reply` until
the client trades the call's `col` token for it (`answerRes`). The reader's half of `ctr` starts
in the invariant, claimed once with `connFresh cid true` (the acceptor's token).

**Protocols** (`reqProto W a`, `respProto W a`): what the dialer writes is a prefix of the frames
of its `CFrame`s; what the acceptor writes is a prefix of frames answering distinct calls, each
with its persistent answer. Payloads are bounded (below `2 ^ 63`) so a frame's length prefix
determines it.
-/
module

public import Harness.Proof.grpc.Base
public import Harness.Proof.net.rpc.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn

namespace google_golang_org.grpc

/-! ## The wire format -/

/-- A payload: the tag, the sequence number, the string's length and bytes, the body
(`encodeMsg`). -/
def msgOf (tag seq : w64) (s : GoString) (body : List w8) : List w8 :=
  u64Le tag ++ u64Le seq ++ u64Le (W64 s.length) ++ s ++ body

/-- A client frame as the ghost state records it: a call (full method name, request bytes, the
saved continuation's name `post`, the client's collection token `col`), or a cancellation of
the call numbered `target`. -/
inductive CFrame where
  | call (fm : GoString) (body : List w8) (post col : GName)
  | cancel (target : w64)

/-- A client frame as a tuple (for its `Countable` instance). -/
def CFrame.toTuple : CFrame → Bool × GoString × List w8 × GName × GName × w64
  | .call fm body post col => (true, fm, body, post, col, W64 0)
  | .cancel t => (false, [], [], default, default, t)

theorem CFrame.toTuple_inj : Function.Injective CFrame.toTuple := by
  intro x y h
  cases x <;> cases y <;> simp_all [CFrame.toTuple]

noncomputable instance CFrame.countable : Pos.Countable CFrame :=
  Pos.Countable.ofInjective (fun f => Pos.Countable.encode f.toTuple)
    (fun _ _ h => CFrame.toTuple_inj (Pos.encode_inj h))

/-- Client frame number `i`'s payload. -/
def CFrame.msg (i : Nat) : CFrame → List w8
  | .call fm body _ _ => msgOf (W64 0) (W64 i) fm body
  | .cancel t => msgOf (W64 1) t [] []

/-- The payloads of the client's frames, numbered from 0. -/
def cmsgs (L : List CFrame) : List (List w8) := L.mapIdx (fun i f => f.msg i)

/-- An answer: the number of the call answered, the status code, the message, the reply. -/
abbrev Ans := Nat × w64 × GoString × List w8

/-- An answer's payload. -/
def respMsg (x : Ans) : List w8 := msgOf x.2.1 (W64 x.1) x.2.2.1 x.2.2.2

/-- The names of a connection: its frames (mono-list), the server reader's count of frames
taken (ghost variable), its answers (ghost map). -/
abbrev GConnNames := GName × GName × GName

namespace GConnNames
abbrev reqs (n : GConnNames) : GName := n.1
abbrev ctr (n : GConnNames) : GName := n.2.1
abbrev ans (n : GConnNames) : GName := n.2.2
end GConnNames

/-! ## Specs -/

/-- A unary method spec: `S req Φ` is the deposit for a call with request bytes `req` and
continuation `Φ` (over the reply bytes of a successful run). -/
abbrev UnarySpec (GF : BundledGFunctors) := List w8 → (List w8 → IProp GF) → IProp GF

/-- The grpc world: the method specs of each address (`MS a fm`, the spec of full method `fm`
at address `a`, if it offers it) and the name of the registry of connections. -/
structure GrpcWorld (GF : BundledGFunctors) where
  MS : GoString → GoString → Option (UnarySpec GF)
  reg : GName

def grpcN : Namespace := ndot nroot "grpc"
def regN : Namespace := ndot grpcN "reg"
def connN : Namespace := ndot grpcN "conn"

section proto
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The registry: every registered connection's dialer gave up its fresh token. -/
def regInv (W : GrpcWorld GF) : IProp GF :=
  iprop(∃ M : GMap w64 GConnNames, ghostMapAuth W.reg 1 M ∗
    [∗map] cid ↦ _n ∈ M, connFresh cid false)

/-- Connection `cid`'s names are `γ` (persistent). -/
def regElem (W : GrpcWorld GF) (cid : w64) (γ : GConnNames) : IProp GF :=
  ghostMapElem W.reg cid .discard γ

/-- The deposit of client frame `f` at address `a`: for a call, its method is one `a` offers,
with spec `S`, and the caller's deposit `S body Φ` for its saved continuation `Φ`. -/
def frameDeposit (W : GrpcWorld GF) (a : GoString) : CFrame → IProp GF
  | .call fm body post _ => iprop(∃ (S : UnarySpec GF) (Φ : List w8 → IProp GF),
      ⌜W.MS a fm = some S⌝ ∗ savedPredOwn post .discard Φ ∗ S body Φ)
  | .cancel _ => iprop(True)

/-- The reply escrow of a call with continuation name `post`: `Φ reply` for its saved `Φ`. -/
def replyEscrow (post : GName) (reply : List w8) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn post .discard Φ ∗ Φ reply)

/-- What the invariant holds for the answer `o` of client frame `i` of `L`: the answered frame is
a call and the code is a `codes.Code` (below `2 ^ 32`, so not `OK` once truncated unless `0`);
once answered with status OK, the continuation of its reply, or the client's token (once
collected); nothing for an error answer. -/
def answerRes (L : List CFrame) (i : Nat) (o : Option (w64 × GoString × List w8)) : IProp GF :=
  match o with
  | some (code, _msg, reply) => iprop(∃ (fm : GoString) (b : List w8) (post col : GName),
      ⌜L[i]? = some (.call fm b post col) ∧ (code = W64 0 ∨ uint.Z code < 2 ^ 32)⌝ ∗
      ((if code = W64 0 then replyEscrow post reply else iprop(True)) ∨ token col))
  | none => iprop(True)

/-- Client frame `i` of `L` is a call. -/
def isCallAt (L : List CFrame) (i : Nat) : Prop :=
  ∃ fm b post col, L[i]? = some (.call fm b post col)

/-- The invariant of connection `cid` (to address `a`) with names `γ`; see the file header. -/
def connInv (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) : IProp GF :=
  iprop(∃ (L : List CFrame) (k : Nat) (A : GMap Nat (Option (w64 × GoString × List w8))),
    monoListAuthOwn γ.reqs (1 : Qp).half L ∗ ghostVar γ.ctr (1 : Qp).half k ∗
    ghostMapAuth γ.ans 1 A ∗
    (ghostVar γ.ctr (1 : Qp).half 0 ∨ connFresh cid true) ∗
    ⌜k ≤ L.length ∧ ∀ i, (A !! i).isSome → i < k ∧ isCallAt L i⌝ ∗
    ([∗list] f ∈ L.drop k, frameDeposit W a f) ∗
    ([∗map] i ↦ o ∈ A, answerRes L i o))

/-- Connection `cid` to address `a` has names `γ` and its invariant (persistent). -/
def isGConn (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) : IProp GF :=
  iprop(regElem W cid γ ∗ inv connN (connInv W a cid γ))

/-- What a dialer of `a` writes: a prefix of the frames of the connection's client frames `L`
(persistent lower bound). -/
def reqProto (W : GrpcWorld GF) (a : GoString) : Proto GF := fun cid bs =>
  iprop(∃ (γ : GConnNames) (L : List CFrame), isGConn W a cid γ ∗ monoListLbOwn γ.reqs L ∗
    ⌜(∀ q ∈ cmsgs L, q.length < 2 ^ 63) ∧ bs <+: net.rpc.framesOf (cmsgs L)⌝)

/-- What an acceptor at `a` writes: a prefix of frames answering distinct calls of the
connection, each with its persistent answer. -/
def respProto (W : GrpcWorld GF) (a : GoString) : Proto GF := fun cid bs =>
  iprop(∃ (γ : GConnNames) (Rs : List Ans), isGConn W a cid γ ∗
    ([∗list] x ∈ Rs, ghostMapElem γ.ans x.1 .discard (some x.2)) ∗
    ⌜(Rs.map Prod.fst).Nodup ∧ (∀ q ∈ Rs.map respMsg, q.length < 2 ^ 63) ∧
      bs <+: net.rpc.framesOf (Rs.map respMsg)⌝)

/-- Address `a` serves grpc in world `W`: its protocols, and the registry (persistent). Made
once per address from its unset protocols (`grpcAddr_set`). -/
def grpcAddr (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(addrProto a (reqProto W a) (respProto W a) ∗ inv regN (regInv W))

end proto

end google_golang_org.grpc

end Perennial
