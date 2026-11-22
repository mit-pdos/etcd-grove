/-
The client side of the net/rpc model (`client.go`, Go 1.27.3's `Client` over the model's frame
codec `clientCodec`): the client's representation predicate `isClient`, its lock invariants and
ghost state, and the vocabulary of the specs of `Client.{send,input,Go,Call,Close}`, `Call.done`,
`NewClient(WithCodec)` and `Dial`. Ported from dsverify-lab's `Harness/Proof/net/rpc/ClientDefs.lean`
(`348a866`), whose model had its own client; here the client is Go's, so the invariants follow
Go's locks (`reqMutex` for the request and the codec's write side, `mutex` for `seq`, `pending`,
`closing`, `shutdown`).

**Sequence numbers.** `send` numbers a call (`seq`) under `mutex` and writes its request under
`reqMutex`, which it holds across both: the `n`-th request written has the sequence number `n`
(`connInv`'s order, `Proto.lean`), until a write fails (the codec's sticky `werr`), after which
nothing more is written. Fewer than `2 ^ 64` calls are numbered: `mutex`'s invariant holds one
time receipt per number issued (`⧗ n`, Perennial's `GooseLang/Receipts.lean`, under the premise
`receiptBound GF ≤ 2 ^ 64` that `NewClientWithCodec` takes), so the numbers are distinct.

**A pending call** (`callRes`, with its entry of the `pending` map, in `mutex`'s invariant while
the client is not shut down): its `*Call`'s fields (read-only but `Error`), the promise of its
`done` channel (`Fulfill` of Perennial's future idiom) with the caller's way to fulfil it from
the call's outcome, the caller's saved continuation `post`, its collection token `col` (traded for
the answer's continuation, `answerRes`), its names recorded in the connection (`nm`, `Proto.lean`),
the decoding resource `D` and its decoding into the reply. The reader removes an entry before it
answers it, so a call is answered at most once.

**The outcome** a call's `done` channel carries (`callPost`): `nil` with the method's answer `Φ rep
""` and the reply decoded (`Θ rep true`); `ServerError(msg)` (`msg ≠ ""`) with the method's answer
`Φ rep msg` and `D` back; or another error, not a `ServerError`, with `D` back or a failed decoding
(`Θ rep false`). An answer comes with `reqSent`: the call's request was written (the connection's
request list holds its number). A call is numbered on a ticket (`ticket γt o`, `o` the number or
`none` if `send` refused it, the caller's write-once ghost cell): `send`'s result (`sendRes`) is
the encoding's `Rargs`, or, when nothing was encoded, the encoding premise back with the request's
unused token (`unsent`), which no `reqSent` of the same number can meet (`unsent_reqSent`, in the
proofs). So `Call` returns what dsverify's `Client.Call.spec` says.
-/
module

public import Net.Proof.net.rpc.Proto
public import Net.Spec.net.rpc.clientCodec__ReadResponseBody
public import Net.Spec.net.rpc.clientCodec__WriteRequest
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Perennial.GooseLang.Receipts
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

/-- The ghost names of a client: its connection's (`Proto.lean`), the numbers issued (`sq`, a ghost
variable, halves in `mutex`'s and `reqMutex`'s invariants), and whether it is shut down (`down`,
a half in `mutex`'s invariant, a quarter in `reqMutex`'s and one with the reader while it runs:
the reader shuts the client down holding both locks, so the holder of either knows). -/
structure ClientNames where
  conn : RpcConnNames
  sq : GName
  down : GName

def cliN : Namespace := rpcN.@"client"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Errors -/

/-- `err` is a non-nil error whose `Error()` returns `msg` (persistent). -/
def errMsg (err : GoInterface) (msg : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ ⌜go.typeSetContains e.ty go.error = true⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errMsg_persistent (err : GoInterface) (msg : GoString) :
    Persistent (errMsg (GF := GF) err msg) := by
  unfold errMsg; infer_instance

/-- The package's variables the client reads, as the package initialization leaves them: `io`'s
errors, `poll.ErrDeadlineExceeded`, `errFrame` and `ErrShutdown` (`errors.New`'s), and `debugLog`
(`false`). -/
def cliEnv : IProp GF :=
  iprop(∃ eof ueof ed : GoInterface, isPkgInit (PROP := IProp GF) pkg_id.io ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
    errors.newVar net.rpc.errFrame go!"rpc: malformed frame" ∗
    errors.newVar net.rpc.ErrShutdown go!"connection is shut down" ∗
    globalAddr net.rpc.debugLog ↦□ false)

instance cliEnv_persistent : Persistent (cliEnv (GF := GF)) := by
  unfold cliEnv; infer_instance

/-! ## Calls -/

/-- The read-only fields of the `*Call` `pc`. -/
def callFields (pc : Loc) (sm : GoString) (args reply : GoInterface) (ch : Loc) : IProp GF :=
  iprop(structFieldRef net.rpc.Call go!"ServiceMethod" pc ↦□ sm ∗
    structFieldRef net.rpc.Call go!"Args" pc ↦□ args ∗
    structFieldRef net.rpc.Call go!"Reply" pc ↦□ reply ∗
    structFieldRef net.rpc.Call go!"Done" pc ↦□ ch)

instance callFields_persistent (pc : Loc) (sm : GoString) (args reply : GoInterface) (ch : Loc) :
    Persistent (callFields (GF := GF) pc sm args reply ch) := by
  unfold callFields; infer_instance

/-- The call's number on its ticket `γt` (persistent): `some s` once `send` numbered it `s`, `none`
if it refused it (the client was shut down or closing). -/
def ticket (γt : GName) (o : Option Nat) : IProp GF := ghostMapElem γt () .discard o

instance ticket_persistent (γt : GName) (o : Option Nat) : Persistent (ticket (GF := GF) γt o) := by
  unfold ticket; infer_instance

/-- The request numbered `o` was written: the connection's request list holds it. -/
def reqSent (γ : RpcConnNames) (o : Option Nat) : IProp GF :=
  match o with
  | none => iprop(False)
  | some s => iprop(∃ L : List RpcReq, monoListLbOwn γ.reqs L ∗ ⌜s < L.length⌝)

instance reqSent_persistent (γ : RpcConnNames) (o : Option Nat) :
    Persistent (reqSent (GF := GF) γ o) := by
  cases o <;> unfold reqSent <;> infer_instance

/-- The request numbered `o` was not written, for good: its token, which writing it gives up. -/
def unsent (γ : RpcConnNames) (o : Option Nat) : IProp GF :=
  match o with
  | none => iprop(True)
  | some s => iprop(∃ p c ap : GName, ghostMapElem γ.nm s .discard (p, c, ap) ∗ token ap)

/-- What a call's `done` channel carries (see the file header). -/
def callPost (γ : RpcConnNames) (o : Option Nat) (Φ : List w8 → GoString → IProp GF)
    (Θ : List w8 → Bool → IProp GF) (D : IProp GF) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ reqSent γ o ∗ ∃ rep, Φ rep [] ∗ Θ rep true) ∨
    (∃ msg : GoString, ⌜msg ≠ [] ∧ err = serverErr msg⌝ ∗ reqSent γ o ∗ (∃ rep, Φ rep msg) ∗ D) ∨
    (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ models_lab.errAny err ∗
      (D ∨ reqSent γ o ∗ ∃ rep, Θ rep false)))

/-- What `send` returns (see the file header): the encoding's `Rargs`, or the encoding premise
`E` back with the request unsent. -/
def sendRes (γ : RpcConnNames) (o : Option Nat) (Rargs E : IProp GF) : IProp GF :=
  iprop(Rargs ∨ (E ∗ unsent γ o))

/-- What the caller of `Go` prepares for its call, for the `*Call` `pc` that `Go` makes: its
ticket `γt` (the cell's authority, still unwritten), the promise `Fulfill γf K` of its `done`
channel `ch`, and how the call's outcome fulfils it. -/
def callDone (γ : RpcConnNames) (γt : GName) (sm : GoString) (args reply : GoInterface)
    (ch : Loc) (γf : FutureNames) (K : Loc → IProp GF) (Φ : List w8 → GoString → IProp GF)
    (Θ : List w8 → Bool → IProp GF) (D : IProp GF) : IProp GF :=
  iprop(isFuture Loc γf ch ∗ Fulfill γf K ∗
    ∀ (pc : Loc) (o : Option Nat) (err : GoInterface), callFields pc sm args reply ch -∗
      ticket γt o -∗ structFieldRef net.rpc.Call go!"Error" pc ↦ err -∗
      callPost γ o Φ Θ D err -∗ K pc)

/-- A pending call `pc` numbered `s` (see the file header). -/
def callRes (γ : RpcConnNames) (s : w64) (pc : Loc) : IProp GF :=
  iprop(∃ (sm : GoString) (args reply : GoInterface) (ch : Loc) (γt : GName) (γf : FutureNames)
      (K : Loc → IProp GF) (Φ : List w8 → GoString → IProp GF) (Θ : List w8 → Bool → IProp GF)
      (D : IProp GF) (C : CodecSpec GF) (post col ap : GName) (e0 : GoInterface),
    callFields pc sm args reply ch ∗ structFieldRef net.rpc.Call go!"Error" pc ↦ e0 ∗
    ticket γt (some (uint.nat s)) ∗ callDone γ γt sm args reply ch γf K Φ Θ D ∗
    savedPredOwn post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ token col ∗
    ghostMapElem γ.nm (uint.nat s) .discard (post, col, ap) ∗
    D ∗ bodyDec C reply D Θ ∗ ⌜reply ≠ interface.nil⌝)

/-! ## The client's invariants -/

/-- The invariant of `mutex` (see the file header). -/
def muInv (γ : ClientNames) (c : Loc) : IProp GF :=
  iprop(∃ (sq : w64) (n : Nat) (mp : Loc) (m : GMap w64 Loc) (sd cls : Bool)
      (NM : GMap Nat (GName × GName × GName)),
    structFieldRef net.rpc.Client go!"seq" c ↦ sq ∗ structFieldRef net.rpc.Client go!"pending" c ↦ mp ∗
    mp ↦$ m ∗ structFieldRef net.rpc.Client go!"shutdown" c ↦ sd ∗
    structFieldRef net.rpc.Client go!"closing" c ↦ cls ∗
    ghostVar γ.sq (1 : Qp).half n ∗ ⧗ n ∗ ⌜sq = W64 n ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
    ghostVar γ.down (1 : Qp).half sd ∗
    ghostMapAuth γ.conn.nm 1 NM ∗ ⌜∀ i, (NM.lookup i).isSome → i < n⌝ ∗
    (if sd then iprop(True) else iprop([∗map] s ↦ pc ∈ m, callRes γ.conn s pc)))

/-- The invariant of `reqMutex` over the codec `cc` and the dialer's end of `cn`, to the address
`a` of world `W` (see the file header). -/
def sendInv (γ : ClientNames) (c cc : Loc) (cn : Nat) (W : RpcWorld GF) (a : GoString) :
    IProp GF :=
  iprop(∃ (rq : net.rpc.Request) (w0 : GoInterface) (L : List RpcReq) (Wd : List w8) (n : Nat),
    structFieldRef net.rpc.Client go!"request" c ↦ rq ∗
    structFieldRef net.rpc.clientCodec go!"werr" cc ↦ w0 ∗
    sendTok (Gg := hG.goose_globalGS) cn false (reqProto W a) Wd ∗
    monoListAuthOwn γ.conn.reqs (1 : Qp).half L ∗ ghostVar γ.sq (1 : Qp).half n ∗
    (∃ sd : Bool, ghostVar γ.down (1 : Qp).half.half sd) ∗
    (⌜w0 = interface.nil⌝ ∨ ⌜notServerErr w0⌝ ∗ models_lab.errAny w0) ∗
    ⌜(∀ r ∈ L, reqOk r) ∧ L.length ≤ n ∧ Wd <+: reqsWire L ∧
      (w0 = interface.nil → Wd = reqsWire L ∧ L.length = n)⌝)

/-- `c` is an rpc client of address `a` in world `W`, with names `γ`, over the model's codec `cc`
on the dialer's end of `cn` (the `*TCPConn` `t`) (persistent). -/
def clientAt (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames) (cc t : Loc)
    (cn : Nat) (la ra : GoInterface) : IProp GF :=
  iprop(structFieldRef net.rpc.Client go!"codec" c ↦□
      interface.mkOk (go.GoType.PointerType net.rpc.clientCodec.ty) #cc ∗
    structFieldRef net.rpc.clientCodec go!"rwc" cc ↦□
      interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
    net.connAt (GF := GF) t cn false a la ra ∗ connIs (Gg := hG.goose_globalGS) cn ∗
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ.conn ∗ cliEnv ∗
    sync.isMutex (structFieldRef net.rpc.Client go!"reqMutex" c) (sendInv γ c cc cn W a) ∗
    sync.isMutex (structFieldRef net.rpc.Client go!"mutex" c) (muInv γ c))

/-- `c` is an rpc client of address `a` in world `W`, with names `γ` (persistent). -/
def isClientN (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames) : IProp GF :=
  iprop(∃ (cc t : Loc) (cn : Nat) (la ra : GoInterface), clientAt c W a γ cc t cn la ra)

/-- `c` is an rpc client of address `a` in world `W` (persistent). -/
def isClient (c : Loc) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ γ : ClientNames, isClientN c W a γ)

/-- The reader's resources (`input`): it has read the frames of the answers `C` it consumed, and
the client is not shut down. -/
def readerOwn (γ : ClientNames) (cn : Nat) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ C : List Ans,
    recvTok (Gg := hG.goose_globalGS) cn false (respProto W a) (framesOf (C.flatMap ansPls)) ∗
    ghostVar γ.down (1 : Qp).half.half false ∗ ⌜∀ x ∈ C, ansOk x⌝)

instance clientAt_persistent (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames)
    (cc t : Loc) (cn : Nat) (la ra : GoInterface) : Persistent (clientAt c W a γ cc t cn la ra) := by
  unfold clientAt; infer_instance

instance isClientN_persistent (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames) :
    Persistent (isClientN c W a γ) := by
  unfold isClientN; infer_instance

instance isClient_persistent (c : Loc) (W : RpcWorld GF) (a : GoString) :
    Persistent (isClient c W a) := by
  unfold isClient; infer_instance

/-- A connection just dialed to `a` and registered in `W` (`dialRpc`, `Dial`'s): the dialer's
end, its tokens (nothing written or read yet), the request list's half and the names' authority. -/
def rpcDialed (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) : IProp GF :=
  iprop(isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
    monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗
    ghostMapAuth γ.nm 1 (∅ : GMap Nat (GName × GName × GName)) ∗
    sendTok (Gg := hG.goose_globalGS) cn false (reqProto W a) [] ∗
    recvTok (Gg := hG.goose_globalGS) cn false (respProto W a) [])

end defs

end net.rpc
end Perennial
