/-
The server side of the net/rpc model (`server.go`, Go 1.27.3's `Server` over the model's frame
codec `serverCodec`): the server's representation predicate `isServer`, its registrations, what a
receiver and its methods must meet, and the vocabulary of the specs of `NewServer`,
`Server.{register,Register,RegisterName}`, the free lists, `sendResponse`, `service.call`,
`readRequestHeader`, `readRequest`, `ServeCodec`, `ServeConn` and `Accept`. Ported from
dsverify-lab's `Harness/Proof/net/rpc/{ServerDefs,ServerGhost}.lean` (`348a866`), whose model had
its own server and dispatch; here the server is Go's, the dispatch through the generated codec's
`Receiver` and its `Method`s (`codec.go`).

**Methods** (`methodOk C rcvr Sm mm`, persistent): the `*Method` `mm` of receiver `rcvr` meets the
spec `Sm` of its method (`S m` for the service spec `S`): `NewArg()` returns a non-`nil` argument
`argv` with a decoding resource `D` and its decoding `argDec C argv D Sm Θ`: from `D`, the codec's
`dec` into `argv` of the argument bytes `args` of a deposit `Sm args Φ` (which it keeps), not of
every request body (a generated codec decodes only bytes of the argument's type: its `Decode`
panics `rpcNotModelled` on another listed type's value, and it is the method's spec that says its
deposits' arguments are of that type; the reader holds the request's deposit when it reads the
body, `req_guard`); and, from the deposit `Sm args Φ` and a decoding of `args` into `argv`
(`Θ args true`), the call obligation `callObl`: `NewReply()` returns a `replyv`, and `Call(rcvr, argv, replyv)` returns
`nil` with the encoding of `replyv` into the answer `Φ eb ""`, or an error with its message `msg`
(`errMsg`) and `Φ [] msg` (the encoding again if `msg` is `""`: Go then sends the reply, `callRet`),
or an error whose message is any string (`models_lab.errAny`) with that answer for every message.

**Error answers** (`errOk S`, persistent): the server answers with one of its own error messages
(`srvErrMsg`, `Errs.lean`) a request it does not run: its body did not read or decode, or its
method is not registered; the deposit gives the continuation's `Φ [] msg` then. Go's net/rpc does
send these errors, so a client's continuation must accept them; but only them: a service's own
error messages (a method's `Call`'s, `callRet`) mean what its spec says.

**Receivers** (`rcvrIs C rcvr S nm np rp`, persistent): what reflection tells `register` (the
`*Receiver` `rp` the codec's `Receiver(rcvr)` returns, `C.rcv rcvr`, `Codec.lean`): the type's name
`nm`, whether it is a nil pointer `np`, and its methods, at least one, each meeting `S` (the spec
covers only the receivers `register` accepts: the error paths of `register` that log, `log.Print`
not being modelled by Perennial, are excluded by its premises: `notes/perennial-changes.md`).

**The server** (`isServer s γ`, persistent): `serviceMap` under `mapLock`, whose invariant
keeps the ghost map `γ` equal to it (`svcMapInv`); the free lists of requests and responses under
`reqLock` and `respLock` (`reqChain`, `respChain`: each `*Request`/`*Response` owned, linked by
`next`). A registration (`svcReg γ C name S`, persistent) is the ghost map's element of `name`, the
`*service` holding the receiver and the methods `register` made (`svcIs`): `register` refuses a
name already taken, so the element never changes. `srvServes γ C W a` (persistent): every service
of address `a` in `W` is registered with its spec, which accepts error answers.

**A connection served** (`ServeCodec`): the reader (the loop) reads request `k` (`readerSt`: the
frames of the requests before it, and the reader's count `k` of the connection's `ctr`, claimed with
the acceptor's fresh token at the first request), takes its deposit once (`take_req`,
`ServerGhost.lean`), and either answers it itself with an error or forks its run; the answer of
request `k` is made when its response is written (`ansPend`: the right to answer request `k` once,
its `ans` element still `none`), under `sending`, whose invariant (`srvSendInv`) holds the codec's
write side: what was written is a prefix of the wire of the answers recorded (`ansRec`), all of it
while no write failed.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.net.rpc.Errs
public import Perennial.Proof.sync.WaitGroupTokJoin

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

def srvN : Namespace := rpcN.@"server"
def srvWgN : Namespace := srvN.@"wg"

/-- The payloads of the requests `L` on the wire, the first numbered `n`: for each its header and
its body. -/
def reqPlsFrom : Nat → List RpcReq → List (List w8)
  | _, [] => []
  | n, r :: L => reqHdr (W64 n) r.sm :: r.body :: reqPlsFrom (n + 1) L

/-- The payloads of the requests `L` on the wire: for the `i`-th its header and its body. -/
def reqPls (L : List RpcReq) : List (List w8) := reqPlsFrom 0 L

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Methods and receivers -/

/-- The spec of one method: `Sm args Φ`, the deposit for argument bytes `args` with continuation
`Φ` (a `MethodSpec` at one method name). -/
abbrev MSpec (GF : BundledGFunctors) := List w8 → (List w8 → GoString → IProp GF) → IProp GF

/-- What a method's `Call` returns (`e`), for its reply `replyv` and continuation `Φ`: `nil` and
the encoding of the reply into `Φ eb ""`; or an error with message `msg`, `Φ [] msg` (the
encoding of the reply if `msg` is `""`, which Go sends as a success); or an error whose `Error()`
is any string (`models_lab.errAny`, e.g. a net/rpc client's error the method forwards), with the
same answer for every message it may return: the server calls `Error()` once
(`service.call`), so the method promises only "some message" (non-empty: `Φ [] msg`; empty: Go
sends the reply as a success). -/
def callRet (C : CodecSpec GF) (replyv : GoInterface) (Φ : List w8 → GoString → IProp GF)
    (e : GoInterface) : IProp GF :=
  iprop((⌜e = interface.nil⌝ ∗ C.enc replyv (fun eb => Φ eb [])) ∨
    (∃ msg : GoString, errMsg e msg ∗
      (if msg = [] then C.enc replyv (fun eb => Φ eb []) else Φ [] msg)) ∨
    (models_lab.errAny e ∗ ∀ msg : GoString,
      (if msg = [] then C.enc replyv (fun eb => Φ eb []) else Φ [] msg)))

/-- The call obligation of the method `v` of `rcvr` on the argument `argv`, for the continuation
`Φ`: `NewReply()`, then `Call(rcvr, argv, replyv)` (`callRet`). -/
def callObl (C : CodecSpec GF) (rcvr : GoInterface) (v : net.rpc.Method) (argv : GoInterface)
    (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(WP (App (Val #v.NewReply') (Val #())) {{ fun r => iprop(∃ replyv : GoInterface,
    ⌜r = #replyv⌝ ∗ WP (App (App (App (Val #v.Call') (Val #rcvr)) (Val #argv)) (Val #replyv))
      {{ fun r' => iprop(∃ e : GoInterface, ⌜r' = #e⌝ ∗ callRet C replyv Φ e) }}) }})

/-- What `NewArg` gives for decoding into `argv` from the resource `D`, for the method spec `Sm`
(persistent): a registered codec meeting `C` and, from `D`, the codec's `dec` into `argv` of the
argument bytes `args` of a deposit `Sm args Φ`, kept (the guard: only the arguments a client
deposited for the method), `Θ args` its outcome. -/
def argDec (C : CodecSpec GF) (argv : GoInterface) (D : IProp GF) (Sm : MSpec GF)
    (Θ : List w8 → Bool → IProp GF) : IProp GF :=
  iprop(codecSet C ∗ □ (D -∗ ∀ (args : List w8) (Φ : List w8 → GoString → IProp GF),
    Sm args Φ -∗ Sm args Φ ∗ C.dec args argv (Θ args)))

instance argDec_persistent (C : CodecSpec GF) (argv : GoInterface) (D : IProp GF) (Sm : MSpec GF)
    (Θ : List w8 → Bool → IProp GF) : Persistent (argDec (GF := GF) C argv D Sm Θ) := by
  unfold argDec; infer_instance

/-- The `*Method` `mm` of `rcvr` meets `Sm` (persistent; see the file header). -/
def methodOk (C : CodecSpec GF) (rcvr : GoInterface) (Sm : MSpec GF) (mm : Loc) : IProp GF :=
  iprop(∃ v : net.rpc.Method, mm ↦□ v ∗
    □ ∀ Ψ : val → IProp GF,
      ▷ (∀ (argv : GoInterface) (D : IProp GF) (Θ : List w8 → Bool → IProp GF),
          ⌜argv ≠ interface.nil⌝ -∗ argDec C argv D Sm Θ -∗ D -∗
          (∀ (args : List w8) (Φ : List w8 → GoString → IProp GF), Sm args Φ -∗ Θ args true -∗
            callObl C rcvr v argv Φ) -∗ Ψ #argv) -∗
      WP (App (Val #v.NewArg') (Val #())) {{ Ψ }})

instance methodOk_persistent (C : CodecSpec GF) (rcvr : GoInterface) (Sm : MSpec GF) (mm : Loc) :
    Persistent (methodOk (GF := GF) C rcvr Sm mm) := by
  unfold methodOk; infer_instance

/-- The service spec `S` accepts the server's own error answers (persistent; see the file
header). -/
def errOk (S : MethodSpec GF) : IProp GF :=
  iprop(□ ∀ (m : GoString) (args : List w8) (Φ : List w8 → GoString → IProp GF) (msg : GoString),
    ⌜srvErrMsg msg⌝ -∗ S m args Φ ={⊤}=∗ Φ [] msg)

instance errOk_persistent (S : MethodSpec GF) : Persistent (errOk S) := by
  unfold errOk; infer_instance

/-- The `*Receiver` `rp` of `rcvr` (persistent; see the file header). -/
def rcvrIs (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF) (nm : GoString)
    (np : Bool) (rp : Loc) : IProp GF :=
  iprop(∃ (v : net.rpc.Receiver) (M : GMap GoString Loc), rp ↦□ v ∗
    ⌜v.Name' = nm ∧ v.NilPtr' = np ∧ GMap.size M ≠ 0⌝ ∗ v.Methods' ↦$□ M ∗
    [∗map] m ↦ mm ∈ M, methodOk C rcvr (S m) mm)

instance rcvrIs_persistent (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF)
    (nm : GoString) (np : Bool) (rp : Loc) : Persistent (rcvrIs (GF := GF) C rcvr S nm np rp) := by
  unfold rcvrIs; infer_instance

/-! ## Services and the server -/

/-- The `*methodType` `mt` `register` made for a method of `rcvr` meeting `Sm` (persistent). -/
def methodTypeIs (C : CodecSpec GF) (rcvr : GoInterface) (Sm : MSpec GF) (mt : Loc) : IProp GF :=
  iprop(∃ mm : Loc, structFieldRef net.rpc.methodType go!"m" mt ↦□ mm ∗ methodOk C rcvr Sm mm ∗
    sync.isMutex (structFieldRef net.rpc.methodType go!"Mutex" mt)
      (∃ n : w64, structFieldRef net.rpc.methodType go!"numCalls" mt ↦ n))

instance methodTypeIs_persistent (C : CodecSpec GF) (rcvr : GoInterface) (Sm : MSpec GF)
    (mt : Loc) : Persistent (methodTypeIs (GF := GF) C rcvr Sm mt) := by
  unfold methodTypeIs; infer_instance

/-- The `*service` `sv` `register` made, its methods meeting `S` (persistent). -/
def svcIs (C : CodecSpec GF) (S : MethodSpec GF) (sv : Loc) : IProp GF :=
  iprop(∃ (rcvr : GoInterface) (mp : Loc) (MT : GMap GoString Loc),
    structFieldRef net.rpc.service go!"rcvr" sv ↦□ rcvr ∗
    structFieldRef net.rpc.service go!"method" sv ↦□ mp ∗ mp ↦$□ MT ∗
    [∗map] m ↦ mt ∈ MT, methodTypeIs C rcvr (S m) mt)

instance svcIs_persistent (C : CodecSpec GF) (S : MethodSpec GF) (sv : Loc) :
    Persistent (svcIs (GF := GF) C S sv) := by
  unfold svcIs; infer_instance

/-- A free list of requests from `p`, the requests `rs` (each owned). -/
def reqChain : List Loc → Loc → IProp GF
  | [], p => iprop(⌜p = null⌝)
  | r :: rs, p => iprop(⌜p = r⌝ ∗ ∃ v : net.rpc.Request, r ↦ v ∗ reqChain rs v.next')

/-- A free list of responses from `p`, the responses `rs` (each owned). -/
def respChain : List Loc → Loc → IProp GF
  | [], p => iprop(⌜p = null⌝)
  | r :: rs, p => iprop(⌜p = r⌝ ∗ ∃ v : net.rpc.Response, r ↦ v ∗ respChain rs v.next')

/-- `mapLock`'s invariant: the services map, and the ghost map `γ` equal to it. -/
def svcMapInv (γ : GName) (s : Loc) : IProp GF :=
  iprop(∃ (smp : Loc) (M : GMap GoString Loc), structFieldRef net.rpc.Server go!"serviceMap" s ↦ smp ∗
    smp ↦$ M ∗ ghostMapAuth γ 1 M)

/-- `reqLock`'s invariant. -/
def reqFreeInv (s : Loc) : IProp GF :=
  iprop(∃ (fr : Loc) (rs : List Loc), structFieldRef net.rpc.Server go!"freeReq" s ↦ fr ∗
    reqChain rs fr)

/-- `respLock`'s invariant. -/
def respFreeInv (s : Loc) : IProp GF :=
  iprop(∃ (fr : Loc) (rs : List Loc), structFieldRef net.rpc.Server go!"freeResp" s ↦ fr ∗
    respChain rs fr)

/-- `s` is a server with the registry `γ` (persistent; see the file header). -/
def isServer (s : Loc) (γ : GName) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isMutex (structFieldRef net.rpc.Server go!"mapLock" s) (svcMapInv γ s) ∗
    sync.isMutex (structFieldRef net.rpc.Server go!"reqLock" s) (reqFreeInv s) ∗
    sync.isMutex (structFieldRef net.rpc.Server go!"respLock" s) (respFreeInv s))

instance isServer_persistent (s : Loc) (γ : GName) : Persistent (isServer (GF := GF) s γ) := by
  unfold isServer; infer_instance

/-- The service `name` of the registry `γ` is a `*service` whose methods meet `S`, for good
(persistent). -/
def svcReg (γ : GName) (C : CodecSpec GF) (name : GoString) (S : MethodSpec GF) : IProp GF :=
  iprop(∃ sv : Loc, ghostMapElem γ name .discard sv ∗ svcIs C S sv)

instance svcReg_persistent (γ : GName) (C : CodecSpec GF) (name : GoString) (S : MethodSpec GF) :
    Persistent (svcReg (GF := GF) γ C name S) := by
  unfold svcReg; infer_instance

/-- Every service of `a` in `W` is registered in `γ` with its spec, which accepts error answers
(persistent). -/
def srvServes (γ : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(□ ∀ (svc : GoString) (S : MethodSpec GF), ⌜W.SS a svc = some S⌝ -∗
    svcReg γ C svc S ∗ errOk S)

instance srvServes_persistent (γ : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) :
    Persistent (srvServes (GF := GF) γ C W a) := by
  unfold srvServes; infer_instance

/-- The package's variables the server reads: the client's (`cliEnv`) and the placeholder
`invalidRequest`. -/
def srvEnv : IProp GF :=
  iprop(cliEnv ∗ globalAddr net.rpc.invalidRequest ↦□ ())

instance srvEnv_persistent : Persistent (srvEnv (GF := GF)) := by
  unfold srvEnv; infer_instance

/-! ## A connection served -/

/-- The answers `Rs` written on connection `cn`: none yet, or answers of the connection, each
with its persistent answer. -/
def ansRec (W : RpcWorld GF) (a : GoString) (cn : Nat) (Rs : List Ans) : IProp GF :=
  iprop(⌜Rs = []⌝ ∨ ∃ γ : RpcConnNames, isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
    [∗list] x ∈ Rs, ghostMapElem γ.ans x.idx .discard (some (x.msg, x.reply)))

/-- The invariant of `sending` over the server codec `sc` on the acceptor's end of `cn`, to the
address `a` of world `W`: what was written is a prefix of the handshake's answer and the wire of
the answers `Rs` recorded, all of it while no write failed, or, before the first answer, a prefix of
the handshake's answer (its write may have failed: `ServeHTTP` ignores the error; the first answer
is written only after a request was read, which the dialer wrote only after the whole answer had
been written, `ansPend`'s `sentLb`). -/
def srvSendInv (W : RpcWorld GF) (a : GoString) (cn : Nat) (sc : Loc) : IProp GF :=
  iprop(∃ (w0 : GoInterface) (Wd : List w8) (Rs : List Ans),
    structFieldRef net.rpc.serverCodec go!"werr" sc ↦ w0 ∗
    sendTok (Gg := hG.goose_globalGS) cn true (respProto W a) Wd ∗ ansRec W a cn Rs ∗
    sentLb (Gg := hG.goose_globalGS) cn false (W.hs a) ∗
    ⌜(∀ x ∈ Rs, ansOk x) ∧ Wd <+: W.hsAns a ++ respsWire Rs ∧
      (w0 = interface.nil → Wd = W.hsAns a ++ respsWire Rs ∨ (Rs = [] ∧ Wd <+: W.hsAns a))⌝)

/-- The right to answer request `k` of connection `cn` (`"Service.Method"` `sm`), once, with its
saved continuation `Φ`: its `ans` element, still `none`; and the handshake's answer was written
whole (the dialer wrote the request after it: `reqProto`). -/
def ansPend (W : RpcWorld GF) (a : GoString) (cn : Nat) (k : Nat) (sm : GoString)
    (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(∃ (γ : RpcConnNames) (L : List RpcReq) (r : RpcReq),
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ monoListLbOwn γ.reqs L ∗
    ⌜L[k]? = some r ∧ r.sm = sm ∧ k < 2 ^ 64⌝ ∗
    ghostMapElem γ.ans k (DFrac.own 1) (none : Option (GoString × List w8)) ∗
    savedPredOwn r.post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗
    sentLb (Gg := hG.goose_globalGS) cn true (W.hsAns a))

/-- The reader of `cn` has read the handshake and the frames of the payloads `ps` (each fitting
a frame) and taken `k` requests of the connection: none at first, with the acceptor's fresh token;
then the reader's half of `ctr`, at `k`. -/
def readerSt (W : RpcWorld GF) (a : GoString) (cn : Nat) (ps : List (List w8)) (k : Nat) :
    IProp GF :=
  iprop(recvTok (Gg := hG.goose_globalGS) cn true (reqProto W a) (W.hs a ++ framesOf ps) ∗
    ⌜∀ q ∈ ps, q.length < 2 ^ 63⌝ ∗
    ((⌜k = 0⌝ ∗ connFresh (Gg := hG.goose_globalGS) cn true) ∨
      ∃ γ : RpcConnNames, isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
        ghostVar γ.ctr (1 : Qp).half k))

/-- A connection accepted at `a`, its handshake done (`Accept`'s, with none; `ServeHTTP`'s): the
acceptor's end of `cn`, its tokens (the handshake read, nothing else, and a prefix of its answer
written: all of it, unless the write failed, which `ServeHTTP` does not look at) and its fresh
token. -/
def rpcAccepted (W : RpcWorld GF) (a : GoString) (cn : Nat) : IProp GF :=
  iprop(∃ w : List w8, ⌜w <+: W.hsAns a⌝ ∗
    sendTok (Gg := hG.goose_globalGS) cn true (respProto W a) w ∗
    recvTok (Gg := hG.goose_globalGS) cn true (reqProto W a) (W.hs a) ∗
    connFresh (Gg := hG.goose_globalGS) cn true)

/-! ## The request loop's pieces -/

/-- The server codec `sc` on the acceptor's end of `cn` (the `*TCPConn` `t`) (persistent). -/
def srvCodecAt (sc t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) : IProp GF :=
  iprop(structFieldRef net.rpc.serverCodec go!"rwc" sc ↦□
      interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
    net.connAt (GF := GF) t cn true a la ra)

instance srvCodecAt_persistent (sc t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) :
    Persistent (srvCodecAt (GF := GF) sc t cn a la ra) := by
  unfold srvCodecAt; infer_instance

/-- What answering with the message `errmsg` and the reply `reply` needs, for the continuation `Φ`:
the reply's encoding into `Φ eb ""` for a success (`errmsg = ""`), else `Φ [] errmsg`. -/
def ansRes (C : CodecSpec GF) (errmsg : GoString) (reply : GoInterface)
    (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  if errmsg = [] then C.enc reply (fun eb => Φ eb []) else Φ [] errmsg

/-- The continuation's error answers: `Φ [] msg` for one of the server's own error messages (the
deposit spent by the service's `errOk`). -/
def errCont (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(∀ msg : GoString, ⌜srvErrMsg msg⌝ ={⊤}=∗ Φ [] msg)

/-- A sticky read error of the server codec (persistent): an error with a read error's message
(`errSrv`, `rdErrMsg`), and a pointer (which `==` compares). -/
def rdErr (e : GoInterface) : IProp GF :=
  iprop(errSrv e ∗ ⌜∃ (T : go.GoType) (l : Loc), e = interface.mkOk (go.GoType.PointerType T) #l⌝)

instance rdErr_persistent (e : GoInterface) : Persistent (rdErr (GF := GF) e) := by
  unfold rdErr; infer_instance

/-- The reader's resources at the top of the loop, on the codec `sc` (its `rerr`): no read failed,
and it has read the frames of the first `k` requests (`readerSt`); or a read failed, `rerr` holding
its error, and the reader reads no more. -/
def rdrOwn (W : RpcWorld GF) (a : GoString) (cn : Nat) (sc : Loc) : IProp GF :=
  iprop(∃ r0 : GoInterface, structFieldRef net.rpc.serverCodec go!"rerr" sc ↦ r0 ∗
    ((⌜r0 = interface.nil⌝ ∗ ∃ (ps : List (List w8)) (k : Nat), readerSt W a cn ps k ∗
        ⌜ps.length = 2 * k⌝) ∨
      (⌜r0 ≠ interface.nil⌝ ∗ rdErr r0 ∗ ∃ R : List w8,
        recvTok (Gg := hG.goose_globalGS) cn true (reqProto W a) R)))

/-- The reader mid-request: it has read the frames `ps` of the first `k` requests and the header of
request `k` (`r`, the `k`-th of the connection's lower bound `L`), and taken it. -/
def rdrMid (W : RpcWorld GF) (a : GoString) (cn : Nat) (k : Nat) (r : RpcReq) : IProp GF :=
  iprop(∃ (γ : RpcConnNames) (L : List RpcReq) (ps : List (List w8)),
    recvTok (Gg := hG.goose_globalGS) cn true (reqProto W a)
      (W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm])) ∗
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ monoListLbOwn γ.reqs L ∗
    ghostVar γ.ctr (1 : Qp).half (k + 1) ∗
    ⌜L[k]? = some r ∧ ps.length = 2 * k ∧ (∀ q ∈ ps, q.length < 2 ^ 63) ∧ reqOk r⌝)

/-- A request read and ready to run (`service.call`'s): the service's receiver `rcvr`, the method
`mt` (its `Method` `v`, its counter's mutex), and the call of `v` on the argument `argv` and the
reply `replyv`, answering the continuation `Φ` (`callRet`). -/
def callReady (C : CodecSpec GF) (svc mt : Loc) (argv replyv : GoInterface)
    (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(∃ (rcvr : GoInterface) (mm : Loc) (v : net.rpc.Method),
    structFieldRef net.rpc.service go!"rcvr" svc ↦□ rcvr ∗
    structFieldRef net.rpc.methodType go!"m" mt ↦□ mm ∗ mm ↦□ v ∗
    sync.isMutex (structFieldRef net.rpc.methodType go!"Mutex" mt)
      (∃ n : w64, structFieldRef net.rpc.methodType go!"numCalls" mt ↦ n) ∗
    WP (App (App (App (Val #v.Call') (Val #rcvr)) (Val #argv)) (Val #replyv))
      {{ fun r' => iprop(∃ e : GoInterface, ⌜r' = #e⌝ ∗ callRet C replyv Φ e) }})

/-- The codec's state a served connection starts with, and the acceptor's tokens. -/
def srvCodecOwn (W : RpcWorld GF) (a : GoString) (cn : Nat) (sc : Loc) : IProp GF :=
  iprop(structFieldRef net.rpc.serverCodec go!"werr" sc ↦ interface.nil ∗
    structFieldRef net.rpc.serverCodec go!"rerr" sc ↦ interface.nil ∗
    structFieldRef net.rpc.serverCodec go!"closed" sc ↦ false ∗ rpcAccepted W a cn)

end defs

end net.rpc
end Perennial
