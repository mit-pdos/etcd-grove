/-
The lab's `net/rpc` vocabulary the swiftpaxos proof is written in (dsverify-lab
`harness/lean/Harness/Proof/net/rpc/{Base,Proto,Defs,ServerDefs,Setup}.lean`), restated over
`Net/`'s `net/rpc` model and its client vocabulary (`Net/Proof/net/rpc`: `RpcWorld`, `MethodSpec`,
`CodecSpec`, `codecSet`, `isClient`, `rpcAddr`, `Client.Call.spec`, `Client.Close.spec`, proved
there), and the statements of the server side and of the HTTP path, which have no proof here
(`*.labSpec`, hypotheses: notes/dsv-swiftpaxos.md, "Hypotheses").

* `RpcCodec GF` (the lab's class): the kit's codec as the specs see it, `enc`/`dec` (its
  `CodecSpec`, `RpcCodec.spec`) and the server's dispatch `call`/`methods`; `RpcNames`.
* `kitCodecOk`: the lab's obligation that the kit's generated codec functions meet `RpcCodec`.
  Over `Net/`'s model the client's obligation is `codecSet RpcCodec.spec` (what `SetCodec`
  gives), and the server's dispatch is in the hypotheses' `Register.labSpec`; so `kitCodecOk` is
  `True` here, kept so the lab's statements read as they did.
* **The HTTP path.** The fork dials the master with `rpc.DialHTTP` and serves with
  `rpc.HandleHTTP` + `http.Serve`: the dialer first writes `CONNECT /_goRPC_ HTTP/1.0\n\n` and
  the acceptor first `HTTP/1.0 200 Connected to Go RPC\n\n` (the lab's `httpReqP`,
  `connectedBytes`). `rpcHttpAddr W a` is `a`'s protocols with those heads in front of `Net/`'s
  `reqProto`/`respProto`, and the registry (`rpcHttpAddr_set` makes it, proved). `DialHTTP.labSpec`
  returns `Net/`'s `isClient`, whose protocol has no head: realizing the hypothesis needs `Net/`'s
  client generalized over a head (a finding).
* The server side (abstract, `SwiftLibs`): `defaultSvcReg name rcvr`, `muxOwner R`, `rpcRouted`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.Bufio
public import Net.Proof.net.rpc.Results
public import Net.Spec.net.rpc.Dial
public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Close

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

namespace net.rpc

/-- The lab's name of an error with some message (`Net/`'s `models_lab.errAny`). -/
abbrev errAny [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
    [HeapGS HasLC.hasLC GF] [go.Semantics] (err : GoInterface) : IProp GF :=
  models_lab.errAny err

/-- The lab's kit (its generated functions' package). -/
class RpcKit where
  pkg : GoString

/-- The kit's generated function `name` (in `RpcKit.pkg`). -/
def kitFn [GooseExts] [GoSemanticsFunctions] [RpcKit] (name : GoString) : GoFunc :=
  functions (RpcKit.pkg ++ go!"." ++ name) []

/-- The codec's encoding and decoding, as `Net/`'s `CodecSpec`. -/
def RpcCodec.spec [GooseExts] {GF : BundledGFunctors} [C : RpcCodec GF] : CodecSpec GF :=
  ⟨C.enc, C.dec⟩

/-- The service names of the kit's receivers, as `Register` sees them. -/
class RpcNames [GooseExts] where
  name : GoInterface → GoString

/-- The rpc path of `DialHTTP` and `HandleHTTP`. -/
def rpcPath : GoString := go!"/_goRPC_"

/-- The request head a client of path `p` writes. -/
def connectHead (p : GoString) : GoString := go!"CONNECT " ++ p ++ go!" HTTP/1.0\n\n"

/-- The response head the acceptor writes. -/
def connectedBytes : GoString := go!"HTTP/1.0 200 Connected to Go RPC\n\n"

section node
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [RpcCodec GF]

/-- The lab's `kitCodecOk`: see the file header (`True` over `Net/`'s model). -/
def kitCodecOk : IProp GF := iprop(True)

instance kitCodecOk_persistent : Persistent (kitCodecOk (GF := GF)) := by
  unfold kitCodecOk; infer_instance

/-- The receiver meets the method spec `S` through the codec's dispatch, for every answer
(persistent; the lab's `rcvrOk`). -/
def rcvrOk (rcvr : GoInterface) (S : MethodSpec GF) : IProp GF :=
  iprop(□ ∀ (m : GoString) (args : List w8) (Φ : List w8 → GoString → IProp GF),
    S m args Φ -∗
    RpcCodec.call rcvr m args (fun reply msg found => iprop(⌜found = true⌝ ∗ Φ reply msg)))

instance rcvrOk_persistent (rcvr : GoInterface) (S : MethodSpec GF) :
    Persistent (rcvrOk (GF := GF) rcvr S) := by
  unfold rcvrOk; infer_instance

/-- The `net.Conn` `cv` holds the `*TCPConn` of end `side` of connection `cn`, the library's
(the lab's `connIface`, over `Net/`'s `connAt` and `connIs`; persistent). -/
def connIface [π : NetProtoGS] (cv : GoInterface) (cn : Nat) (side : Bool) : IProp GF :=
  iprop(∃ (t : Loc) (a : GoString) (la ra : GoInterface),
    ⌜cv = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t⌝ ∗
    net.connAt t cn side a la ra ∗ connIs (Gg := hG.goose_globalGS) cn)

instance connIface_persistent [π : NetProtoGS] (cv : GoInterface) (cn : Nat) (side : Bool) :
    Persistent (connIface (GF := GF) cv cn side) := by
  unfold connIface; infer_instance

end node

section http
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What a dialer of an address serving path `p` writes: a prefix of `connectHead p`, or the
head and then bytes meeting `Pb` (the lab's `net.http.httpReqP`). -/
def httpReqP (p : GoString) (Pb : Proto GF) : Proto GF := fun cn bs =>
  iprop(⌜bs <+: connectHead p⌝ ∨ ∃ rest, ⌜bs = connectHead p ++ rest⌝ ∗ Pb cn rest)

/-- What an acceptor answering an rpc dial writes: a prefix of `connectedBytes`, or them and then
bytes meeting `Pb`. -/
def httpRespP (Pb : Proto GF) : Proto GF := fun cn bs =>
  iprop(⌜bs <+: connectedBytes⌝ ∨ ∃ rest, ⌜bs = connectedBytes ++ rest⌝ ∗ Pb cn rest)

/-- Address `a` serves rpc over HTTP in world `W`: `Net/`'s rpc protocols behind the heads, and the
registry (persistent). -/
def rpcHttpAddr (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(addrProto (Gg := Gg) a (httpReqP rpcPath (reqProto W a)) (httpRespP (respProto W a)) ∗
    inv regN' (regInv (Gg := Gg) W))

instance rpcHttpAddr_persistent (W : RpcWorld GF) (a : GoString) :
    Persistent (rpcHttpAddr (Gg := Gg) W a) := by
  unfold rpcHttpAddr; infer_instance

end http

end net.rpc

namespace bufio

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [errors.Assumptions] [net.rpc.Assumptions] [net.FieldAssumptions]
variable [net.Assumptions]

/-- A variable made by `errors.New` holds an error with some message (the lab's
`bufio.newVar_errOrNil`, over `Net/`'s `errAny_newVar`). -/
theorem newVar_errOrNil (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ e : GoInterface, globalAddr X ↦□ e ∗ errOrNil e ∗ ⌜e ≠ interface.nil⌝ := by
  iintro #HNP
  ihave #HNP' := HNP
  iunfold errors.newVar at HNP'
  icases HNP' with ⟨%x, #Hx, -⟩
  ihave #Ha := net.rpc.errAny_newVar _ _ _ $$ HNP Hx
  iexists _
  iframe Hx
  isplitl
  · iunfold errOrNil; iright
    isplitl
    · iexact Ha
    ipureintro
    intro e' h T _
    cases h
    exact ⟨x, rfl⟩
  ipureintro; simp [interface.mkOk]

end lemmas

end bufio

end Perennial
