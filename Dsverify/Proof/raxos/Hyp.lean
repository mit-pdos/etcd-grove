/-
**The port's hypotheses about libraries with no spec here** (notes/dsv-quepaxa.md, "Hypotheses";
the coordinator's rule for missing model pieces: a spec that is not proved here is a hypothesis,
named after the lab's spec, never an axiom or trusted code). The lab proved each of these of its
own models (`Harness/Proof/{grpc,sync}`); here they are `Prop`s the kit's statement will take as
premises, to be discharged when each piece comes as one shared change:

* **protobuf** (the lab's `Harness/Proof/grpc/Pb.lean`): `proto.Marshal.spec`,
  `proto.Unmarshal.spec` of QuePaxa's messages (`clientwrapper.go`), over the codec of the
  program's messages `qpCodec` (`msg.marshalPre`, `msg.unmarshalPre`): the obligations
  `Net/Proof/models_lab/pbcodec/Codec.lean`'s `PbCodec` describes, met by the real protobuf on
  these messages. The way to discharge them: the kit's codec regenerated with
  `models/protobuf/pbgen.py`, and protobuf's model.
* **gRPC, unary** (the lab's `Harness/Proof/grpc/{Proto,ClientDefs,ServerDefs,Server}.lean`): the
  vocabulary `GrpcVocab` (abstract: what the Lean half of `models/grpc` over `Net/` will define:
  the protocols of a gRPC address `reqProto`/`respProto`, a world's registry `worldOk`, a server
  `isServer`/`srvOwn`/`srvServed`, a client connection `isClientConn`, a handler's error
  `handlerErr`) and the class `GrpcHyp V` of its laws and the specs `grpc.NewServer.spec`,
  `grpc.Server.RegisterService.spec`, `grpc.Server.Serve.spec`, `grpc.WithInsecure.spec`,
  `grpc.Dial.spec`, `grpc.ClientConn.Invoke.spec`, with the lab's statements (`UnarySpec`,
  `GrpcWorld`, `handlerOk`, `decOk`, `replyOk`, `descOk`, `grpcAddr` defined as there, over the
  vocabulary). `grpcAddr W a` is `Net/`'s `addrProto a (reqProto W a) (respProto W a)` with the
  world's registry: the recorders' addresses get those protocols in the deployment.
* **`sync.Map`** (the lab's `Harness/Proof/sync/Map.lean`; Perennial has no spec): the vocabulary
  `ownSyncMap m M` (abstract) and the class `SyncMapHyp` of its laws (`ownSyncMap_zero` from the
  zero map) and the logically atomic specs `sync.Map.Load.spec`, `Store.spec`, `Delete.spec` for
  string keys.
-/
module

public import Dsverify.Proof.raxos.Msg
public import Dsverify.Proof.google_golang_org.grpc.Base
public import Net.Proof.models_lab.pbcodec.Codec
public import GooseLang.Ext.Net.Proto
public import Net.Proof.net.Base
public import Perennial.Proof.context.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos.hyp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open models_lab (errAny)
open models_lab.pbcodec (PbCodec)

/-! ## protobuf -/

section pb
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The codec of QuePaxa's messages (`Msg.lean`): what the program marshals and unmarshals. -/
def qpCodec : PbCodec GF := ⟨msg.marshalPre, msg.unmarshalPre⟩

/-- **Hypothesis** `proto.Marshal(m)` of a message of the program's kinds: its encoding, or an
error with `Ψ none` (the lab's `Marshal.spec` with its codec). -/
abbrev proto.Marshal.spec : Prop :=
  ∀ (m : GoInterface) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msg.marshalPre m Ψ }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal)) (Val #m))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err);
      (⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨
      (⌜err ≠ interface.nil⌝ ∗ errAny err ∗ Ψ none) }}

/-- **Hypothesis** `proto.Unmarshal(b, m)` into a fresh message of the program's kinds (the lab's
`Unmarshal.spec` with its codec). -/
abbrev proto.Unmarshal.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (m : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ b ↦*{dq} bs ∗
      msg.unmarshalPre bs m Ψ }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b)) (Val #m))
  {{ (err : GoInterface), RET #err;
      ∃ ok : Bool, b ↦*{dq} bs ∗ ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok ∗
        (if ok then iprop(True) else errAny err) }}

/-- The protobuf hypotheses, together. -/
class PbHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  marshal : proto.Marshal.spec (GF := GF) (hG := hG)
  unmarshal : proto.Unmarshal.spec (GF := GF) (hG := hG)

end pb

/-! ## gRPC, unary -/

namespace grpc

/-- A unary method spec: `S req Φ` is the deposit for a call with request bytes `req` and
continuation `Φ` (over the reply bytes of a successful run). -/
abbrev UnarySpec (GF : BundledGFunctors) := List w8 → (List w8 → IProp GF) → IProp GF

/-- The grpc world: the method specs of each address (`MS a fm`, the spec of full method `fm`
at address `a`, if it offers it) and the name of the registry of connections. -/
structure GrpcWorld (GF : BundledGFunctors) where
  MS : GoString → GoString → Option (UnarySpec GF)
  reg : GName

/-- The full method name of method `m` of service `svc`. -/
def fullMethod (svc m : GoString) : GoString := go!"/" ++ svc ++ go!"/" ++ m

/-- **The vocabulary of the gRPC hypotheses** (abstract; see the file header). -/
structure GrpcVocab [GooseExts] (GF : BundledGFunctors) where
  /-- what a dialer of a gRPC address of the world writes -/
  reqProto : GrpcWorld GF → GoString → Proto GF
  /-- what an acceptor at a gRPC address of the world writes -/
  respProto : GrpcWorld GF → GoString → Proto GF
  /-- the world's registry exists (persistent) -/
  worldOk : GrpcWorld GF → IProp GF
  /-- `s` is a server for address `a` of the world, with owner names `γ` (persistent) -/
  isServer : Loc → GName → GrpcWorld GF → GoString → IProp GF
  /-- the server's owner token, with the services `R` registered (exclusive) -/
  srvOwn : GName → List GoString → IProp GF
  /-- the server's token after `Serve` ran (exclusive) -/
  srvServed : GName → IProp GF
  /-- `cc` is a client connection to address `a` of the world (persistent) -/
  isClientConn : Loc → GrpcWorld GF → GoString → IProp GF
  /-- an error a handler may return, which the server turns into a status (persistent) -/
  handlerErr : GoInterface → IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable (V : GrpcVocab GF) [cd : PbCodec GF]

/-- Address `a` serves grpc in world `W`: its protocols, and the registry (persistent). -/
def grpcAddr (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(addrProto (Gg := hG.goose_globalGS) a (V.reqProto W a) (V.respProto W a) ∗ V.worldOk W)

/-- A handler's reply gives the continuation of its encoding: a nil reply is the empty message;
another is encoded by the codec (an encoding failure is an error answer, which needs nothing). -/
def replyOk (reply : GoInterface) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop((⌜reply = interface.nil⌝ ∗ Φ []) ∨
    (⌜reply ≠ interface.nil⌝ ∗ PbCodec.marshal reply (fun o => iprop(∀ bs, ⌜o = some bs⌝ -∗ Φ bs))))

/-- `dec` decodes the request bytes `bs` with the codec (persistent). -/
def decOk (dec : GoFunc) (bs : List w8) : IProp GF :=
  iprop(□ ∀ (v : GoInterface) (Ψ : Bool → IProp GF) (Θ : val → IProp GF),
    PbCodec.unmarshal bs v Ψ -∗
    ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ Ψ true) ∨
        (⌜err ≠ interface.nil⌝ ∗ V.handlerErr err ∗ (Ψ false ∨ PbCodec.unmarshal bs v Ψ))) -∗
      Θ #err) -∗
    WP (App (Val #dec) (Val #v)) {{ Θ }})

/-- The handler `h` with implementation `impl` meets `S` (persistent): called with any context, a
decoding function of the request bytes, a nil interceptor and the caller's deposit, it returns a
reply whose encoding gives the continuation, or an error the server turns into a status. -/
def handlerOk (impl : GoInterface) (h : GoFunc) (S : UnarySpec GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cdesc : context.ContextDesc (IProp GF)) (dec : GoFunc)
      (bs : List w8) (Φ : List w8 → IProp GF) (Θ : val → IProp GF),
    context.isContext ctx cdesc -∗ decOk V dec bs -∗ S bs Φ -∗
    ▷ (∀ (reply err : GoInterface), ((⌜err = interface.nil⌝ ∗ replyOk reply Φ) ∨
        (⌜err ≠ interface.nil⌝ ∗ V.handlerErr err)) -∗ Θ (PairV #reply #err)) -∗
    WP (App (App (App (App (Val #h) (Val #impl)) (Val #(interface.ok ctx))) (Val #dec))
      (Val #func.nil)) {{ Θ }})

/-- A service descriptor `sd` (read with fraction `dq`) whose every method's handler meets its
spec at `a` with implementation `ss`, and which has no streams. -/
def descOk (W : GrpcWorld GF) (a : GoString) (sd : Loc) (dq : DFrac) (name : GoString)
    (ss : GoInterface) : IProp GF :=
  iprop(∃ (msl ssl : GoSlice) (Ms : List google_golang_org.grpc.MethodDesc),
    structFieldRef google_golang_org.grpc.ServiceDesc go!"ServiceName" sd ↦{dq} name ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Methods" sd ↦{dq} msl ∗
    msl ↦*{dq} Ms ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams" sd ↦{dq} ssl ∗
    ⌜ssl.len = W64 0⌝ ∗
    □ ∀ (i : Nat) (d : google_golang_org.grpc.MethodDesc) (S : UnarySpec GF),
      ⌜Ms[i]? = some d ∧ W.MS a (fullMethod name d.MethodName') = some S⌝ -∗
      handlerOk V ss d.Handler' S)

/-- What a caller of `Invoke` with spec `S` gives for its request `args`: a nil request (the
empty message) with the deposit `S [] Φ`, or one the codec encodes, the deposit for its
encoding; `R` comes back in every case. -/
def encPre (args : GoInterface) (S : UnarySpec GF) (Φ : List w8 → IProp GF) (R : IProp GF) :
    IProp GF :=
  iprop((⌜args = interface.nil⌝ ∗ S [] Φ ∗ R) ∨
    (⌜args ≠ interface.nil⌝ ∗ PbCodec.marshal args (fun o => match o with
      | some bs => iprop(S bs Φ ∗ R)
      | none => R)))

/-! ### The specs (the lab's statements) -/

/-- `NewServer()`: a server for the world and address the caller names, with its owner token. -/
abbrev NewServer.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opt : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.NewServer)) (Val #opt))
  {{ (s : Loc) (γ : GName), RET #s; V.isServer s γ W a ∗ V.srvOwn γ [] }}

/-- `s.RegisterService(sd, ss)` with the owner token for `R`, a service not registered yet, no
streams, every method's handler meeting its spec: the token for `name :: R`. -/
abbrev Server.RegisterService.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (W : GrpcWorld GF) (a : GoString) (R : List GoString) (sd : Loc)
    (dq : DFrac) (name : GoString) (ss : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ V.isServer s γ W a ∗
      V.srvOwn γ R ∗ ⌜name ∉ R⌝ ∗ descOk V W a sd dq name ss }}
    (App (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!!
      go!"RegisterService")) (Val #sd)) (Val #ss))
  {{ RET #(); V.srvOwn γ (name :: R) ∗ descOk V W a sd dq name ss }}

/-- `s.Serve(lis)` on a listener of `a` (from `net.Listen`), with the server's owner token or its
served token: it returns only with an error, and the served token. -/
abbrev Server.Serve.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (W : GrpcWorld GF) (a : GoString) (R : List GoString)
    (li : GoInterface) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ V.isServer s γs W a ∗
      (V.srvOwn γs R ∨ V.srvServed γs) ∗ net.isListener li l ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
      netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗ grpcAddr V W a }}
    (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve"))
      (Val #li))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ ∗ V.srvServed γs }}

/-- `WithInsecure()`: some dial option. -/
abbrev WithInsecure.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithInsecure)) (Val #()))
  {{ (o : GoInterface), RET #o; True }}

/-- `Dial(a, opts...)` of a gRPC address of the world, with `WithInsecure()`'s option among the
options (as QuePaxa's): a client connection, or an error. -/
abbrev Dial.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opts : GoSlice) (dq : DFrac) (os : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcAddr V W a ∗
      opts ↦*{dq} os }}
    (App (App (Val (@! google_golang_org.grpc.Dial)) (Val #a)) (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      opts ↦*{dq} os ∗
      ((⌜err = interface.nil⌝ ∗ V.isClientConn cc W a) ∨ (⌜err ≠ interface.nil⌝ ∗ errAny err)) }}

/-- `cc.Invoke(ctx, fm, args, reply, opts)`: `nil` after one run of the method's handler at the
server on the encoded request, with its continuation `Φ rep` and the reply decoded into `reply`
(`Θ rep true`); or an error, after at most one run (the deposit may be lost), with the decoding
resource `D` back or a failed decoding, and `R` (or the encoding premise, if nothing was
encoded). -/
abbrev ClientConn.Invoke.spec : Prop :=
  ∀ (cc : Loc) (W : GrpcWorld GF) (a : GoString) (ctx : GoInterfaceOk)
    (cdesc : context.ContextDesc (IProp GF)) (fm : GoString) (S : UnarySpec GF)
    (args reply : GoInterface) (opts : GoSlice) (Φ : List w8 → IProp GF) (R D : IProp GF)
    (Θ : List w8 → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ V.isClientConn cc W a ∗
      context.isContext ctx cdesc ∗ ⌜W.MS a fm = some S⌝ ∗ encPre args S Φ R ∗ D ∗
      □ (D -∗ ∀ rep, PbCodec.unmarshal rep reply (Θ rep)) }}
    (App (App (App (App (App (Val (cc @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty
      @!! go!"Invoke")) (Val #(interface.ok ctx))) (Val #fm)) (Val #args)) (Val #reply))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ R ∗ ∃ rep, Φ rep ∗ Θ rep true) ∨
      (⌜err ≠ interface.nil⌝ ∗ errAny err ∗ (R ∨ encPre args S Φ R) ∗
        (D ∨ ∃ rep, Θ rep false)) }}

end defs

/-- **The gRPC hypotheses** (see the file header): the vocabulary's laws and the specs. -/
class GrpcHyp [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [NetProtoGS]
    (V : GrpcVocab GF) [PbCodec GF] : Prop where
  worldOk_persistent : ∀ W, Persistent (V.worldOk W)
  isServer_persistent : ∀ s γ W a, Persistent (V.isServer s γ W a)
  isClientConn_persistent : ∀ cc W a, Persistent (V.isClientConn cc W a)
  handlerErr_persistent : ∀ err, Persistent (V.handlerErr err)
  /-- a world's registry, for the method specs `MS` -/
  world_alloc : ∀ (MS : GoString → GoString → Option (UnarySpec GF)) (E : CoPset),
    ⊢ |={E}=> ∃ reg : GName, V.worldOk ⟨MS, reg⟩
  NewServer : NewServer.spec V
  RegisterService : Server.RegisterService.spec V
  Serve : Server.Serve.spec V
  WithInsecure : WithInsecure.spec (GF := GF)
  Dial : Dial.spec V
  Invoke : ClientConn.Invoke.spec V

attribute [instance] GrpcHyp.worldOk_persistent GrpcHyp.isServer_persistent
  GrpcHyp.isClientConn_persistent GrpcHyp.handlerErr_persistent

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS]
variable (V : GrpcVocab GF) [cd : PbCodec GF] [GrpcHyp V]

instance grpcAddr_persistent (W : GrpcWorld GF) (a : GoString) : Persistent (grpcAddr V W a) := by
  unfold grpcAddr; infer_instance
instance decOk_persistent (dec : GoFunc) (bs : List w8) : Persistent (decOk V dec bs) := by
  unfold decOk; infer_instance
instance handlerOk_persistent (impl : GoInterface) (h : GoFunc) (S : UnarySpec GF) :
    Persistent (handlerOk V impl h S) := by
  unfold handlerOk; infer_instance

end inst

end grpc

/-! ## `sync.Map` -/

namespace sync

/-- **The vocabulary of the `sync.Map` hypotheses**: `own m M`, the map at `m` holds the string
keys' values `M` (exclusive; abstract). -/
structure MapVocab [GooseExts] (GF : BundledGFunctors) where
  own : Loc → GMap GoString GoInterface → IProp GF

/-- A string key as the interface the map stores. -/
abbrev strKey [GooseExts] [GoGlobalContext] (k : GoString) : GoInterface :=
  interface.mkOk go.string #k

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable (V : MapVocab GF)

/-- `m.Load(k)` for a string key `k`: logically atomic; `(M[k], true)` if `M` has `k`, else
`(nil, false)`. -/
abbrev Map.Load.spec : Prop :=
  ∀ (m : Loc) (k : GoString) (Φ : val → IProp GF),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗
  (AU <{ ∃∃ (M : GMap GoString GoInterface), V.own m M }> @ ⊤, ∅
    <{ V.own m M, COMM Φ (PairV #((M !! k).getD interface.nil) #((M !! k).isSome)) }>) -∗
  WP (App (Val (m @!! go.GoType.PointerType Perennial.sync.Map.ty @!! go!"Load"))
    (Val #(strKey k))) {{ Φ }}

/-- `m.Store(k, v)` for a string key `k`: logically atomic; the contents become `M[k := v]`. -/
abbrev Map.Store.spec : Prop :=
  ∀ (m : Loc) (k : GoString) (v : GoInterface) (Φ : val → IProp GF),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗
  (AU <{ ∃∃ (M : GMap GoString GoInterface), V.own m M }> @ ⊤, ∅
    <{ V.own m (M.insert k v), COMM Φ #() }>) -∗
  WP (App (App (Val (m @!! go.GoType.PointerType Perennial.sync.Map.ty @!! go!"Store"))
    (Val #(strKey k))) (Val #v)) {{ Φ }}

/-- `m.Delete(k)` for a string key `k`: logically atomic; `k` leaves the contents. -/
abbrev Map.Delete.spec : Prop :=
  ∀ (m : Loc) (k : GoString) (Φ : val → IProp GF),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗
  (AU <{ ∃∃ (M : GMap GoString GoInterface), V.own m M }> @ ⊤, ∅
    <{ V.own m (M.delete k), COMM Φ #() }>) -∗
  WP (App (Val (m @!! go.GoType.PointerType Perennial.sync.Map.ty @!! go!"Delete"))
    (Val #(strKey k))) {{ Φ }}

end defs

/-- **The `sync.Map` hypotheses**: a zero map holds nothing, and the specs. -/
class MapHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] (V : MapVocab GF) : Prop where
  own_zero : ∀ m : Loc, ⊢ (m ↦ (zero_val Perennial.sync.Map) : IProp GF) ==∗ V.own m ∅
  Load : Map.Load.spec V
  Store : Map.Store.spec V
  Delete : Map.Delete.spec V

end sync

end Perennial.raxos.hyp
