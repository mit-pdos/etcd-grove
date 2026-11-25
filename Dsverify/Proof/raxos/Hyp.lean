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
  `handlerErr`), the class `GrpcWorldHyp V` (over the global ghost state: a world's registry
  can be allocated) and the class `GrpcHyp V` of the specs `grpc.NewServer.spec`,
  `grpc.Server.RegisterService.spec`, `grpc.Server.Serve.spec`, `grpc.WithInsecure.spec`,
  `grpc.Dial.spec`, `grpc.ClientConn.Invoke.spec`, with the lab's statements (`UnarySpec`,
  `GrpcWorld`, `replyOk`, `descOk`, `grpcAddr` defined as there, over the vocabulary), except
  `handlerOk` and `decOk`: the lab's handler held the caller's deposit from the start (its model's
  server runs a handler only on a whole request frame); here `dec` hands it over, as grpc-go runs a
  handler on the request's headers (review #24). `grpcAddr W a` is `Net/`'s `addrProto a (reqProto W a) (respProto W a)` with the
  world's registry: the recorders' addresses get those protocols in the deployment.
* **math/rand** (the lab's `Harness/Proof/math/rand.lean`): `math.rand.Seed.spec` (names only at
  Perennial 47ec64a9d), the class `RandHyp`. (Until 2026-11-24, math-rand-isinit, also the
  package-level `Intn`: Perennial proves it now, `Dsverify/Proof/math/rand/IntnPos.lean`.)
* **`strconv.Atoi`** is no longer a hypothesis: its value spec and the class `AtoiSpec` are in
  `AtoiSpec.lean` (imported here, so the proofs see them), proved in `AtoiProof.lean` over
  Perennial's translation.
* **`sync.Map`** (the lab's `Harness/Proof/sync/Map.lean`; Perennial has no spec): the vocabulary
  `own m M` and the memory's points-to `tp` (`MapVocab`, abstract) and the class `MapHyp` of its
  laws (`ivt`: `tp` is the memory's, `own_timeless`, `own_zero` from the zero map) and the logically atomic specs `sync.Map.Load.spec`, `Store.spec`, `Delete.spec` for
  string keys.


**dsv-fix4** (mit-pdos/etcd-grove#49 fix 4): no longer a statement premise: `RandHyp`, `UtcHyp`, `SortHyp` and `PrintlnHyp` are built in the top-level proof from per-function trust-boundary axioms (`Dsverify/Proof/math/rand/Seed.lean`, `time/Time__UTC.lean`, `sort/Ints.lean`, `fmt/Println.lean`); `PbHyp` (its axiom review refuted it, `notes/axiom-review/dsv-fix4/quepaxa-pb.md`: `msg.marshalPre` admits any value of the runtime fields `state`/`sizeCache`), `GrpcHyp`, `GrpcWorldHyp`, `MapHyp` and the vocabulary `QpVocab` stay premises.
-/
module

public import Dsverify.Proof.raxos.Msg
public import Dsverify.Proof.google_golang_org.grpc.Base
public import Net.Proof.models_lab.pbcodec.Codec
public import GooseLang.Ext.Net.Proto
public import Net.Proof.net.Base
public import Perennial.Proof.context.Base
public import Proof.math.rand.Base
public import Perennial.Proof.fmt.Base
public import Net.Proof.models_lab.Errors
public import Dsverify.Proof.raxos.AtoiSpec

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
error with `Ψ none` (the lab's `Marshal.spec` with its codec). The message's representation is
given back: protobuf-go v1.36.12 writes only the runtime fields `state` (the generated
`ProtoReflect`, `proto/encode.go:111`; `internal/impl/pointer_unsafe.go:207-208`) and `sizeCache`
of each message (`internal/impl/encode.go:67,123,128`, via `proto/encode.go:183-190`'s `Size`
and `codec_field.go:160,164` for sub-messages), atomically, and reads the others. A `msg.pt*`
read with `dq = 1` owns both (the whole struct, existentially); one read with another `dq` keeps
them in an invariant (`msg.pbRtN`), so the stores of concurrent marshals of a shared message are
justified (review #24, finding 2). gRPC's codec (`encoding/proto/proto.go:51-64`: `proto.Size`,
then `Marshal` with `UseCachedSize`) writes the same fields: `PbCodec.marshal` is this
precondition. -/
abbrev proto.Marshal.spec : Prop :=
  ∀ (m : GoInterface) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msg.marshalPre m Ψ }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal)) (Val #m))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err);
      (⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨
      (⌜err ≠ interface.nil⌝ ∗ errAny err ∗ Ψ none) }}

/-- **Hypothesis** `proto.Unmarshal(b, m)` into a fresh message of the program's kinds (the lab's
`Unmarshal.spec` with its codec). The decoded message and its sub-messages are owned (`msg.decInto`:
reps with `dq = 1`, whole structs): protobuf-go writes every field of the fresh message it fills,
runtime fields included, and allocates the sub-messages. -/
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

/-! ## math/rand -/

section rand
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Hypothesis** `Seed(seed)`: nothing (the lab's model's). -/
abbrev math.rand.Seed.spec : Prop :=
  ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! Perennial.math.rand.Seed)) (Val #seed))
    {{ RET #(); True }}

/-- The `math/rand` hypotheses (the lab's model's specs; Perennial proves `Intn`, no longer here,
and leaves `Seed` names only).
Only the package-level functions: QuePaxa's `rand.New(rand.NewSource(..))`/`(*Rand).Intn` run only
in asynchronous mode (`isAsynchronous`), which the deployment never sets (`Proposer/Slots.lean`), so
no spec of them is assumed. -/
class RandHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Seed : math.rand.Seed.spec (GF := GF) (hG := hG)

end rand

/-! ## time.Time.UTC -/

namespace time

section utc
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Hypothesis** `t.UTC()`: some `Time` (the lab's `Time.wp_UTC`; Perennial leaves `Time.UTC`
untranslated, `Perennial/Code/time.toml`). Discharge: Perennial translating `UTC` (its body is
`t.setLoc(&utcLoc)`; `setLoc` is not translated either) and the lab's proof. -/
abbrev Time.UTC.spec : Prop :=
  ∀ (t : Perennial.time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! Perennial.time.Time.ty @!! go!"UTC")) (Val #()))
    {{ (t' : Perennial.time.Time), RET #t'; True }}

end utc

end time

/-- The `time.Time.UTC` hypothesis. -/
class UtcHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  UTC : time.Time.UTC.spec (GF := GF) (hG := hG)

/-! ## sort.Ints -/

namespace sort

section ints
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Hypothesis** `sort.Ints(x)`: the slice's elements permuted into ascending signed order (the
lab's `wp_Ints`, proved there over its own translation of `sort.Ints`, `func Ints(x []int) {
slices.Sort(x) }`, from Perennial's `slices.wp_Sort`; Perennial leaves `sort.Ints` untranslated).
Discharge: Perennial translates `sort.Ints`; the lab's proof (`Harness/Proof/sort/Ints.lean`) then
applies. -/
abbrev Ints.spec : Prop :=
  ∀ (data : GoSlice) (xs : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val (@! Perennial.sort.Ints)) (Val #data))
    {{ (xs' : List w64), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : w64), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → sint.Z xi ≤ sint.Z xj⌝ }}

end ints

end sort

/-- The `sort.Ints` hypothesis. -/
class SortHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Ints : sort.Ints.spec (GF := GF) (hG := hG)

/-! ## fmt.Println -/

namespace fmt

section println
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An operand `Println` may format: `nil` or a well-formed basic value (`fmt.ArgWf`: Go calls no
method of it), or an error whose `Error()` returns some string (`models_lab.errAny`: Go's `%v` of
an `error` calls its `Error()`) and that is not a `fmt.Formatter` (whose `Format` Go would call
first). -/
def printOk (x : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, x = interface.ok ii → Perennial.fmt.ArgWf ii⌝ ∨
    (models_lab.errAny x ∗
      ⌜∀ ii, x = interface.ok ii → go.typeSetContains ii.ty Perennial.fmt.Formatter.ty = false⌝))

instance printOk_persistent (x : GoInterface) : Persistent (printOk (GF := GF) x) := by
  unfold printOk; infer_instance

/-- **Hypothesis** `fmt.Println(a...)` of operands `printOk` allows returns, giving the slice
back; the output is not modelled, nor the results (the lab's `wp_Println_ok`, proved there over
its own model of `fmt`; Perennial leaves `fmt.Println`/`Fprintln` untranslated and has no spec).
Discharge: Perennial translates `Fprintln`/`doPrintln` and proves this from its `printArg` (as
`Printf`'s spec, with `argOk` under `%v`). -/
abbrev Println.spec : Prop :=
  ∀ (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ □ ([∗list] x ∈ xs, printOk x) ∗ arg ↦*{dq} xs }}
      (App (Val (@! Perennial.fmt.Println)) (Val #arg))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); arg ↦*{dq} xs }}

end println

end fmt

/-- The `fmt.Println` hypothesis. -/
class PrintlnHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Println : fmt.Println.spec (GF := GF) (hG := hG)

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
  /-- a dial option that sets the transport's credentials (`WithInsecure()`'s; the lab's model's
  `DialOption.creds = true`) -/
  credsOpt : GoInterface → Prop
  worldOk_persistent : ∀ W, Persistent (worldOk W)
  isServer_persistent : ∀ s γ W a, Persistent (isServer s γ W a)
  isClientConn_persistent : ∀ cc W a, Persistent (isClientConn cc W a)
  handlerErr_persistent : ∀ err, Persistent (handlerErr err)

attribute [instance] GrpcVocab.worldOk_persistent GrpcVocab.isServer_persistent
  GrpcVocab.isClientConn_persistent GrpcVocab.handlerErr_persistent

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [π : NetProtoGS]

/-- Address `a` serves grpc in world `W`: its protocols, and the registry (persistent). -/
def grpcAddr (V : GrpcVocab GF) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(addrProto a (V.reqProto W a) (V.respProto W a) ∗ V.worldOk W)

end addr

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable (V : GrpcVocab GF) [cd : PbCodec GF]

/-- A handler's reply gives the continuation of its encoding: a nil reply is the empty message;
another is encoded by the codec (an encoding failure is an error answer, which needs nothing). -/
def replyOk (reply : GoInterface) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop((⌜reply = interface.nil⌝ ∗ Φ []) ∨
    (⌜reply ≠ interface.nil⌝ ∗ PbCodec.marshal reply (fun o => iprop(∀ bs, ⌜o = some bs⌝ -∗ Φ bs))))

/-- `dec`, the decoding function the server hands the handler of one call with method spec `S`
(one use: not persistent). Called on a message `v`, with the codec's premise for whatever request
bytes arrive: `nil` once the request bytes `bs` arrived and decoded into `v` (`Ψ bs true`), and only
then the caller's deposit `S bs Φ` for them, with `Got Φ`, the call's receipt of its continuation
(what the reply obligation of `handlerOk` is stated for); or an error the server turns into a
status, with `v` decoded or failed (`Ψ bs b`: gRPC checks for the end of the request stream after
decoding) or untouched (the premise back: the request never came). grpc-go v1.84: `dec` is
`stream.RecvMsg` (`server.go`, `wrapUnaryHandler`), which reads the request frame and unmarshals
it with the codec (`stream.go`, `serverStream.RecvMsg`; `rpc_util.go`, `recv`). -/
def decOk (S : UnarySpec GF) (Got : (List w8 → IProp GF) → IProp GF) (dec : GoFunc) :
    IProp GF :=
  iprop(∀ (v : GoInterface) (Ψ : List w8 → Bool → IProp GF) (Θ : val → IProp GF),
    (∀ bs, PbCodec.unmarshal bs v (Ψ bs)) -∗
    ▷ (∀ err : GoInterface,
        ((⌜err = interface.nil⌝ ∗ ∃ (bs : List w8) (Φ : List w8 → IProp GF),
            S bs Φ ∗ Got Φ ∗ Ψ bs true) ∨
          (⌜err ≠ interface.nil⌝ ∗ V.handlerErr err ∗
            ((∃ (bs : List w8) (b : Bool), Ψ bs b) ∨ ∀ bs, PbCodec.unmarshal bs v (Ψ bs)))) -∗
      Θ #err) -∗
    WP (App (Val #dec) (Val #v)) {{ Θ }})

/-- The handler `h` with implementation `impl` meets `S` (persistent): called with any context, a
decoding function `dec` of the call (`decOk`), for any receipt `Got`, and a nil interceptor, it
returns a reply whose encoding gives the continuation `Φ` that `dec` handed over (`Got Φ`), or an
error the server turns into a status. The handler holds nothing of the caller's before `dec`
returns: grpc-go runs it as soon as the request's headers arrive (`server.go`, `processRPC` calls
the wrapped handler before any request bytes are read), and the client sends the headers before it
marshals the request, which can fail (`call.go`, `invoke`; `stream.go`, `clientStream.SendMsg`). -/
def handlerOk (impl : GoInterface) (h : GoFunc) (S : UnarySpec GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cdesc : context.ContextDesc (IProp GF)) (dec : GoFunc)
      (Got : (List w8 → IProp GF) → IProp GF) (Θ : val → IProp GF),
    context.isContext ctx cdesc -∗ decOk V S Got dec -∗
    ▷ (∀ (reply err : GoInterface),
        ((⌜err = interface.nil⌝ ∗ ∃ Φ : List w8 → IProp GF, Got Φ ∗ replyOk reply Φ) ∨
          (⌜err ≠ interface.nil⌝ ∗ V.handlerErr err)) -∗ Θ (PairV #reply #err)) -∗
    WP (App (App (App (App (Val #h) (Val #impl)) (Val #(interface.ok ctx))) (Val #dec))
      (Val #func.nil)) {{ Θ }})

/-- A service descriptor `sd` (read with fraction `dq`, all its fields) whose every method's
handler meets its spec at `a` with implementation `ss`, and which has no streams; its
`HandlerType` is a typed nil pointer to an interface type `T` that `ss` (non-nil) implements:
`RegisterService` evaluates `reflect.TypeOf(sd.HandlerType).Elem()` and checks
`reflect.TypeOf(ss).Implements(ht)` (grpc `server.go`, `RegisterService`; a nil `HandlerType`
or `ss`, or a non-interface `T`, panics, and a `ss` not implementing it is `logger.Fatalf`), and
it reads `Metadata`. -/
def descOk (W : GrpcWorld GF) (a : GoString) (sd : Loc) (dq : DFrac) (name : GoString)
    (ss : GoInterface) : IProp GF :=
  iprop(∃ (msl ssl : GoSlice) (Ms : List google_golang_org.grpc.MethodDesc) (T : go.GoType)
      (md : GoInterface),
    structFieldRef google_golang_org.grpc.ServiceDesc go!"ServiceName" sd ↦{dq} name ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"HandlerType" sd ↦{dq}
      interface.mkOk (go.GoType.PointerType T) #(null : Loc) ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Metadata" sd ↦{dq} md ∗
    ⌜go.isInterfaceType (underlying T) = true ∧
      ∃ ii, ss = interface.ok ii ∧ go.typeSetContains ii.ty T = true⌝ ∗
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

/-- `NewServer()` with no options (QuePaxa's recorder passes none): a server for the world and
address the caller names, with its owner token. -/
abbrev NewServer.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opt : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ ⌜opt.len = W64 0⌝ }}
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

/-- `s.Serve(lis)` on a listener at `la` (from `net.Listen`; `la` may be a wildcard, D21) whose
accepted addresses all carry the protocols of the server's address `a` (`lisProto`, set once by
`lis_set_proto`), with the server's owner token or its served token: it returns only with an
error, and the served token. (The lab's spec took a listener at `a` itself and `grpcAddr V W a`;
the replicas listen at `0.0.0.0:port` and are dialed at `127.0.0.1:port`.) -/
abbrev Server.Serve.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (W : GrpcWorld GF) (a la : GoString) (R : List GoString)
    (li : GoInterface) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ V.isServer s γs W a ∗
      (V.srvOwn γs R ∨ V.srvServed γs) ∗ net.isListener li l ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l la true ∗
      netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      lisProto (Gg := hG.goose_globalGS) la (V.reqProto W a) (V.respProto W a) ∗ V.worldOk W }}
    (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve"))
      (Val #li))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ ∗ V.srvServed γs }}

/-- `WithInsecure()`: a dial option that sets the transport's credentials. -/
abbrev WithInsecure.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithInsecure)) (Val #()))
  {{ (o : GoInterface), RET #o; ⌜V.credsOpt o⌝ }}

/-- The decimal digits of `n`, as a Go string. -/
def decDigits (n : Nat) : GoString :=
  (toString n).toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- A dial target of the shape `127.0.0.1:port` (`port` in `1..65535`): no URL scheme, so gRPC's
`parseTarget` falls back to the default `passthrough` resolver, whose `Build` accepts any
non-empty endpoint, and `determineAuthority` takes it as is. -/
def dialTarget (a : GoString) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ p ≤ 65535 ∧ a = go!"127.0.0.1:" ++ decDigits p

/-- `Dial(a, opts...)` of a gRPC address of the world of the shape `dialTarget` (the lab's
`dialPost`), with options that are all credential options (QuePaxa's one `WithInsecure()`): a
client connection. (`Dial` fails with `errNoTransportSecurity` when no option sets credentials, on
a target it cannot parse or resolve, or with other options' errors; none of these is allowed
here. It does not block, so nothing else fails.) -/
abbrev Dial.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opts : GoSlice) (dq : DFrac) (os : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcAddr (Gg := hG.goose_globalGS) V W a ∗
      ⌜dialTarget a⌝ ∗ ⌜os ≠ [] ∧ ∀ o ∈ os, V.credsOpt o⌝ ∗ opts ↦*{dq} os }}
    (App (App (Val (@! google_golang_org.grpc.Dial)) (Val #a)) (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      opts ↦*{dq} os ∗ ⌜err = interface.nil⌝ ∗ V.isClientConn cc W a }}

/-- `cc.Invoke(ctx, fm, args, reply, opts)`: `nil` after one run of the method's handler at the
server whose `dec` took the encoded request with its deposit `S bs Φ` (`handlerOk`, `decOk`), with
its continuation `Φ rep` and the reply decoded into `reply` (`Θ rep true`); or an error, after at
most one run (the deposit may be lost; the handler may have run with no request at all, when the
encoding fails after the headers went out), with the decoding resource `D` back or a decoding run,
failed or not (gRPC reports a trailer's error status after decoding the reply), and `R` (or the
encoding premise, if nothing was encoded). No call options
(`opts` empty: QuePaxa's generated client passes none; options run arbitrary code). -/
abbrev ClientConn.Invoke.spec : Prop :=
  ∀ (cc : Loc) (W : GrpcWorld GF) (a : GoString) (ctx : GoInterfaceOk)
    (cdesc : context.ContextDesc (IProp GF)) (fm : GoString) (S : UnarySpec GF)
    (args reply : GoInterface) (opts : GoSlice) (Φ : List w8 → IProp GF) (R D : IProp GF)
    (Θ : List w8 → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ V.isClientConn cc W a ∗
      context.isContext ctx cdesc ∗ ⌜W.MS a fm = some S⌝ ∗ ⌜opts.len = W64 0⌝ ∗
      encPre args S Φ R ∗ D ∗
      □ (D -∗ ∀ rep, PbCodec.unmarshal rep reply (Θ rep)) }}
    (App (App (App (App (App (Val (cc @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty
      @!! go!"Invoke")) (Val #(interface.ok ctx))) (Val #fm)) (Val #args)) (Val #reply))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ R ∗ ∃ rep, Φ rep ∗ Θ rep true) ∨
      (⌜err ≠ interface.nil⌝ ∗ errAny err ∗ (R ∨ encPre args S Φ R) ∗
        (D ∨ ∃ (rep : List w8) (b : Bool), Θ rep b)) }}

end defs

/-- **The gRPC hypotheses** (see the file header): the specs (the world's registry is
`GrpcWorldHyp`'s). -/
class GrpcHyp [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [NetProtoGS]
    (V : GrpcVocab GF) [cd : PbCodec GF] : Prop where
  NewServer : NewServer.spec V
  RegisterService : Server.RegisterService.spec V
  Serve : Server.Serve.spec V
  WithInsecure : WithInsecure.spec V
  Dial : Dial.spec V
  Invoke : ClientConn.Invoke.spec V

section world
variable [GooseExts] [GooseInterp]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The gRPC hypothesis on the global ghost state** (the lab's `world_alloc`): a world's
registry exists for any method specs `MS`. Over the global ghost state, not a machine's heap: the
deployment's start (`kit_start`) allocates the registry before any machine runs. -/
class GrpcWorldHyp {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
    (V : GrpcVocab GF) : Prop where
  /-- a world's registry, for the method specs `MS` -/
  world_alloc : ∀ (MS : GoString → GoString → Option (UnarySpec GF)) (E : CoPset),
    ⊢ |={E}=> ∃ reg : GName, V.worldOk ⟨MS, reg⟩

end world

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS]
variable (V : GrpcVocab GF) [cd : PbCodec GF]

instance grpcAddr_persistent (W : GrpcWorld GF) (a : GoString) :
    Persistent (grpcAddr (Gg := hG.goose_globalGS) V W a) := by
  unfold grpcAddr; infer_instance
instance handlerOk_persistent (impl : GoInterface) (h : GoFunc) (S : UnarySpec GF) :
    Persistent (handlerOk V impl h S) := by
  unfold handlerOk; infer_instance

end inst

end grpc

/-! ## `sync.Map` -/

namespace sync

/-- **The vocabulary of the `sync.Map` hypotheses**: `own m M`, the map at `m` holds the string
keys' values `M` (exclusive; abstract), and the typed points-to of a `sync.Map` value, `tp`
(Perennial's generated one is `sorry`: `sync.Map`'s field `internal/sync.HashTrieMap` is an
axiomatized type whose `TypedPointsto`/`IntoValTypedUnderlying` instances are `sorry`; the
instances of `StoreInst.lean`, of high priority, use this one; notes/perennial-changes.md). -/
structure MapVocab [GooseExts] (GF : BundledGFunctors) where
  own : Loc → GMap GoString GoInterface → IProp GF
  tp : TypedPointsto (GF := GF) Perennial.sync.Map

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

/-- **The `sync.Map` hypotheses**: the points-to `V.tp` is the memory's (`ivt`: allocating,
loading and storing a `sync.Map` respect it), a zero map holds nothing, and the specs.

`ivt` is a hypothesis about Perennial's model, not about Go's library: it stands in for Perennial's
`sorry` `TypedPointsto`/`IntoValTypedUnderlying` instances of `internal/sync.HashTrieMap` (the
axiomatized type of `sync.Map`'s field), which no proof here may use (`StoreInst.lean`;
notes/perennial-changes.md). It goes when Perennial gives those instances. -/
class MapHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] (V : MapVocab GF) : Prop where
  ivt : @IntoValTypedUnderlying _ _ _ _ HasLC.hasLC GF hG Perennial.sync.Map
    Perennial.sync.Map.underlying _ V.tp _
  own_timeless : ∀ m M, Timeless (V.own m M)
  own_zero : ∀ m : Loc, ⊢ @typedPointsto GF _ V.tp m (zero_val Perennial.sync.Map) (DFrac.own 1) ==∗
    V.own m ∅
  Load : Map.Load.spec V
  Store : Map.Store.spec V
  Delete : Map.Delete.spec V

attribute [instance] MapHyp.own_timeless

end sync

/-- **The deployment's gRPC vocabulary**, as an instance (data only: the vocabulary the protocol
proof's definitions mention, `netProtos` and the replicas' gRPC clients; the hypotheses about it,
`GrpcHyp QpVocab.grpc`, are premises of the theorems that use them). -/
class QpVocab [GooseExts] (GF : BundledGFunctors) where
  grpc : grpc.GrpcVocab GF
  /-- the `sync.Map` vocabulary of the replicas' batch stores (its points-to `tp` is the
  instance of `sync.Map`'s memory, `StoreInst.lean`) -/
  map : sync.MapVocab GF

end Perennial.raxos.hyp
