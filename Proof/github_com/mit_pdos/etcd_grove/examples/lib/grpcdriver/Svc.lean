/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: its service's table

The driver's one service, `grpcdriver.Driver` (`svc/svc.go`), as gRPC's service table (`GrpcSvc`,
`InvGrpcWire.lean`: heap-free, the same term on both machines), over protobuf's `StringValue`
(`PerTypeStringValue.lean`: `pbStringValueT` for a unary request, `pbStringValueRT` for a unary
reply, `pbStringValueST` on a stream).

**Each call id runs `Echo` at most once** (the client's `unary-reply` check: the reply is `v#1`).
The client hands out ids from a counter; each id comes with an exclusive token `idTok γid id`
(`Defs.lean`). An `Echo` request's deposit carries the token of its value's id (`mkVal id w`, which
determines `id`: `mkVal_inj`); the server's state (`server`'s `mu`) keeps the token of every value it
has run, so a second run of a value would hold two tokens of its id: it does not happen, and the
first run counts `1`.

**The unary methods' specs** (`GrpcSpecMd`: the metadata, the request's model, the reply's
continuation `Φ`, the error's `Ψe`):
* `Echo` (`echoSpec`): on a fresh value `v` with its id's token, `Φ (v ++ "#1")`;
* `Fail` (`failSpec`): `Ψe v` (the handler always fails, with the request's value as its message;
  no reply);
* `Meta` (`metaSpec`): `Φ` of the values the metadata has at `mdKeyS`, joined by `","`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Defs
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.PerTypeStringValue
public import Proof.google_golang_org.grpc.metadata.Outgoing

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

/-- The metadata key the client sets and `Meta` reads back (`grpcdriver.go`'s `mdKeyS`). -/
abbrev mdKeyS : GoString := go!"x-driver"

/-- The service's methods' full names (`svc.go`'s `Driver_*_FullMethodName`). -/
abbrev echoName : GoString := go!"/grpcdriver.Driver/Echo"
abbrev failName : GoString := go!"/grpcdriver.Driver/Fail"
abbrev metaName : GoString := go!"/grpcdriver.Driver/Meta"
abbrev serverStreamName : GoString := go!"/grpcdriver.Driver/ServerStream"
abbrev clientStreamName : GoString := go!"/grpcdriver.Driver/ClientStream"
abbrev bidiName : GoString := go!"/grpcdriver.Driver/Bidi"

/-- The server's address (`grpcdriver.go`'s `Addr`). -/
abbrev drvAddr : GoString := go!"127.0.0.1:7301"

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- A unary request's wire part (`StringValue`). -/
abbrev reqWire : ProtoWire := (pbStringValueT (GF := GF)).toProtoMsg.wire

/-- A unary reply's wire part (`StringValue`). -/
abbrev repWire : ProtoWire := (pbStringValueRT (GF := GF)).toProtoMsg.wire

/-- `Echo`'s spec (see the file header). -/
def echoSpec (γid : GName) : GrpcSpecMd (GF := GF) (pbStringValueT (GF := GF)).toProtoMsg
    (pbStringValueRT (GF := GF)).toProtoMsg :=
  fun _ (v : GoString) (Φ : GoString → IProp GF) _ =>
    iprop(∃ (id : w64) (w : GoString), ⌜v = mkVal id w ∧ wordOk w⌝ ∗
      idTok (GF := GF) γid id ∗ Φ (v ++ go!"#1"))

/-- `Fail`'s spec (see the file header). -/
def failSpec : GrpcSpecMd (GF := GF) (pbStringValueT (GF := GF)).toProtoMsg
    (pbStringValueRT (GF := GF)).toProtoMsg :=
  fun _ (v : GoString) _ (Ψe : GoString → IProp GF) => Ψe v

/-- `Meta`'s spec (see the file header). -/
def metaSpec : GrpcSpecMd (GF := GF) (pbStringValueT (GF := GF)).toProtoMsg
    (pbStringValueRT (GF := GF)).toProtoMsg :=
  fun md _ (Φ : GoString → IProp GF) _ =>
    Φ (go!",".intercalate (metadata.mdVals md mdKeyS))

/-- **The service's table** (unary methods; the streaming methods' entries are to come with the
stream end's statement, T10 of `coordinator-notes`' plan). -/
def drvSvc (γid : GName) : GrpcSvc GF := fun name =>
  if name = echoName then some (.unary ⟨reqWire (GF := GF), repWire (GF := GF), echoSpec γid⟩)
  else if name = failName then some (.unary ⟨reqWire (GF := GF), repWire (GF := GF), failSpec⟩)
  else if name = metaName then some (.unary ⟨reqWire (GF := GF), repWire (GF := GF), metaSpec⟩)
  else none

end specs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end Perennial
