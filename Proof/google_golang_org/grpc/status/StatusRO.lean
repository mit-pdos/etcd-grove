/-
An error's gRPC status code, `statusCode`, and a read-only gRPC status, `grpcStatusRO` (k8s 7f-5a-P
step 5, E1, approved by etcd-grove-81 2026-11-15; `notes/k8s-7f5a-draft.md` §11.2), declared on their
own: a module with no import beyond GooseLang's values and Iris' propositions, so that the cache's
`grpcErrMethodsOk` (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) can state the status an error's
`GRPCStatus()` returns, and `status.FromError.spec` its code. `statusCode` was declared in
`Spec/google_golang_org/grpc/status/FromError.lean` until then, under the same name.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The gRPC status code of an error** (opaque): what `status.FromError(err).Code()` returns.
grpc's `FromError` reads the status embedded in the error value (`GRPCStatus()`, or `Unknown` for
an error that has none, `OK` for `nil`), so the code is a function of the error; nothing more is
said of it. (The watch slice's unit W-C: `isHaltErr` compares it.) -/
opaque statusCode [GooseExts] : GoInterface → w32

/-- The fact behind `grpcStatusRO` (opaque: only the trusted texts that build a status give it). -/
opaque grpcStatusROP : Loc → w32 → Prop

/-- **A read-only gRPC status** (persistent; E1): `s` is a non-nil `*Status` (grpc's
`internal/status.Status`), built by `status.New`/`Error` (or grpc's other constructors) and never
written after, whose `Code()` is `c` and whose `Code()` and `Message()` never change. grpc's
`*Status` is not immutable in Go (a whole-struct assignment `*s = *t`, from any package, copies its
unexported fields; protobuf's internal size cache is written by `proto.Marshal`): the fact is a
guarantee of the producer that built `s` and never writes it after, given by the trusted texts of
the producers (through `grpcErrMethodsOk`). A status may be shared (package-level `status.Error`
values: grpc's `ErrClientConnClosing`, `errContextCanceled`/`errContextDeadline`, etcd's
`ErrGRPC*`). Opaque because grpc's `Status` is an axiomatized type (no points-to can be stated):
the definition is the law `grpcStatusRO s c ⊢ ⌜s ≠ null⌝` and the opaque `grpcStatusROP`. -/
def grpcStatusRO {PROP : Type} [Iris.BI PROP] (s : Loc) (c : w32) : PROP :=
  iprop(⌜s ≠ null ∧ grpcStatusROP s c⌝)

instance grpcStatusRO_persistent {PROP : Type} [Iris.BI PROP] (s : Loc) (c : w32) :
    Iris.BI.Persistent (grpcStatusRO (PROP := PROP) s c) := by
  unfold grpcStatusRO; infer_instance

end EtcdGrove
end Perennial
