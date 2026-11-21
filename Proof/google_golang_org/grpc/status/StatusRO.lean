/-
A read-only gRPC status, `status.statusAt s c m` (errdesc stage 2a, 2026-11-20; until then
`grpcStatusRO s c` over the opaque `grpcStatusROP`, k8s 7f-5a-P step 5, E1, approved by etcd-grove-81
2026-11-15, and an error's code the pure `statusCode`), declared on its own: a module with no import
beyond GooseLang's values and Iris' propositions, so that the cache's `grpcErrMethodsOk`
(`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) can state the status an error's `GRPCStatus()` returns.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- (opaque; TRUSTED; no law; errdesc stage 2a, 2026-11-20) **`s` is a gRPC `*Status` of code `c` and
message `m`, never written after**: built by `status.New`/`Error` (or grpc's other constructors) and
never written after, so its `Code()` and `Message()` return `c` and `m` on every call (grpc's `*Status`
is not immutable in Go: a whole-struct assignment `*s = *t`, from any package, copies its unexported
fields; protobuf's internal size cache is written by `proto.Marshal`; the fact is a guarantee of the
producer, given by the posts of the uninterpreted producers, through `grpcErrMethodsOk`). A status may
be shared (package-level `status.Error` values: grpc's `ErrClientConnClosing`,
`errContextCanceled`/`errContextDeadline`, etcd's `ErrGRPC*`). An `IProp` of the heap whose names it
takes (`hG`); no law relates two of them (the per-heap rule, `notes/errdesc-ghost-plan.md`). Until
2026-11-20 the opaque pure `grpcStatusROP : Loc → w32 → Prop` with the error's code the pure
`statusCode : GoInterface → w32`, a function of the error value, which no implementation can meet for
the errors it allocates. SpecPlan's `statusAt`. -/
opaque status.statusAtRaw [GooseExts] [GooseSemantics] [GooseInterp] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    (s : Loc) (c : w32) (m : GoString) : IProp GF

/-- **A read-only gRPC status of code `c` and message `m`** (persistent): `s` is not nil, and the
leaf `status.statusAtRaw s c m`. -/
def status.statusAt [GooseExts] [GooseSemantics] [GooseInterp] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    (s : Loc) (c : w32) (m : GoString) : IProp GF :=
  iprop(⌜s ≠ null⌝ ∗ □ status.statusAtRaw s c m)

instance status.statusAt_persistent [GooseExts] [GooseSemantics] [GooseInterp] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] (s : Loc) (c : w32) (m : GoString) :
    Iris.BI.Persistent (status.statusAt (GF := GF) s c m) := by
  unfold status.statusAt; infer_instance

theorem status.statusAt_nonnull [GooseExts] [GooseSemantics] [GooseInterp] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] (s : Loc) (c : w32) (m : GoString) :
    status.statusAt (GF := GF) s c m ⊢ ⌜s ≠ null⌝ := by
  unfold status.statusAt
  iintro ⟨%h, -⟩
  ipureintro; exact h

end EtcdGrove
end Perennial
