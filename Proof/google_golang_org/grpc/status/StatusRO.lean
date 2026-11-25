/-
A read-only gRPC status, `status.statusAt s c m` (errdesc stage 2a, 2026-11-20; until then
`grpcStatusRO s c` over the opaque `grpcStatusROP`, k8s 7f-5a-P step 5, E1, approved by etcd-grove-81
2026-11-15, and an error's code the pure `statusCode`), and the status a `*status.Error` holds,
`status.grpcStatusIs` (status-bodies, 2026-11-25), declared on their own: a module with no import
beyond GooseLang's values, Iris' propositions and the translated types, so that the cache's
`grpcErrMethodsOk` (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) can state the status of an error.
-/
module

public import Perennial.Golang.Theory
public import GeneratedProof.google_golang_org.grpc.internal.status
public import GeneratedProof.google_golang_org.genproto.googleapis.rpc.status

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`s` is a gRPC `*Status` of code `c` and message `m`, never written after** (status-bodies,
2026-11-25: a definition, over the translated `internal/status.Status` and genproto's `Status`; until
then an opaque, TRUSTED, of no law): `s`'s field `s` (`internal/status/status.go`, `type Status struct
{ s *spb.Status }`) holds a non-nil `p` for good, and `p`'s fields `Code` and `Message` hold `c` and
`m` for good, so that `Code()` and `Message()` return `c` and `m` on every call. Persistent points-to:
a producer that builds `s` (`status.New`/`Error`, grpc's other constructors) and never writes those
fields after gives them up. True of grpc (v1.84.0, the model `models/grpc`): `internal/status` writes
`Status.s` only in its constructors (`New`, `FromProto` and `NewWithProto` store a fresh or cloned
`*spb.Status`; `Proto()` returns a clone; `WithDetails` builds a new `Status`), `internal/status` is
not importable outside grpc, and the one function that hands out the raw `*spb.Status`,
`RawStatusProto`, has two callers in the model, `model_transport.go:1087` and `:1325`, which only
read `GetDetails()` and pass it to `proto.Marshal`, which writes its `sizeCache` (another field), not
`Code` or `Message` (#24 7175520513, the condition of the approval). A status may be shared
(package-level `status.Error` values: grpc's `ErrClientConnClosing`, `errContextCanceled`/
`errContextDeadline`, etcd's `ErrGRPC*`). Two of them at one `s` agree (`statusAt_agree`). Until
2026-11-20 the opaque pure `grpcStatusROP : Loc → w32 → Prop` with the error's code the pure
`statusCode : GoInterface → w32`. SpecPlan's `statusAt`. -/
def status.statusAtRaw (s : Loc) (c : w32) (m : GoString) : IProp GF :=
  iprop(∃ p : Loc, ⌜p ≠ null⌝ ∗
    s.[google_golang_org.grpc.internal.status.Status, go!"s"] ↦□ p ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Code"] ↦□ c ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Message"] ↦□ m)

instance status.statusAtRaw_persistent (s : Loc) (c : w32) (m : GoString) :
    Iris.BI.Persistent (status.statusAtRaw (GF := GF) s c m) := by
  unfold status.statusAtRaw; infer_instance

/-- **A read-only gRPC status of code `c` and message `m`** (persistent): `s` is not nil, and the
leaf `status.statusAtRaw s c m`. -/
def status.statusAt (s : Loc) (c : w32) (m : GoString) : IProp GF :=
  iprop(⌜s ≠ null⌝ ∗ □ status.statusAtRaw s c m)

instance status.statusAt_persistent (s : Loc) (c : w32) (m : GoString) :
    Iris.BI.Persistent (status.statusAt (GF := GF) s c m) := by
  unfold status.statusAt; infer_instance

theorem status.statusAt_nonnull (s : Loc) (c : w32) (m : GoString) :
    status.statusAt (GF := GF) s c m ⊢ ⌜s ≠ null⌝ := by
  unfold status.statusAt
  iintro ⟨%h, -⟩
  ipureintro; exact h

open Iris.ProofMode in
/-- **Two read-only statuses at one `s` agree** on the code and the message (the persistent points-to
agree). -/
theorem status.statusAt_agree (s : Loc) (c c' : w32) (m m' : GoString) :
    status.statusAt (GF := GF) s c m ⊢ status.statusAt s c' m' -∗ ⌜c = c' ∧ m = m'⌝ := by
  unfold status.statusAt status.statusAtRaw
  iintro ⟨-, #⟨%p, -, #Hs, #Hc, #Hm⟩⟩ ⟨-, #⟨%p', -, #Hs', #Hc', #Hm'⟩⟩
  icombine Hs Hs' gives %hp
  subst hp
  icombine Hc Hc' gives %hc
  icombine Hm Hm' gives %hm
  ipureintro; exact ⟨hc, hm⟩

/-- **`e` is a `*status.Error` holding the read-only status `s` of code `c` and message `m`**
(persistent; status-bodies, 2026-11-25): its dynamic type is `*internal/status.Error`, its value a
pointer `l` whose field `s` holds `s` for good (`&Error{s: s}`, built by `(*Status).Err()` and never
written after: `internal/status` writes `Error.s` nowhere else), and `statusAt s c m`. What an error
with grpc's `GRPCStatus() *Status` is (`grpcErrMethodsOk`, `descIs`, `statusCodeIs`): until then a WP of
its `GRPCStatus()` returning `s`, one per fact, which no proof of a function calling `GRPCStatus()` once
could make agree (#24 7175612915). In grpc (the model) and in the code translated here, `*Error` is the
only type with that method (`internal/status/status.go:216`). -/
def status.grpcStatusIs (e : GoInterfaceOk) (s : Loc) (c : w32) (m : GoString) :
    IProp GF :=
  iprop(⌜e.ty = go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty⌝ ∗
    ∃ l : Loc, ⌜e.v = #l⌝ ∗ l.[google_golang_org.grpc.internal.status.Error, go!"s"] ↦□ s ∗
      status.statusAt s c m)

instance status.grpcStatusIs_persistent (e : GoInterfaceOk) (s : Loc)
    (c : w32) (m : GoString) : Iris.BI.Persistent (status.grpcStatusIs (GF := GF) e s c m) := by
  unfold status.grpcStatusIs; infer_instance

open Iris.ProofMode in
/-- The status a `*status.Error` holds is read-only. -/
theorem status.grpcStatusIs_statusAt (e : GoInterfaceOk) (s : Loc) (c : w32) (m : GoString) :
    status.grpcStatusIs (GF := GF) e s c m ⊢ status.statusAt s c m := by
  unfold status.grpcStatusIs
  iintro ⟨-, %l, -, -, #H⟩
  iexact H

open Iris.ProofMode in
/-- **Two of them on one error agree**: the same status, code and message. -/
theorem status.grpcStatusIs_agree (e : GoInterfaceOk) (s s' : Loc)
    (c c' : w32) (m m' : GoString) :
    status.grpcStatusIs (GF := GF) e s c m ⊢ status.grpcStatusIs e s' c' m' -∗
      ⌜s = s' ∧ c = c' ∧ m = m'⌝ := by
  unfold status.grpcStatusIs
  iintro ⟨-, %l, %hl, #Hl, #Ha⟩ ⟨-, %l', %hl', #Hl', #Ha'⟩
  have hll : l = l' := go.intoVal_inj (hl.symm.trans hl')
  subst hll
  icombine Hl Hl' gives %hs
  subst hs
  ihave %h := status.statusAt_agree _ _ _ _ _ $$ Ha Ha'
  ipureintro; exact ⟨rfl, h⟩

end defs

end EtcdGrove
end Perennial
