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
public import GeneratedProof.google_golang_org.protobuf.types.known.anypb
public import Proof.google_golang_org.protobuf.proto.UfWire

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

/-- The schema of `google.protobuf.Any` (`TypeUrl` 1 and `Value` 2, both `LEN`), for its unknown
fields (`ufWire`). -/
abbrev status.anySchema : FieldSchema := [(1, [2]), (2, [2])]

/-- The schema of `google.rpc.Status` (`Code` 1 `VARINT`, `Message` 2 `LEN`, `Details` 3 `LEN`). -/
abbrev status.spbStatusSchema : FieldSchema := [(1, [0]), (2, [2]), (3, [2])]

/-- **An element of a `*spb.Status`'s `Details`, read-only** (prove-statuserror, 2026-11-26): `nil`, or
an `*anypb.Any` whose fields `proto.Equal` reads (`TypeUrl`, `Value` and its bytes, `unknownFields`
and its bytes) hold their values for good. Not `sizeCache` (`proto.Marshal` writes it, and nothing
here reads it) nor `state` (protobuf's `MessageState`, read and written only atomically, by the lazy
`messageInfo` initialization). Its unknown fields are what protobuf-go's decoder leaves (`ufWire`): whole,
well-formed fields, on which `proto.Equal`'s `equalUnknown` (`internal/impl/equal.go:196-230`, a
`protowire.ConsumeField` loop) cannot fail; other bytes, of equal length and different content, make it
panic (`slice bounds out of range [:-1]`: `notes/axiom-review/proto-equal-status.md`), and only
protobuf reflection's `SetUnknown` (whose documentation requires valid bytes) can store them. -/
def status.pbAnyRO (a : Loc) : IProp GF :=
  iprop(⌜a = null⌝ ∨ ∃ (tu : GoString) (v u : GoSlice) (vb ub : List w8),
    a.[google_golang_org.protobuf.types.known.anypb.Any, go!"TypeUrl"] ↦□ tu ∗
    a.[google_golang_org.protobuf.types.known.anypb.Any, go!"Value"] ↦□ v ∗ v ↦*□ vb ∗
    a.[google_golang_org.protobuf.types.known.anypb.Any, go!"unknownFields"] ↦□ u ∗ u ↦*□ ub ∗
    ⌜ufWire status.anySchema ub⌝)

instance status.pbAnyRO_persistent (a : Loc) : Iris.BI.Persistent (status.pbAnyRO (GF := GF) a) := by
  unfold status.pbAnyRO; infer_instance

/-- **The fields of a `*spb.Status` beyond `Code` and `Message` that `proto.Equal` reads, read-only**
(prove-statuserror, 2026-11-26, approved by coordinator-E on #37 7183375670): `unknownFields` and its
bytes, `Details`, its elements and each element's (`status.pbAnyRO`); the unknown fields, here and in
each element, what protobuf-go's decoder leaves (`ufWire`, so that `proto.Equal` cannot panic on them). Not `sizeCache` (`proto.Marshal`
writes it: `RawStatusProto`'s callers marshal the status) nor `state` (only atomic accesses). -/
def status.pbStatusRestRO (p : Loc) : IProp GF :=
  iprop(∃ (u d : GoSlice) (ub : List w8) (ds : List Loc),
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"unknownFields"] ↦□ u ∗
    u ↦*□ ub ∗ ⌜ufWire status.spbStatusSchema ub⌝ ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Details"] ↦□ d ∗ d ↦*□ ds ∗
    [∗list] a ∈ ds, status.pbAnyRO a)

instance status.pbStatusRestRO_persistent (p : Loc) :
    Iris.BI.Persistent (status.pbStatusRestRO (GF := GF) p) := by
  unfold status.pbStatusRestRO; infer_instance

/-- **`p` is a non-nil `*spb.Status` (genproto's `google.rpc.Status`) of code `c` and message `m`,
read-only**: its fields `Code` and `Message` hold `c` and `m` for good, and so do the others
`proto.Equal` reads (`status.pbStatusRestRO`). What `proto.Equal`'s spec reads
(`Spec/google_golang_org/protobuf/proto/EqualStatus.lean`). -/
def status.pbStatusRO (p : Loc) (c : w32) (m : GoString) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Code"] ↦□ c ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Message"] ↦□ m ∗
    status.pbStatusRestRO p)

instance status.pbStatusRO_persistent (p : Loc) (c : w32) (m : GoString) :
    Iris.BI.Persistent (status.pbStatusRO (GF := GF) p c m) := by
  unfold status.pbStatusRO; infer_instance

/-- **`s` is a gRPC `*Status` of code `c` and message `m`, never written after** (status-bodies,
2026-11-25: a definition, over the translated `internal/status.Status` and genproto's `Status`; until
then an opaque, TRUSTED, of no law): `s`'s field `s` (`internal/status/status.go`, `type Status struct
{ s *spb.Status }`) holds a non-nil `p` for good, and `p`'s fields `Code` and `Message` hold `c` and
`m` for good, so that `Code()` and `Message()` return `c` and `m` on every call; and so do the other
fields of `p` that `proto.Equal` reads (`status.pbStatusRO`, `status.pbStatusRestRO`: `unknownFields`,
`Details` and its `Any`s; prove-statuserror, 2026-11-26, approved by coordinator-E on #37 7183375670,
so that `(*Error).Is`'s `proto.Equal` of two statuses has the read permission it needs, with the
unknown fields well-formed, as the decoder leaves them (`ufWire`); not
`sizeCache`, which `proto.Marshal` writes, nor `state`, touched only atomically). Persistent points-to:
a producer that builds `s` (`status.New`/`Error`, grpc's other constructors) and never writes those
fields after gives them up. True of grpc (v1.84.0, the model `models/grpc`): `internal/status` writes
`Status.s` only in its constructors (`New`, `FromProto` and `NewWithProto` store a fresh or cloned
`*spb.Status`; `Proto()` returns a clone; `WithDetails` builds a new `Status`), `internal/status` is
not importable outside grpc, and the one function that hands out the raw `*spb.Status`,
`RawStatusProto`, has two callers in the model, `model_transport.go:1087` and `:1325`, which only
read `GetDetails()` and pass it to `proto.Marshal`, which writes its `sizeCache` (another field), not
`Code`, `Message`, `Details`, the `Any`s' fields read here or `unknownFields` (#24 7175520513, the
condition of the approval; `notes/axiom-review/proto-equal-status.md` for the extension). A status
may be shared (package-level `status.Error` values: grpc's `ErrClientConnClosing`,
`errContextCanceled`/`errContextDeadline`, etcd's `ErrGRPC*`). Two of them at one `s` agree
(`statusAt_agree`). Until 2026-11-20 the opaque pure `grpcStatusROP : Loc → w32 → Prop` with the
error's code the pure `statusCode : GoInterface → w32`. SpecPlan's `statusAt`. -/
def status.statusAtRaw (s : Loc) (c : w32) (m : GoString) : IProp GF :=
  iprop(∃ p : Loc, s.[google_golang_org.grpc.internal.status.Status, go!"s"] ↦□ p ∗
    ⌜p ≠ null⌝ ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Code"] ↦□ c ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Message"] ↦□ m ∗
    ∃ (u d : GoSlice) (ub : List w8) (ds : List Loc),
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"unknownFields"] ↦□ u ∗
    u ↦*□ ub ∗ ⌜ufWire status.spbStatusSchema ub⌝ ∗
    p.[google_golang_org.genproto.googleapis.rpc.status.Status, go!"Details"] ↦□ d ∗ d ↦*□ ds ∗
    [∗list] a ∈ ds, (⌜a = null⌝ ∨ ∃ (tu : GoString) (v u : GoSlice) (vb ub : List w8),
      a.[google_golang_org.protobuf.types.known.anypb.Any, go!"TypeUrl"] ↦□ tu ∗
      a.[google_golang_org.protobuf.types.known.anypb.Any, go!"Value"] ↦□ v ∗ v ↦*□ vb ∗
      a.[google_golang_org.protobuf.types.known.anypb.Any, go!"unknownFields"] ↦□ u ∗ u ↦*□ ub ∗
      ⌜ufWire status.anySchema ub⌝))

/-- `statusAtRaw` is `s`'s field `s` holding a `pbStatusRO` (its body spelled out, `pbStatusRO`,
`pbStatusRestRO` and `pbAnyRO` inline, so that the trust-base walks of the posts that give it,
`etc/axiom-tok-check.py`, stay within their depth). -/
theorem status.statusAtRaw_eq (s : Loc) (c : w32) (m : GoString) :
    status.statusAtRaw (GF := GF) s c m =
      iprop(∃ p : Loc, s.[google_golang_org.grpc.internal.status.Status, go!"s"] ↦□ p ∗
        status.pbStatusRO p c m) := rfl

instance status.statusAtRaw_persistent (s : Loc) (c : w32) (m : GoString) :
    Iris.BI.Persistent (status.statusAtRaw (GF := GF) s c m) := by
  rw [status.statusAtRaw_eq]; infer_instance


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
  iintro ⟨-, #⟨%p, #Hs, -, #Hc, #Hm, -⟩⟩ ⟨-, #⟨%p', #Hs', -, #Hc', #Hm', -⟩⟩
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
