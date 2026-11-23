/-
**The pure vocabulary of `createHeaderFields`' callees** (phase 7 S2 core, 2026-11-23,
`notes/phase7-plan.md` §0a): what the grpc model's `isReservedHeader`, grpc's `grpcutil.ContentType`,
`internal/metadata.ValidatePair` and `internal/status.IsRestrictedControlPlaneCode` compute, as pure
functions of their arguments. Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace grpcHdr

/-- The keys `isReservedHeader` lists (`model_http_util.go`, grpc-go's `http_util.go`). -/
def reservedHdrs : List GoString :=
  [go!"content-type", go!"user-agent", go!"grpc-message-type", go!"grpc-encoding",
    go!"grpc-message", go!"grpc-status", go!"grpc-timeout", go!"te"]

/-- **`isReservedHeader(h)`**: a pseudo-header (first byte `:`) or one of `reservedHdrs`. -/
def reservedHdr (h : GoString) : Prop := h.head? = some (W8 58) ∨ h ∈ reservedHdrs

instance (h : GoString) : Decidable (reservedHdr h) := by unfold reservedHdr; infer_instance

/-- **`grpcutil.ContentType(sub)`**: `application/grpc`, with `+sub` for a non-empty subtype. -/
def contentTypeOf (sub : GoString) : GoString :=
  if sub = [] then go!"application/grpc" else go!"application/grpc" ++ go!"+" ++ sub

/-- A key byte `ValidateKey` accepts: `[0-9a-z_.-]`. -/
def keyByteOk (b : w8) : Prop :=
  (W8 97 ≤ b ∧ b ≤ W8 122) ∨ (W8 48 ≤ b ∧ b ≤ W8 57) ∨ b = W8 46 ∨ b = W8 45 ∨ b = W8 95

instance (b : w8) : Decidable (keyByteOk b) := by unfold keyByteOk; infer_instance

/-- **`ValidateKey(k)` returns `nil`**: a non-empty key that is a pseudo-header (first byte `:`, not
checked further) or whose bytes are all `keyByteOk`. -/
def keyOk (k : GoString) : Prop :=
  k ≠ [] ∧ (k.head? = some (W8 58) ∨ ∀ b ∈ k, keyByteOk b)

/-- A printable ASCII byte (`hasNotPrintable`'s complement): `0x20`-`0x7E`. -/
def printable (b : w8) : Prop := W8 32 ≤ b ∧ b ≤ W8 126

instance (b : w8) : Decidable (printable b) := by unfold printable; infer_instance

/-- `keyByteOk` on the byte's value. -/
theorem keyByteOk_iff (b : w8) : keyByteOk b ↔
    (97 ≤ uint.Z b ∧ uint.Z b ≤ 122) ∨ (48 ≤ uint.Z b ∧ uint.Z b ≤ 57) ∨ uint.Z b = 46 ∨
      uint.Z b = 45 ∨ uint.Z b = 95 := by
  unfold keyByteOk
  simp only [BitVec.le_def]
  constructor <;> intro h <;> word

/-- `printable` on the byte's value. -/
theorem printable_iff (b : w8) : printable b ↔ 32 ≤ uint.Z b ∧ uint.Z b ≤ 126 := by
  unfold printable
  simp only [BitVec.le_def]
  constructor <;> intro h <;> word

/-- **`ValidatePair(k, vs...)` returns `nil`**: the key is `keyOk`, and it ends in `-bin` or every
value's bytes are printable. -/
def pairOk (k : GoString) (vs : List GoString) : Prop :=
  keyOk k ∧ (go!"-bin" <:+ k ∨ ∀ v ∈ vs, ∀ b ∈ v, printable b)

/-- The codes gRFC A54 restricts to the control plane (`IsRestrictedControlPlaneCode`):
`InvalidArgument`, `NotFound`, `AlreadyExists`, `FailedPrecondition`, `Aborted`, `OutOfRange`,
`DataLoss`. -/
def restrictedCodes : List w32 := [W32 3, W32 5, W32 6, W32 9, W32 10, W32 11, W32 15]

/-- **The model's `encodeMetadataHeader(k, v)`**: a `-bin` key's value base64-encoded without
padding (`b64Raw`), any other value as it is. -/
def encMdHdr (k v : GoString) : GoString := if go!"-bin" <:+ k then b64Raw v else v

/-- **`grpcutil.div(d, r)`**: `d / r` rounded up when the remainder is positive (Go's truncating
`/` and `%` on `int64`, `BitVec.sdiv`/`srem`). -/
def durDiv (d r : w64) : w64 :=
  if 0 < sint.Z (BitVec.srem d r) then BitVec.sdiv d r + W64 1 else BitVec.sdiv d r

/-- The `grpc-timeout` value in one unit: `strconv.FormatInt(div(t, r), 10)` and the unit's letter. -/
def encDurUnit (t r : w64) (u : GoString) : GoString :=
  _root_.Perennial.internal.strconv.fmtInt (durDiv t r) (W64 10) ++ u

/-- `grpcutil.EncodeDuration`'s bound on the number (`maxTimeoutValue`, eight digits). -/
def maxTimeoutValue : Int := 99999999

/-- **`grpcutil.EncodeDuration(t)`**: `0n` for a non-positive duration, else the duration in the
finest unit (`n`, `u`, `m`, `S`, `M`, then `H`) whose rounded-up count is at most
`maxTimeoutValue` (hours unconditionally). -/
def encodeDurationOf (t : w64) : GoString :=
  if sint.Z t ≤ 0 then go!"0n"
  else if sint.Z (durDiv t (W64 1)) ≤ maxTimeoutValue then encDurUnit t (W64 1) go!"n"
  else if sint.Z (durDiv t (W64 1000)) ≤ maxTimeoutValue then encDurUnit t (W64 1000) go!"u"
  else if sint.Z (durDiv t (W64 1000000)) ≤ maxTimeoutValue then
    encDurUnit t (W64 1000000) go!"m"
  else if sint.Z (durDiv t (W64 1000000000)) ≤ maxTimeoutValue then
    encDurUnit t (W64 1000000000) go!"S"
  else if sint.Z (durDiv t (W64 60000000000)) ≤ maxTimeoutValue then
    encDurUnit t (W64 60000000000) go!"M"
  else encDurUnit t (W64 3600000000000) go!"H"

end grpcHdr
end EtcdGrove
end Perennial
