/-
**The pure vocabulary of `createHeaderFields`' callees** (phase 7 S2 core, 2026-11-23,
`notes/phase7-plan.md` §0a): what the grpc model's `isReservedHeader`, grpc's `grpcutil.ContentType`,
`internal/metadata.ValidatePair` and `internal/status.IsRestrictedControlPlaneCode` compute, as pure
functions of their arguments. Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire

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

/-- **`ValidatePair(k, vs...)` returns `nil`**: the key is `keyOk`, and it ends in `-bin` or every
value's bytes are printable. -/
def pairOk (k : GoString) (vs : List GoString) : Prop :=
  keyOk k ∧ (go!"-bin" <:+ k ∨ ∀ v ∈ vs, ∀ b ∈ v, printable b)

/-- The codes gRFC A54 restricts to the control plane (`IsRestrictedControlPlaneCode`):
`InvalidArgument`, `NotFound`, `AlreadyExists`, `FailedPrecondition`, `Aborted`, `OutOfRange`,
`DataLoss`. -/
def restrictedCodes : List w32 := [W32 3, W32 5, W32 6, W32 9, W32 10, W32 11, W32 15]

end grpcHdr
end EtcdGrove
end Perennial
