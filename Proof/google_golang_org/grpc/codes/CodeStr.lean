/-
What grpc's `codes.Code.String()` returns (`code_string.go`), as a pure function of the code:
`codes.codeStr`. The vocabulary of `Spec/google_golang_org/grpc/codes/Code__String.lean` and of
`(*status.Status).String()`'s message (`Proof/google_golang_org/grpc/internal/status/`).
-/
module

public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- `c.String()` (grpc v1.84.0 `codes/code_string.go`): the name of each of the seventeen codes,
`Code(<decimal>)` for any other (`"Code(" + strconv.FormatInt(int64(c), 10) + ")"`). -/
def codes.codeStr (c : w32) : GoString :=
  if c = W32 0 then go!"OK"
  else if c = W32 1 then go!"Canceled"
  else if c = W32 2 then go!"Unknown"
  else if c = W32 3 then go!"InvalidArgument"
  else if c = W32 4 then go!"DeadlineExceeded"
  else if c = W32 5 then go!"NotFound"
  else if c = W32 6 then go!"AlreadyExists"
  else if c = W32 7 then go!"PermissionDenied"
  else if c = W32 8 then go!"ResourceExhausted"
  else if c = W32 9 then go!"FailedPrecondition"
  else if c = W32 10 then go!"Aborted"
  else if c = W32 11 then go!"OutOfRange"
  else if c = W32 12 then go!"Unimplemented"
  else if c = W32 13 then go!"Internal"
  else if c = W32 14 then go!"Unavailable"
  else if c = W32 15 then go!"DataLoss"
  else if c = W32 16 then go!"Unauthenticated"
  else go!"Code(" ++ internal.strconv.fmtInt (W64 (uint.Z c)) (W64 10) ++ go!")"

end EtcdGrove
end Perennial
