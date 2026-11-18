/-
An error's gRPC description, `errDesc` (D29), declared on its own: a module with no import beyond
GooseLang's values, so that a spec of any package may state an error's description without
importing gRPC's or the cache's facts. `fmt.ErrorfWrap`'s post states its error's (N1b, k8s etcd3
7c-2 part 2, 2026-11-06; `notes/decisions.md`, "`errDesc` in a module of its own"). Until then it
was declared in `Proof/go_etcd_io/etcd/cache/v3/Base.lean`, under the same name.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

noncomputable section

namespace Perennial

namespace go_etcd_io.etcd.cache.v3

/-- **An error's description** (opaque; D29, 2026-10-21): what `rpctypes.ErrorDesc(err)` returns,
the status message (`status.FromError(err).Message()`), which for an error that is not a status
error is its `Error()` (`Spec/google_golang_org/grpc/status/FromError.lean`). grpc's `FromError`
reads the status embedded in the error value, so the description is a function of the error, as
its code is (`statusCode`); nothing more is said of it. -/
opaque errDesc [GooseExts] : GoInterface → GoString

end go_etcd_io.etcd.cache.v3

end Perennial
