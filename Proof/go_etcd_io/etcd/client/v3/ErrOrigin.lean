/-
Ghost marks on the errors of `clientv3.newClient`'s callees whose errors are otherwise arbitrary
(pr-verify etcd#21714): `loggerErr e` on an error zap's `Config.Build` or
`logutil.CreateDefaultZapLogger` returns, `versionErr e` on one `Client.checkVersion` returns. They
have no meaning in Go and no definition the proofs can unfold (`opaque`), so only those callees'
contracts (axioms) give them: `newClient`'s spec can then say an error came from the logger's
construction or the version check, rather than "any error" whenever those paths are possible (a
reviewer's point: without them, a client with no `Config.Logger` could return any error and meet
the spec). Lean-first (no Rocq counterpart); on the verification branch `pr-verify/etcd-21714` only.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The error `e` came from building a zap logger (`Config.Build`, `CreateDefaultZapLogger`). -/
opaque loggerErr [FfiSyntax] : GoInterfaceOk → Prop

/-- The error `e` came from `Client.checkVersion`. -/
opaque versionErr [FfiSyntax] : GoInterfaceOk → Prop

end EtcdGrove
end Perennial
