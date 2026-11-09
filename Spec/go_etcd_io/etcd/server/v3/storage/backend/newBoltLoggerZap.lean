/-
## `newBoltLoggerZap(bcfg)` (`backend.go:1107-1110`): trusted (names only)

**Users.** `newBackend`. **Why it is true.** `bcfg.Logger.Named("bbolt")`,
`WithOptions(AddCallerSkip(1)).Sugar()` (zap: a logger), wrapped in a fresh `*zapBoltLogger`: a
pointer-typed `bolt.Logger` (4c's `loggerPtrOk`; its methods' contract is 4c's logger contract,
requested in `req/go_etcd_io_bbolt.md`). **Changes.** From `specs-ref`'s: the logger's shape only.
**Margin.** The logger's methods are 4c's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`newBoltLoggerZap(bcfg)`**: a pointer-typed `bolt.Logger`. -/
def newBoltLoggerZap.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ Zap.isLogger cfg.Logger' }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.newBoltLoggerZap)) (Val #cfg))
  {{ (r : GoInterface), RET #r; ∃ l : Loc,
      ⌜r = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.zapBoltLogger.ty) #l⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
