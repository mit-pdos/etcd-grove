/-
## `(*ServerConfig).WALDir()` (`config.go`)

**Users.** `bootstrap`, `purgeFile`. **Proof sketch.** names only: trusted. **Changes**: from `specs-ref`'s
`ServerConfig__WALDir.lean` where it existed (`config.backendPathOf`); `walDirOf` keyed by both
directories (the WAL API's critique 3). **Margin.** Exact (the path is opaque).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Config

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

/-- **`WALDir()`**: the WAL directory. -/
def ServerConfig.WALDir.spec : Prop :=
  ∀ (c : Loc) (datadir dedicatedwaldir : GoString),
  {{ (typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c) datadir DFrac.discard ∗ typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DedicatedWALDir" c) dedicatedwaldir DFrac.discard : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"WALDir")) (Val #()))
  {{ RET #(Config.walDirOf ⟨datadir, dedicatedwaldir⟩); True }}

end spec

end Config
end EtcdGrove
end Perennial
