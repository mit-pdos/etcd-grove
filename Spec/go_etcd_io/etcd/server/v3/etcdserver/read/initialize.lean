/-
The read package's initializer (`server/v3/etcdserver/read`), as a spec (item 8, 2026-10-17): it
initializes its imports and gives the package's fact (`readInit`). Not proved: its translated
`init()` calls `prometheus.MustRegister` on its two counters, which panics on a name already
registered, and a true spec of it needs a model of prometheus' default registry (the names
registered so far) that the package initializers share; nor are `context`'s facts `readInit`
states (`Canceled`, `DeadlineExceeded`) in Perennial's `context` fact. The packages importing it
(`etcdserver`, `v3rpc`) take it as a hypothesis (`etc/gen-init.py`, `ASSUMED`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `read`'s `initialize'`: from `ownInitializing`, it gives the package's `isPkgInit`. -/
abbrev go_etcd_io.etcd.server.v3.etcdserver.read.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val go_etcd_io.etcd.server.v3.etcdserver.read.initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }}

end spec

end Perennial
