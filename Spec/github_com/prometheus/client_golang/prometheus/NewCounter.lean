/-
prometheus's `NewCounter(opts)` (names only; item 8, the read package's initializer): a counter
whose one descriptor is named `BuildFQName(opts.Namespace, opts.Subsystem, opts.Name)`.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `prometheus.NewCounter(opts)` of label-free options with a valid name returns a counter
(mvcc's `counterSpec`: `Inc` and `Add` of a non-negative value return) that describes one
descriptor, of `opts`' fully-qualified name. -/
abbrev prometheus.NewCounter.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.CounterOpts) (ns sub name help : GoString),
  prometheus.counterOpts o ns sub name help →
  prometheus.nameOk (prometheus.fqName ns sub name) →
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.NewCounter)) (Val #o))
  {{ (c : GoInterfaceOk), RET #(GoInterface.ok c);
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c ∗
      ⌜prometheus.collectorName c (prometheus.fqName ns sub name)⌝ }}

end spec

end EtcdGrove
end Perennial
