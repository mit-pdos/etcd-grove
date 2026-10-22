/-
`NewClient(addr, lg)` (`examples/common/common.go`; 2026-10-22, D33): a client of the one endpoint
`addr`, with etcd's default client configuration -- `clientv3.New(Config{Endpoints: {addr}, Logger:
lg})`, what the examples' `Main`s called. Lean-first (no Rocq counterpart).

**The triple:** `clientv3.New.spec` at that configuration (its `clientCfgOk` from the literal: a
plain endpoint, a logger): a new client of `[addr]` at the watch environment `V`, the caller's
choice, or an error and `nil`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Base
public import Spec.go_etcd_io.etcd.client.v3.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev NewClient.spec : Prop :=
  ∀ (addr : GoString) (lg : Loc) (V : client.WEnv GF),
  lg ≠ null → plainEndpoint addr → threadBound GF ≤ 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.NewClient))
      (Val #addr)) (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl [addr] V) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end common
end EtcdGrove
end Perennial
