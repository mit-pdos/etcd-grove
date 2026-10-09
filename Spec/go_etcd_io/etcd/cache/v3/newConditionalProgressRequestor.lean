/-
`newConditionalProgressRequestor(notifier, clock, requestInterval)`
(`cache/progress_requestor.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newConditionalProgressRequestor(n, clk, ri)`: a progress requestor (`isProgressRequestor`:
no waiters, not stopped, `cond` on its `mux`) whose `run` will use `n`, `clk` and `ri`
(`isPrRun`). -/
abbrev newConditionalProgressRequestor.spec : Prop :=
  ∀ (n clk : GoInterface) (ri : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (App (App (Val (@! newConditionalProgressRequestor)) (Val #n)) (Val #clk)) (Val #ri))
  {{ (p : Loc), RET #p; isProgressRequestor p ∗ isPrRun p n clk ri }}

end spec

end EtcdGrove
end Perennial
