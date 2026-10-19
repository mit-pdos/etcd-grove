/-
`reuseOrNewWithCallOptions(opt, retryOptions)` (`client/v3/retry_interceptor.go`; unit P3a).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `reuseOrNewWithCallOptions(opt, retryOptions)`: `opt` itself if there is no option, otherwise
a copy the options' closures write (`optApplyOk`): read-only options either way
(`retryOptsAt`). -/
abbrev reuseOrNewWithCallOptions.spec : Prop :=
  ∀ (o : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption)
    -- (2026-10-19, D21 M6) the options' retry bounds (`optApplyMax`): the bound after is the
    -- last `withMax`'s, or `mx`'s
    (ks : List (Option w64)) (mx : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryOptsMax o mx ∗ sl ↦*□ ros ∗ [∗list] ro;k ∈ ros;ks, optApplyMax ro.applyFunc' k }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.reuseOrNewWithCallOptions)) (Val #o)) (Val #sl))
  {{ (o' : Loc), RET #o'; retryOptsMax o' (maxAfter mx ks) }}

end spec

end EtcdGrove
end Perennial
