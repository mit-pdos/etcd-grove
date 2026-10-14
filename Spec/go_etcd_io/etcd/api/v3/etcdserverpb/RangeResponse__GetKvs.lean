/-
`etcdserverpb.RangeResponse.GetKvs()` (`api/etcdserverpb/rpc.pb.go`, translated for the txn
package's `WarnOfExpensiveReadOnlyTxnRequest`; unit P4, 2026-10-14). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `r.GetKvs()` of a non-nil `*RangeResponse`: its `Kvs` (read-only). -/
abbrev RangeResponse.GetKvs.spec : Prop :=
  ∀ (r : Loc) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜r ≠ null⌝ ∗
      structFieldRef etcdserverpb.RangeResponse go!"Kvs" r ↦□ sl }}
    (App (Val (r @!! go.GoType.PointerType etcdserverpb.RangeResponse.ty @!! go!"GetKvs"))
      (Val #()))
  {{ RET #sl; True }}

end spec

end EtcdGrove
end Perennial
