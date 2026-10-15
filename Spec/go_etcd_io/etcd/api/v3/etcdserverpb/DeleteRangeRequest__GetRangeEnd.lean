/-
`etcdserverpb.DeleteRangeRequest.GetRangeEnd()` (`api/etcdserverpb/rpc.pb.go`, translated for the server's request
path). Lean-first (no Rocq counterpart).
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

/-- `p.GetRangeEnd()` on a non-nil `*DeleteRangeRequest` returns its `RangeEnd` field. -/
abbrev DeleteRangeRequest.GetRangeEnd.spec : Prop :=
  ∀ (p : Loc) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" p ↦□ v }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty @!! go!"GetRangeEnd")) (Val #()))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
