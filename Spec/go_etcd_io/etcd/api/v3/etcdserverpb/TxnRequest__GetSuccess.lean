/-
`etcdserverpb.TxnRequest.GetSuccess()` (`api/etcdserverpb/rpc.pb.go`, translated for the server's request
path: the read side's trace attributes, unit 3b). Lean-first (no Rocq counterpart).
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

/-- `p.GetSuccess()` on a non-nil `*TxnRequest` returns its `Success` field. -/
abbrev TxnRequest.GetSuccess.spec : Prop :=
  ∀ (p : Loc) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.TxnRequest go!"Success" p ↦□ v }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.TxnRequest.ty @!! go!"GetSuccess")) (Val #()))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
