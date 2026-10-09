/-
`clientv3.cloneCompare(c)` (`client/v3/compare.go`, translated for `client/v3/concurrency`). Lean-first (no
Rocq counterpart); see `InvCmp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCmp

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cloneCompare(c)` of a comparison holding `m`: a fresh clone (`proto.Clone`), owned. -/
abbrev cloneCompare.spec : Prop :=
  ∀ (p : Loc) (m : CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ compareAt p m ∗ ⌜p ≠ null⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.cloneCompare)) (Val #p))
  {{ (p' : Loc), RET #p'; ⌜p' ≠ null⌝ ∗ compareOwn p' m }}

end spec

end EtcdGrove
end Perennial
