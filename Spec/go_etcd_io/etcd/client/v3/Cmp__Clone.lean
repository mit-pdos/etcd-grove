/-
`clientv3.Cmp.Clone()` (`client/v3/compare.go`, translated for `client/v3/concurrency`). Lean-first (no
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

/-- `cmp.Clone()` (through a pointer) of a comparison modelled by `m`: a `Cmp` with a fresh clone,
owned. -/
abbrev Cmp.Clone.spec : Prop :=
  ∀ (cmpp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpp ↦{dq} c ∗ cmpAt c m }}
    (App (Val (cmpp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"Clone")) (Val #()))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpp ↦{dq} c ∗ ⌜c'.c' ≠ null⌝ ∗ compareOwn c'.c' m }}

end spec

end EtcdGrove
end Perennial
