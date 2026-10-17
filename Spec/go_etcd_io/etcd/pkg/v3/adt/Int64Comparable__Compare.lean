/-
`Int64Comparable.Compare` (`interval_tree.go`), as etcd#22252 changes it (the same body as
etcd#22358's; this spec and its proof are from branch `pr-verify/etcd-22358`). Lean-first (no
Rocq counterpart); see `Proof/go_etcd_io/etcd/pkg/v3/adt/Int64Ivl.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Int64Ivl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `v.Compare(c)` for `c` an `Int64Comparable` `w`: the signed order's three-way comparison,
for every pair of int64s (`int64Cmp_spec`). -/
abbrev adt.Int64Comparable.Compare.spec : Prop :=
  ∀ (v w : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (v @!! Int64Comparable.ty @!! go!"Compare"))
      (Val #(interface.mkOk Int64Comparable.ty #w)))
  {{ RET #(W64 (adt.int64Cmp v w)); True }}

end spec

end EtcdGrove
end Perennial
