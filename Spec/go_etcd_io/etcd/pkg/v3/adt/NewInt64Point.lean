/-
`NewInt64Point` (`interval_tree.go`), as etcd#22358 changes it. Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/pkg/v3/adt/Int64Ivl.lean`.
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

/-- `NewInt64Point(a)`: the interval `[a, a + 1)`, and the empty `[a, a)` at `MaxInt64`, which
has no successor (`int64PointEnd`); in either case `Begin ≤ End` (`int64PointEnd_spec`). -/
abbrev adt.NewInt64Point.spec : Prop :=
  ∀ (a : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewInt64Point)) (Val #a))
  {{ RET #(adt.int64Ivl a (adt.int64PointEnd a)); True }}

end spec

end EtcdGrove
end Perennial
