/-
`NewBytesAffineInterval` (`interval_tree.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/pkg/v3/adt/BytesIvl.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.BytesIvl

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

/-- `NewBytesAffineInterval(b, e)`: the interval of the two slices (aliased, not read). -/
abbrev adt.NewBytesAffineInterval.spec : Prop :=
  ∀ (b e : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewBytesAffineInterval)) (Val #b)) (Val #e))
  {{ RET #(adt.bytesIvl b e); True }}

end spec

end EtcdGrove
end Perennial
