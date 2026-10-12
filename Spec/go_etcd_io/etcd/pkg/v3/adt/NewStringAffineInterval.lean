/-
`NewStringAffineInterval` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

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

/-- `NewStringAffineInterval(b, e)`: the affine interval `[b, e)`. -/
abbrev adt.NewStringAffineInterval.spec : Prop :=
  ∀ (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewStringAffineInterval)) (Val #b)) (Val #e))
  {{ RET #(adt.affIvl b e); True }}

end spec

end EtcdGrove
end Perennial
