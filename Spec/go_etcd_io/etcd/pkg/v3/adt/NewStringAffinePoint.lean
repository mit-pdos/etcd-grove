/-
`NewStringAffinePoint` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `NewStringAffinePoint(s)`: the interval `[s, s + "\x00")` of the one key `s`. -/
abbrev adt.NewStringAffinePoint.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewStringAffinePoint)) (Val #s))
  {{ RET #(adt.affIvl s (s ++ go!"\x00")); True }}

end spec

end EtcdGrove
end Perennial
