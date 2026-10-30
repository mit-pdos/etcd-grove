module
public import Proof.go_etcd_io.bbolt.Init
public import Perennial.Proof.sync_proof.rwmutex_guard

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable [AllG GF]

/-- `db.Stats()`: a copy of `*db.stats` read under `statlock` (any invariant `P`: a read lock
gives `P rfrac`, the unlock takes it back), or the zero `Stats` if `db.stats` is nil (`Stats`
checks, so a nil `stats` is no safety violation). Over the fields it reads. -/
abbrev DB.Stats.spec : Prop :=
  ∀ (dbl sp : Loc) (sv : Stats) (dq : DFrac) (q : DFrac) (P : Qp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"stats" dbl ↦{dq} sp ∗
      sync.ownRWMutex (structFieldRef DB go!"statlock" dbl) P ∗ (⌜sp = null⌝ ∨ sp ↦{q} sv) }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Stats")) (Val #()))
  {{ RET #(if sp = null then zero_val Stats else sv);
      structFieldRef DB go!"stats" dbl ↦{dq} sp ∗
      sync.ownRWMutex (structFieldRef DB go!"statlock" dbl) P ∗ (⌜sp = null⌝ ∨ sp ↦{q} sv) }}

end spec

end bbolt
end EtcdGrove
end Perennial
