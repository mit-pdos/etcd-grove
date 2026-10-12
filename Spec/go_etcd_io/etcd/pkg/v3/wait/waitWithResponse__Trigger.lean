/-
`(*waitWithResponse).Trigger(id, x)` (`wait.go`): does nothing. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.List

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `w.Trigger(id, x)` returns. -/
abbrev wait.waitWithResponse.Trigger.spec : Prop :=
  ∀ (p : Loc) (id : w64) (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait }}
    (App (App (Val (p @!! go.GoType.PointerType wait.waitWithResponse.ty @!! go!"Trigger")) (Val #id))
      (Val #x))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
