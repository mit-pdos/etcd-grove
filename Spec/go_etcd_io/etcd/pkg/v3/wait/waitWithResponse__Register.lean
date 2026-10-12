/-
`(*waitWithResponse).Register(id)` (`wait.go`). Lean-first (no Rocq counterpart).
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

/-- `w.Register(id)` returns the channel `w` holds. -/
abbrev wait.waitWithResponse.Register.spec : Prop :=
  ∀ (p ch : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗
      structFieldRef wait.waitWithResponse go!"ch" p ↦□ ch }}
    (App (Val (p @!! go.GoType.PointerType wait.waitWithResponse.ty @!! go!"Register")) (Val #id))
  {{ RET #ch; True }}

end spec

end EtcdGrove
end Perennial
