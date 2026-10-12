/-
`wait.NewWithResponse(ch)` (`wait.go`, a `Wait` for tests that returns `ch` to every `Register`). Lean-first (no Rocq counterpart).
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

/-- `NewWithResponse(ch)`: a `*waitWithResponse` holding `ch` (read-only). -/
abbrev wait.NewWithResponse.spec : Prop :=
  ∀ (ch : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait }}
    (App (Val (@! wait.NewWithResponse)) (Val #ch))
  {{ (w : GoInterface), RET #w; ∃ p : Loc,
      ⌜w = interface.mkOk (go.GoType.PointerType wait.waitWithResponse.ty) #p⌝ ∗
      structFieldRef wait.waitWithResponse go!"ch" p ↦□ ch }}

end spec

end EtcdGrove
end Perennial
