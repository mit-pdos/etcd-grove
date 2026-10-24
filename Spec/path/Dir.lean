/-
`path.Dir`: the trust boundary (`path` is names-only; the pure model `apply.pathDir` is in
`apply/RestModel.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `path.Dir(p)` returns `apply.pathDir p`. -/
abbrev path.Dir.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.path }}
    (App (Val (@! _root_.Perennial.path.Dir)) (Val #p))
  {{ RET #(apply.pathDir p); True }}

end spec

end EtcdGrove
end Perennial
