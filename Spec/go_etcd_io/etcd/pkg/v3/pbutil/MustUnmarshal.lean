/-
`pbutil.MustUnmarshal(um, data)` (`pbutil.go:40`): calls `um.Unmarshal(data)` and panics if
`err != nil`. Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.pbutil
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

/-- `pbutil.MustUnmarshal(um, data)` calls `um.Unmarshal(data)` and returns `#()` when that call
returns `nil` error. -/
abbrev pbutil.MustUnmarshal.spec : Prop :=
  ∀ (ty : go.GoType) (r_ptr : Loc) (data : GoSlice) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
      P ∗
      (P -∗ WP (App (Val (r_ptr @!! ty @!! go!"Unmarshal")) (Val #data))
        {{ err, ⌜err = #(GoInterface.nil)⌝ ∗ Q }}) }}
    (App (App (Val #(functions pbutil.MustUnmarshal [])) (Val #(interface.mkOk ty #r_ptr))) (Val #data))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
