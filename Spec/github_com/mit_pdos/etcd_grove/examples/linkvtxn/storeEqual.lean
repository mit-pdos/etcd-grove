/- Lean-first (no Rocq counterpart).

`storeEqual(a, b)` (linkvtxn.go): whether the stores `a` and `b` hold the same entries and
revision.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev storeEqual.spec : Prop :=
  ∀ (a b : store) (ga gb : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗ storeOwn a ga ∗ storeOwn b gb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.storeEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (ga = gb)); True }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
