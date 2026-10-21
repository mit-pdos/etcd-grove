/- Lean-first (no Rocq counterpart).

`resEqual(x, y)` (linkvtxn.go): a transaction operation's result compared with the model's
(`resEqualL`).
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
abbrev resEqual.spec : Prop :=
  ∀ (x y : TRes),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.resEqual)) (Val #x)) (Val #y))
  {{ RET #(resEqualL x y); True }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
