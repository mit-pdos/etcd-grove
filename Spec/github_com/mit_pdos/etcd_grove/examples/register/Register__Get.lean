/- Lean-first (no Rocq counterpart).

`(*Register).Get()` (register.go:164), logically atomic:
`<<∀ x, regVal γr x>> Get <<regVal γr x, RET x>>`. One operation credit.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Register.Get.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (Φ : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ isRegister γr γp r ∗ opCred γp 1 ∗
      AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅ <{ regVal γr x, COMM Φ x }> }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"Get")) (Val #()))
  {{ (x : List w8), RET #x; Φ x }}

end spec

end register
end EtcdGrove
end Perennial
