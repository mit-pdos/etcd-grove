/- Lean-first (no Rocq counterpart).

`(*Register).Put(val)` (register.go:219), logically atomic:
`<<∀ x, regVal γr x>> Put val <<regVal γr val>>`, in Iris's form: the client's atomic update
(at `regMask`: not raft's commit invariant nor the register's). One operation credit.
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
abbrev Register.Put.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (val : List w8) (Φ : IProp GF),
  (val.length : Int) < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ isRegister γr γp r ∗ opCred γp 1 ∗
      AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅ <{ regVal γr val, COMM Φ }> }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"Put")) (Val #val))
  {{ RET #(); Φ }}

end spec

end register
end EtcdGrove
end Perennial
