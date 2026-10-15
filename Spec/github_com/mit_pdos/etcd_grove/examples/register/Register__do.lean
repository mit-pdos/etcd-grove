/- Lean-first (no Rocq counterpart).

`(*Register).do(kind, val)` (register.go:206): one operation, logically atomic: the
client's atomic update over the register's value takes effect when the operation's first
entry is committed (`reg_propAu`); `do` returns the value after it. One operation credit.
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
abbrev Register.do.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (kind : w8) (val : List w8)
    (Φ : List w8 → IProp GF),
  (val.length : Int) < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ isRegister γr γp r ∗ opCred γp 1 ∗
      AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅
        <{ regVal γr (opNext kind val x), COMM Φ (opNext kind val x) }> }}
    (App (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"do")) (Val #kind)) (Val #val))
  {{ (res : List w8), RET #res; Φ res }}

end spec

end register
end EtcdGrove
end Perennial
