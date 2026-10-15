/-
`(*list).Register(id)` (`wait.go`). Lean-first (no Rocq counterpart); see `wait/List.lean`.
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

/-- `l.Register(id)`, with the id's slot (so the `dup id` panic does not happen) and an
expectation `Ψ` the registration condition allows: a channel to receive one value satisfying `Ψ`
from (`waitRecv`), and the record of the registration. -/
abbrev wait.list.Register.spec : Prop :=
  ∀ (l : Loc) (γi : IdNames) (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (id : w64) (Ψ : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ waitList l γi γw R ∗
      idSlot γi id ∗ □ R id Ψ }}
    (App (Val (l @!! go.GoType.PointerType wait.list'.ty @!! go!"Register")) (Val #id))
  {{ (ch : Loc), RET #ch; ∃ γh, waitRecv γh ch Ψ ∗ waitRegd γw id γh.takenName }}

end spec

end EtcdGrove
end Perennial
