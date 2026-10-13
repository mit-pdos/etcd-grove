/-
`(*list).IsRegistered(id)` (`wait.go`). Lean-first (no Rocq counterpart); see `wait/List.lean`.
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

/-- `l.IsRegistered(id)`, with the reader's slots (read-locking the id's shard): a boolean; to a
caller that knows `id` was registered (`ot = some t`, `waitRegd`), `false` means the registration
is gone (`waitGone`). -/
abbrev wait.list.IsRegistered.spec : Prop :=
  ∀ (l : Loc) (γi : IdNames) (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (id : w64) (ot : Option GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ waitListReader l γi γw R ∗
      waitRegdOpt γw id ot }}
    (App (Val (l @!! go.GoType.PointerType wait.list'.ty @!! go!"IsRegistered")) (Val #id))
  {{ (b : Bool), RET #b; waitListReader l γi γw R ∗ (⌜b = true⌝ ∨ waitGoneOpt γw id ot) }}

end spec

end EtcdGrove
end Perennial
