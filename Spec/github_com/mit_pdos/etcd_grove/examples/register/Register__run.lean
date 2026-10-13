/- Lean-first (no Rocq counterpart).

`(*Register).run(send)` (register.go:117): the replica's driver of its node: append each
`Ready`'s entries to the storage, send its messages (`send`, a callback, gets what a
transport needs: each message legitimately sent, of a term within the budget, and its
read credit), note its read states, apply its committed entries (counting them: the
applied index), answer the reads whose index is applied (`answer`), `Advance`.
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
abbrev Register.run.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) (send : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ isReplica γr γp r id n st ∗ nodeDriver γp.node id n [] ∗ runOwn γr r [] ∗
      sendSpec send γp.node }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"run")) (Val #send))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
