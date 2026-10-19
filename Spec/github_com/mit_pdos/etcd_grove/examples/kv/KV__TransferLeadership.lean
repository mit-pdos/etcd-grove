/- Lean-first (no Rocq counterpart).

`(*KV).TransferLeadership(to)` (kv.go), 2026-10-13: the replica's node is asked
to hand the leadership over to `to` (`Node.TransferLeadership`). Nothing is promised of the
outcome: the store's operations are specified whoever leads.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.TransferLeadership.spec : Prop :=
  ∀ (γr : KVNames) (γp : RepNames) (r : Loc) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isKV γr γp r }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"TransferLeadership")) (Val #to))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
