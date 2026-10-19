/- Lean-first (no Rocq counterpart).

`(*KV).run(send)` (kv.go:117): the replica's driver of its node: append each
`Ready`'s entries to the storage, send its messages (`send`, a callback, gets what a
transport needs: each message legitimately sent, of a term within the budget, and its
read credit), note its read states, apply its committed entries (counting them: the
applied index), answer the reads whose index is applied (`answer`), `Advance`.
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
abbrev KV.run.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) (send : GoFunc)
    (op : CCOp) (c0 c1 : CCState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ isReplica γr γp r id n st ∗
      -- (2026-10-15, stage N) the node in the dynamic mode of a cluster whose conf changes are
      -- `op` (`KVCC`), and the driver's view of its configuration, the initial one
      ⌜KVCC γp.node op c0 c1⌝ ∗ nodeCfg γp.node 0 c0 ∗
      nodeDriver γp.node id n [] ∗ runOwn γr r [] ∗
      sendSpec send γp.node }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"run")) (Val #send))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
