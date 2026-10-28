/- Lean-first (no Rocq counterpart).

`(*KV).run(send)` (kv.go): the replica's driver of its node: (D22 S-r, 2026-10-21) install a
`Ready`'s snapshot (its data, decoded, replaces the store's state, `install`, which answers this
replica's waiters among the operations it covers (2026-10-22); `ApplySnapshot`), append each
`Ready`'s entries to the storage, send its messages (`send`, a callback, gets what a
transport needs: each message sent, `sentMsg`, with its credits), note its read states, apply its committed entries (counting them: the
applied index), answer the reads whose index is applied (`answer`), `Advance`; (D22 S-r) every `snapEvery`
applied entries take a snapshot (`encodeState`, `CreateSnapshot`) and compact (`Compact`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.run.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) (send : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isReplica γr γp r id n st ∗
      -- the node's driver token, idle at its start, on the store's storage
      nodeDriver n γr.cluster kvRaftN (NodeDriverState.init (kvStorIface st)) ∗
      runOwn γr r [] ∗
      -- the storage's snapshot token, at a fresh storage (`runStor`)
      runStor γr st memStorEmpty ∗
      sendSpec send γr.cluster }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"run")) (Val #send))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
