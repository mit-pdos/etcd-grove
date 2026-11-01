/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__request.lean`.
Lean-first (no Rocq counterpart; kvreconf-snapshot-thread, 2026-10-30: `maybeSnapshot`'s proof,
its storage calls moved to the snapshot goroutine's `snapshot`).

Under the lock the applier reads its own halves (`r.index = len ap`, `r.cs = csp`) and encodes its
maps (`encodeState`: `ap`'s state, `kvr_snapOk_of`). With a configuration and an index past
`snapIndex`, the request carries the frozen entry at `len ap` (`frozenTo_at`: `ap`'s last term),
the snapshot certified in the registry (`kvr_snap_make`), the delivered log (`storDL`), the
configuration and the data; with `compact`, the known compaction point, the frozen log and the
node's applied index. A send that cannot complete (a request pending) drops it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__request
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.BagSend
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.encodeState
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.SnapMake
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Replica.request.wp_proof
    (wp_encodeState : encodeState.spec (GF := GF) (hG := hG)) :
    Replica.request.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end kvreconf
end EtcdGrove
end Perennial
