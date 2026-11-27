/- Lean-first (no Rocq counterpart).

# The interim law `raftStateLastFits.law` (2026-11-27, the restart axiom's review R2, I2)

`StopReadFacts.lean`'s header says what it is for. **Interim: retired when raft's proof states it as a law
of `raftState`** (its facts: every record of a node's durable log past the bootstrap log keeps a time
receipt, `lastRec_receipt`, so its last index is below the receipts' bound past the bootstrap log, which
`readyFits` caps at `2^61`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopReadFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **Interim: a node's durable log ends within its cluster's room** (`raftStateLastFits.law`, see
`StopReadFacts.lean`). Why it is true of raft (v3.7.0 at the pin, as this repository's raft proof models
it): a node's durable state is what its `Ready` batches stored (`RaftState.next`); every entry of it past
the bootstrap log was appended by a leader's `appendEntry`, whose index is its log's last plus one and
whose record keeps a time receipt (`lastRec_receipt`, `Protocol/Refinement.lean`), and a snapshot's index
is a committed entry's; the receipts number at most `receiptBound`, so the last index is below
`receiptBound + bootLen ≤ 2^61` (`readyFits`). [inference from the raft proof's comments, not a proved
lemma; to be reviewed] -/
axiom raftStateLastFits_law_holds : raftStateLastFits.law (GF := GF)

end proof

end EtcdGrove
end Perennial

end
