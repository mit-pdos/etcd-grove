-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/MaybeAppendIp.lean` (etc/copy-part.py; rerun it, do not edit).
/-
(#33 S4) **`offsetInProgress` after `raftLog.maybeAppend` accepts a batch** (`maybeAppendIp`), which
`raftLog.maybeAppend.spec` and `HandleAppResult` (`handleAppendEntries`) state exactly: the
`RawNode` specs' in-progress boundary after a `MsgApp` (`RawNodeAbsSpecs.lean`, decision 3).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvRaftlog
public import KvNet.Proof.go_etcd_io.raft.v3.Plog

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **`offsetInProgress` after `maybeAppend` accepts the batch `ents`**: kept when the log already
has every entry (`findConflict` is `0`), else `truncateAndAppend`'s at the conflict `ci`
(`logTruncInprogress`: `min(offsetInProgress, ci)` when `ci` is inside the log). -/
def maybeAppendIp [GooseExts] (ls : LogState) (ents : List EntryM) : w64 :=
  if plogFindConflict ls.prev (ls.sents ++ ls.uents) ents = W64 0 then ls.inprogress
  else logTruncInprogress ls (plogFindConflict ls.prev (ls.sents ++ ls.uents) ents)

end EtcdGrove
end Perennial
