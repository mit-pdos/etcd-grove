/- Immutable runs of entry terms, shared by startup and the Ready loop. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open go_etcd_io.etcd.server.v3.etcdserver
variable [GooseExts]

/-- The update to the output of the outer loop. An equal term extends the
last run while retaining the first index at which that term occurred. -/
def replayJoin (runs : List replayTermRun) (r : replayTermRun) : List replayTermRun :=
  match runs.getLast? with
  | some old =>
    if old.term' = r.term' then runs.dropLast ++ [{ r with first' := old.first' }]
    else runs ++ [r]
  | none => [r]

def replayAddEntry (runs : List replayTermRun) (e : EntryModel) : List replayTermRun :=
  replayJoin runs ⟨e.index, e.index, e.term⟩

end EtcdGrove
end Perennial
