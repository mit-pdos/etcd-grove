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

theorem replayJoin_snoc (pre : List replayTermRun) (a b : replayTermRun) :
    replayJoin (pre ++ [a]) b =
      if a.term' = b.term' then pre ++ [{ b with first' := a.first' }] else (pre ++ [a]) ++ [b] := by
  simp [replayJoin, List.getLast?_append]

def replayAddEntry (runs : List replayTermRun) (e : EntryModel) : List replayTermRun :=
  replayJoin runs ⟨e.index, e.index, e.term⟩

/-- Runs are nonempty, ordered ranges which do not overlap. -/
def replayLayout (rs : List replayTermRun) : Prop :=
  (∀ r ∈ rs, uint.nat r.first' ≤ uint.nat r.last') ∧
    rs.Pairwise (fun a b => uint.nat a.last' < uint.nat b.first')

def replayContains (r : replayTermRun) (ci term : w64) : Prop :=
  uint.nat r.first' ≤ uint.nat ci ∧ uint.nat ci ≤ uint.nat r.last' ∧ r.term' = term

def replayHasTerm (rs : List replayTermRun) (ci term : w64) : Prop :=
  ∃ r ∈ rs, replayContains r ci term

/-- While replay is behind the initial backend, its exact entry term is in a readable run. -/
def replayPending (rs : List replayTermRun) (A : List EntryModel) (n : Nat) : Prop :=
  replayLayout rs ∧ ∀ ci : w64, n < A.length → uint.Z ci = A.length →
    replayHasTerm rs ci ((A.getLast?.map EntryModel.term).getD (W64 0))

theorem replayPending_mono {rs : List replayTermRun} {A : List EntryModel} {n m : Nat}
    (hp : replayPending rs A n) (hm : n ≤ m) : replayPending rs A m :=
  ⟨hp.1, fun ci hn => hp.2 ci (Nat.lt_of_le_of_lt hm hn)⟩

end EtcdGrove
end Perennial
