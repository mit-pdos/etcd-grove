/-
**The applied log's lease table** (the lease-grant stage, 2026-11-02; `notes/lease-grant-plan.md`,
"Design of the server chain", 2.0): `appliedTable γr A`, the KV model's lease table of the raft
node's prefix `γr.raft.pre` (`RNNames.pre`) and the applied entries `A`, folded from the empty
table: the live ids the leased rest image (`srvRest`'s leased arm) and the tie's halves (`ltHalf`)
are at. Lean-first (no Rocq counterpart). The KV model's own table folds over `A` alone; the two
agree where the prefix is empty (`kvLeases_pre`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.GrantRest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The lease table of the applied log** `A`, after the raft node's prefix. -/
def appliedTable [GooseExts] (γr : ReadNames) (A : List EntryModel) : LeaseTable :=
  kvLeases γr.kv (γr.raft.pre ++ A)

/-- **An empty prefix grants nothing** (m-a): the table of the prefix alone is empty. -/
theorem kvLeases_pre [GooseExts] (γr : ReadNames) (h : γr.raft.pre = []) :
    (kvLeases γr.kv γr.raft.pre).ids = [] := by
  rw [h]; rfl

end EtcdGrove
end Perennial
