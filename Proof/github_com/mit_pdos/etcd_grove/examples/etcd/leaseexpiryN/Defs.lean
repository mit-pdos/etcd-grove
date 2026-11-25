/-
**leaseexpiryN's `Main(k)`: its named premises and vocabulary** (`notes/leaseN-plan.md`, 2026-11-16). Lean-first (no
Rocq counterpart). putgetN's (`putgetN/Defs.lean`) for the `k` members of `examples/etcd/leaseexpiryN/leaseexpiryN.go`.

**The members** (`members k`, `etcdstart.Members("leaseexpiryN", k, 12000, 13000)`): member `i` (from `0`) named
`leaseexpiryN-i`, peer address `127.0.0.1:(12000+i)`, client address `127.0.0.1:(13000+i)`; every member's client
address is served (`startOf`).

**The pure facts** (putgetN's `BootFacts`, reused): the member ids `ids` in the members' order (etcd's, from
each peer URL and the cluster token `leaseexpiryN-1973196`; `TestMemberIDs` checks them for every `k ≤ 1000`), the peers
`ps` in `bootstrap`'s order, a permutation of the ids, and the bootstrap log.

**The Iris premises** (`premises`, persistent): putgetN's at this program's token: `bootstrap`'s contract
for every member (`etcdstart.bootPremise`), `proto.Marshal`'s contract at the bootstrap log's conf changes
(`bootMarshal`), the raft wrapper's trust-boundary contracts (`etcdstart.commonPremises`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **The members of `Main(k)`'s cluster** (`Members("leaseexpiryN", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"leaseexpiryN" k (W64 12000) (W64 13000)

/-- **The members `Main(k)` starts** (2026-11-24, P6): `Main` returns at once for a `k` outside
`[1, 1000]` (`if k < 1 || k > 1000 { return }`), starting none; otherwise `members k`. -/
def cluster (k : w64) : List GMember :=
  if 1 ≤ uint.nat k ∧ uint.nat k ≤ 1000 then members (uint.nat k) else []

theorem cluster_cases (k : w64) :
    (1 ≤ uint.nat k ∧ uint.nat k ≤ 1000 ∧ cluster k = members (uint.nat k)) ∨ cluster k = [] := by
  unfold cluster
  split
  · next h => exact Or.inl ⟨h.1, h.2, rfl⟩
  · exact Or.inr rfl

theorem mem_cluster {k : w64} {m : GMember} (h : m ∈ cluster k) :
    m ∈ members (uint.nat k) ∧ uint.nat k ≤ 1000 := by
  rcases cluster_cases k with ⟨-, hk, he⟩ | he
  · rw [he] at h; exact ⟨h, hk⟩
  · rw [he] at h; simp at h

/-- The cluster's token (`Token`). -/
abbrev token : GoString := go!"leaseexpiryN-1973196"

/-- **The program's start bundles** (name, peer address, client address): every member's. -/
def startOf (ms : List GMember) : List (GoString × GoString × Option GoString) :=
  ms.map (fun m => (m.Name', m.Peer', some m.Client'))

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`Main(k)`'s named premises** (persistent; see the file header). -/
def premises (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    ([∗list] m; id ∈ members k; ids,
      etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN (members k) ids) token
        m.Name' (urlsN (members k) m) id))

instance premises_persistent (k N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) k N ids ps ctxs boot) := by
  unfold premises; infer_instance

end defs

end etcd_leaseexpiryN
end EtcdGrove
end Perennial
