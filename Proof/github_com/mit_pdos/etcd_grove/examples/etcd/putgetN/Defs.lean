/-
**putgetN's `Main(k)`: its named premises and vocabulary** (the clusterN Scope,
`notes/clusterN-scope.md`, 2026-11-15). Lean-first (no Rocq counterpart). putget3's
(`putget3/Defs.lean`) for the `k` members of `examples/etcd/putgetN/putgetN.go`.

**The members** (`members k`, `etcdstart.Members("putgetN", k, 24000, 25000)`): member `i` (from `0`)
named `putgetN-i`, peer address `127.0.0.1:(24000+i)`, client address `127.0.0.1:(25000+i)`; only
member `0`'s client address is served (`startOf`: the program's start bundles, member `0`'s with its
client address).

**The pure facts** (`BootFacts`): `bootstrap`'s results as Go computes them: the member ids `ids`
in the members' order (etcd's, from each peer URL and the cluster token `putgetN-1405`;
`TestMemberIDs` checks their 16 low bits distinct and not `0` for every `k ≤ 1000`), the peers `ps`
in `bootstrap`'s order, a permutation of the ids, and the bootstrap log (`BootCore`: the ids' low
bits distinct and not `0`, one conf change per member). putget3's `BootFacts id₁ id₂ id₃` with a list.

**The Iris premises** (`premises`, persistent): putget3's, for every member: `bootstrap`'s contract
(`etcdstart.bootPremise`, putget3's own `bootPremise` with the configuration's token a parameter: the
same configuration fields), at every server raft names of the cluster, for the member's
configuration (`etcdstart.cfgOk`) and URLs (`etcdstart.urlsN`: putget3's `urlsOk` for a list), at the
URL directory `dirN` (each member's one peer URL); `proto.Marshal`'s contract at the bootstrap log's
conf changes (`bootMarshal`); the raft wrapper's trust-boundary contracts (`etcdstart.commonPremises`,
putget3's `commonPremises`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **The members of `Main(k)`'s cluster** (`Members("putgetN", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"putgetN" k (W64 24000) (W64 25000)

/-- The cluster's token (`Token`). -/
abbrev token : GoString := go!"putgetN-1405"

/-- **The program's start bundles** (name, peer address, client address): every member's peer
address, member `0`'s client address. -/
def startOf : List GMember → List (GoString × GoString × Option GoString)
  | [] => []
  | m :: r => (m.Name', m.Peer', some m.Client') :: r.map (fun m => (m.Name', m.Peer', none))

/-- **The peer-URL directory of the cluster** (the members `ms` with the ids `ids`, in order):
each member's one peer URL. -/
def dirN (ms : List GMember) (ids : List w64) (id : w64) : List GoString :=
  match (ms.zip ids).find? (fun p => decide (p.2 = id)) with
  | some p => [go!"http://" ++ p.1.Peer']
  | none => []

/-- **`bootstrap`'s results, as Go computes them** (see the file header). -/
structure BootFacts (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (bl : List LogEntry) : Prop extends BootCore ps ctxs bl where
  /-- the peers are a permutation of the members' ids (putget3's `perm`) -/
  perm : ps.Perm ids

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`Main(k)`'s named premises** (persistent; see the file header), at the bound `N` of each
member's apply thread's write tokens, the member ids (in the members' order), the peers, their
contexts and the bootstrap log. -/
def premises (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    ([∗list] m; id ∈ members k; ids,
      etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) token
        m.Name' (urlsN (members k) m) id))

instance premises_persistent (k N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) k N ids ps ctxs boot) := by
  unfold premises; infer_instance

end defs

end etcd_putgetN
end EtcdGrove
end Perennial
