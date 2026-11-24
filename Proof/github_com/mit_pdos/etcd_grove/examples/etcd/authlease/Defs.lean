/-
**authlease's `Main(k)`: its named premises and vocabulary** (auth-lease S4, `notes/auth-lease-s4-draft.md`
§2, 2026-11-18; authN's `Defs.lean` at the token `authlease-1787` and the ports 16000/17000).
Lean-first (no Rocq counterpart). putgetN's (`putgetN/Defs.lean`) at auth3's configuration (the simple
token provider), for the `k` members of `examples/etcd/authlease/authlease.go`.

**The members** (`members k`, `etcdstart.Members("authlease", k, 16000, 17000)`): member `i` (from `0`)
named `authlease-i`, peer address `127.0.0.1:(16000+i)`, client address `127.0.0.1:(17000+i)`; every
member's client address is served (`startOf`).

**The pure facts** (putgetN's `BootFacts`, reused): the member ids `ids` in the members' order (etcd's, from
each peer URL and the cluster token `authlease-1787`; `TestMemberIDs` checks their 16 low bits distinct
and not `0` for every `k ≤ 300`, the bound of `examples/etcd/all`), the peers `ps` in `bootstrap`'s order, a permutation of the ids,
and the bootstrap log.

**The Iris premises** (`premises`, persistent): putgetN's at auth3's configuration: `bootstrap`'s
contract for every member (`etcdstart.bootPremiseOn`: `bootPremise` with `AuthToken = "simple"`, auth3's
`bootPremise` at the token `authlease-1787`), `proto.Marshal`'s contract at the bootstrap log's conf
changes (`bootMarshal`), the raft wrapper's trust-boundary contracts (`etcdstart.commonPremises`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersAuthDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **The members of `Main(k)`'s cluster** (`Members("authlease", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"authlease" k (W64 16000) (W64 17000)

/-- The cluster's token (`Token`). -/
abbrev token : GoString := go!"authlease-1787"

/-- **The program's start bundles** (name, peer address, client address): every member's. -/
def startOf (ms : List GMember) : List (GoString × GoString × Option GoString) :=
  ms.map (fun m => (m.Name', m.Peer', some m.Client'))

/-- **The member a principal uses** (`run`'s): the index `i mod k` of `ms`: `anon` at `0`, `u` and
`bad` at `1`, `v` at `2`. -/
def memberAtMod (ms : List GMember) (i : Nat) : Option GMember := ms[i % ms.length]?

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
      etcdstart.bootPremiseOn N ps (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN (members k) ids) token
        m.Name' (urlsN (members k) m) id))

instance premises_persistent (k N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) k N ids ps ctxs boot) := by
  unfold premises; infer_instance

end defs

end etcd_authlease
end EtcdGrove
end Perennial
