/-
**restartN's `Run(k)` and its functions: their named premises and vocabulary** (`notes/restartN-plan.md`,
2026-11-15). Lean-first (no Rocq counterpart). restart3's (`restart/Defs.lean`) for the `k` members of
`examples/etcd/restartN/restartN.go`, with putgetN's members (`etcd_putgetN.dirN`, `BootFacts`).

**The members** (`members k`, `etcdstart.Members("restartN", k, 14000, 15000)`): member `i` (from `0`)
named `restartN-i`, peer address `127.0.0.1:(14000+i)`, client address `127.0.0.1:(15000+i)` (not
served).

**The pure facts** (`BootFacts`): putgetN's, at the token `restartN-11208` (`TestMemberIDs` in
`restartN_test.go` checks the ids for every `k ≤ 300`, the bound of `examples/etcd/all`).

**The Iris premises** (`premises`, persistent): `bootstrap`'s contract for each member's first start
(`etcdstart.bootPremise`, putgetN's `[∗list]`) and, for the members that may be stopped (`stopCands k`:
the last `min 2 (k - 1)` members, `k - 2` and `k - 1`), its restart case (`etcdstart.bootPremiseR`);
`proto.Marshal`'s contract at the bootstrap log (`bootMarshal`); the members' shared premises
(`etcdstart.commonPremises`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Swap
public import Perennial.Proof.sync.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootUnserved

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcd_restart etcdstart

section pure
variable [GooseExts]

/-- **The members of `Run(k)`'s cluster** (`Members("restartN", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"restartN" k (W64 14000) (W64 15000)

/-- **The members that may be stopped** (`Run`'s choice: member `k - 1`, or `k - 2` if `k > 2` and
member `k - 1` leads): the last `min 2 (k - 1)` members, with their ids. -/
def nStop (k : Nat) : Nat := min 2 (k - 1)

/-- **`bootstrap`'s results, as Go computes them** (putgetN's). -/
abbrev BootFacts (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry) : Prop :=
  etcd_putgetN.BootFacts ids ps ctxs bl

/-- **The peer-URL directory of the cluster**: each member's one peer URL (putgetN's). -/
abbrev dirN (ms : List GMember) (ids : List w64) : w64 → List GoString := etcd_putgetN.dirN ms ids

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **The token of `restartN`'s cluster** (`Token`). -/
abbrev token : GoString := go!"restartN-11208"

/-- **The members' peer addresses, not yet served** (2026-11-27): the frame each member's first boot lends
`bootstrap` (`etcdstart.addrsFree`, `bootstrap.specUnserved`): the right to listen at each member's peer address,
reserved for HTTP. `startMembers` holds it for every member while it builds them all, before serving any. -/
abbrev peersFree (ms : List GMember) : IProp GF := etcdstart.addrsFree (hG := hG) (ms.map (·.Peer'))

/-- **What `startMembers` takes per member** (`etcdstart.memberPre`, its contract `bootPremiseF` at the frame
`peersFree ms`): `bootstrap`'s contract at the member's name, URLs and id, its `memberBoot`, its network's HTTP
side and its fresh bundle (with its peer address). -/
def memberPreU (N : Nat) (ms : List GMember) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (x : GMember × MemberG GF) :
    IProp GF :=
  iprop(bootPremiseF (peersFree ms) N ps bootLog ctxs dir token x.1.Name' (urlsN ms x.1) x.2.id ∗
    memberBoot x.2.γ ctxs x.2.ρ x.2.E Φs x.2.id ∗ netHttpOk γn x.2.id ∗
    memberFreshRes x.1.Name' ⟨some x.1.Peer', none⟩ γn)

/-- **`Run(k)`'s named premises** (persistent; see the file header), at the bound `N`, the member ids
(in the members' order), the peers `ps` (in `bootstrap`'s order), the peers' contexts and the bootstrap
log. -/
def premises (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    -- (2026-11-28) at a member count `Run` covers (`k ≤ 1000`: the peer addresses loopback literals)
    (□ (⌜k ≤ 1000⌝ -∗ [∗list] m; id ∈ members k; ids,
      etcdstart.bootPremiseF (peersFree (members k)) N ps (LogEntry.toEntries boot 0) ctxs
        (dirN (members k) ids) token m.Name' (etcdstart.urlsN (members k) m) id)) ∗
    ([∗list] m; id ∈ (members k).drop (k - nStop k); ids.drop (k - nStop k),
      etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) token
        m.Name' (etcdstart.urlsN (members k) m) id))

instance premises_persistent (k N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) k N ids ps ctxs boot) := by
  unfold premises; infer_instance

/-- A handler's contract is persistent (its body is). -/
instance handlerOk_persistent' (H : http.HttpNet GF) (a : GoString) (Rs : IProp GF) (h : GoInterface) :
    Persistent (http.handlerOk H a Rs h) := by
  unfold http.handlerOk; infer_instance

/-- **The swap's lock invariant** (`Swap.lean`): the handler `sw.h` of the current incarnation, a
handler of the member's peer address `a` lending its incarnation's resource, and the mutex's view of
the current incarnation. -/
def swLock (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) : IProp GF :=
  iprop(∃ (h : _root_.Perennial.net.http.Handler) (c b : GName) (τ : SrvTr GF),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap go!"h" sw ↦ h ∗
    swCur γS γn c b τ ∗ http.handlerOk (raftHttpNet (netRh γn)) a (srvServeRes γn τ) h)

/-- **A member's peer handler** (persistent): `sw.mu` a mutex guarding `swLock`, and the swap's
global invariant, at `http.Serve`'s slot count. -/
def swapOk (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) : IProp GF :=
  iprop(⌜γS.n = http.httpProcSlots⌝ ∗ ∃ mu : Loc,
    structFieldRef github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap go!"mu" sw ↦□ mu ∗
    sync.isMutex mu (swLock sw γS γn a) ∗ swGInv γS)

instance swapOk_persistent (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) :
    Persistent (swapOk sw γS γn a) := by
  unfold swapOk; infer_instance

/-- **A member's record**: its peer handler `sw` (`swapOk`, at the member's peer address
`peerAddr`), its name, peer URLs (`[http://peerAddr]`) and client address. -/
def memberRec (m : Loc) (γS : SwNames) (γn : NetNames GF) (name peerAddr client : GoString) :
    IProp GF :=
  iprop(∃ (sw : Loc) (peer : GoSlice),
    m ↦ (github_com.mit_pdos.etcd_grove.examples.etcd.restartN.member.mk sw name peer client) ∗
    peer ↦*□ [etcdstart.httpURL peerAddr] ∗ swapOk sw γS γn peerAddr)

end defs

end etcd_restartN
end EtcdGrove
end Perennial
