/-
**restart3's `Run` and its functions: their named premises and vocabulary** (restart3 C2,
2026-11-15, `notes/restart3-handoff.md`; the restart plan's R2a draft until then). Lean-first (no Rocq
counterpart). putget3's (`putget3/Defs.lean`) for the members of `examples/etcd/restart/restart3.go`,
with a member's stop and restart.

**The pure facts** (`BootFacts`): putget3's, for `restart3`'s three configurations (the cluster
token `restart3`; `TestMemberIDs` in `restart3_test.go` prints the ids).

**The Iris premises** (`premises`, persistent): `bootstrap`'s contract for each member's first
start (`etcdstart.bootPremise`, in the shared start's form) and, for members 2 and 3 (either may be the
one stopped), its restart case (`etcdstart.bootPremiseR`); `proto.Marshal`'s contract at the
bootstrap log (`bootMarshal`); the members' shared premises (`etcdstart.commonPremises`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Swap
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s results, as Go computes them** (pure facts of the program; see the file
header): putget3's (2026-11-09, raft-entsize [r3a]: until then a field-for-field copy of it). -/
abbrev BootFacts (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (bl : List LogEntry) : Prop :=
  etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs bl

/-- The members' names. -/
abbrev name₁ : GoString := go!"restart3-1"
abbrev name₂ : GoString := go!"restart3-2"
abbrev name₃ : GoString := go!"restart3-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:23861"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:23862"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:23863"

/-- The members' client addresses (each member's one client URL `http://` of it; not served). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:23864"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:23865"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:23866"

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [etcdstart.httpURL peerAddr₁] else if k = name₂ then [etcdstart.httpURL peerAddr₂]
  else if k = name₃ then [etcdstart.httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration** (D19r (F), putget's at three members): its peer
URLs `[http://peerAddr]`, its client URLs `[http://client]`, the initial cluster's map (`Main`'s
`cluster`: the three members' names to their peer URL slices) and its URLs by name `initURLs3`. -/
def urlsOk (peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [etcdstart.httpURL peerAddr] ∧ U.client = [etcdstart.httpURL client] ∧
    (∃ sl₁ sl₂ sl₃ : GoSlice,
      U.initMap = GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅))) ∧
    U.initURLs = initURLs3

/-- **The peer-URL directory of `Main`'s cluster** (D21 M2): each member's one peer URL. -/
def dir3 (id₁ id₂ id₃ : w64) (id : w64) : List GoString :=
  if id = id₁ then [go!"http://" ++ peerAddr₁] else if id = id₂ then [go!"http://" ++ peerAddr₂]
  else if id = id₃ then [go!"http://" ++ peerAddr₃] else []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- **The token of `restart3`'s cluster.** -/
abbrev token : GoString := go!"restart3"

/-- **`Run`'s named premises** (persistent; see the file header), at the bound `N`, the member ids,
the peers `ps` (in `bootstrap`'s order), the peers' contexts and the bootstrap log. -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₁ (urlsOk peerAddr₁ clientAddr₁) id₁ ∗
    etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₂ (urlsOk peerAddr₂ clientAddr₂) id₂ ∗
    etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₃ (urlsOk peerAddr₃ clientAddr₃) id₃ ∗
    etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₂ (urlsOk peerAddr₂ clientAddr₂) id₂ ∗
    etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₃ (urlsOk peerAddr₃ clientAddr₃) id₃)

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ ps ctxs boot) := by
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
    structFieldRef github_com.mit_pdos.etcd_grove.examples.etcd.restart.raftSwap go!"h" sw ↦ h ∗
    swCur γS γn c b τ ∗ http.handlerOk (raftHttpNet (netRh γn)) a (srvServeRes γn τ) h)

/-- **A member's peer handler** (persistent): `sw.mu` a mutex guarding `swLock`, and the swap's
global invariant, at `http.Serve`'s slot count. -/
def swapOk (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) : IProp GF :=
  iprop(⌜γS.n = http.httpProcSlots⌝ ∗ ∃ mu : Loc,
    structFieldRef github_com.mit_pdos.etcd_grove.examples.etcd.restart.raftSwap go!"mu" sw ↦□ mu ∗
    sync.isMutex mu (swLock sw γS γn a) ∗ swGInv γS)

instance swapOk_persistent (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) :
    Persistent (swapOk sw γS γn a) := by
  unfold swapOk; infer_instance

/-- **A member's record**: its peer handler `sw` (`swapOk`, at the member's peer address
`peerAddr`), its name, peer URLs (`[http://peerAddr]`) and client address. -/
def memberRec (m : Loc) (γS : SwNames) (γn : NetNames GF) (name peerAddr client : GoString) :
    IProp GF :=
  iprop(∃ (sw : Loc) (peer : GoSlice),
    m ↦ (github_com.mit_pdos.etcd_grove.examples.etcd.restart.member.mk sw name peer client) ∗
    peer ↦*□ [etcdstart.httpURL peerAddr] ∗ swapOk sw γS γn peerAddr)

end defs

end etcd_restart
end EtcdGrove
end Perennial
