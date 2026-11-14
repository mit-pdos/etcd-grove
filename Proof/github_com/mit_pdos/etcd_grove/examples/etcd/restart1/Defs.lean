/-
**restart1's functions: their named premises and vocabulary** (restart S7.5, 2026-11-14,
`notes/restart-s7-scope.md`). Lean-first (no Rocq counterpart). putget's (`putget/Defs.lean`) for the
one member of `examples/etcd/restart1/restart1.go`, with its stop and restart (restart3's,
`restart/Defs.lean`, at one member).

**The pure facts** (`BootFacts`): a one-member cluster's (`etcdstart.BootFacts`; the cluster token
`restart1`; `TestMemberID` in `restart1_test.go` prints the id).

**The Iris premises** (`premises`, persistent): a one-member `Main`'s (`etcdstart.premises`:
`bootstrap`'s contract for the first start, `proto.Marshal`'s at the bootstrap log, the members'
shared premises) and `bootstrap`'s restart contract (`etcdstart.bootPremiseR`, N1 of the Scope).

**A started member, split for its in-process writes and its stop** (`memberUp_splitStop`, probe P1
of `notes/restart-s7-probe.md`): at one apply environment, the request and read views, the
revocation's built part (from which an in-process `Put` borrows its `leadTimeMu` slot and `E.RD`), the
`GoAttach` resources, and what `HardStop` takes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopReaders
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s result, as Go computes it** (pure facts of the program): a one-member
cluster's (`etcdstart.BootFacts`, putget's). -/
abbrev BootFacts (id : w64) (ctxs : List (List w8)) (bl : List LogEntry) : Prop :=
  etcdstart.BootFacts id ctxs bl

/-- The member's name (its data directory `restart1.etcd`, its cluster token). -/
abbrev name : GoString := go!"restart1"

/-- The member's peer address (its one peer URL `http://` of it; not served). -/
abbrev peerAddr : GoString := go!"127.0.0.1:23811"

/-- The member's client address (its one client URL `http://` of it; not served). -/
abbrev clientAddr : GoString := go!"127.0.0.1:23812"

/-- **The URLs of the member's configuration** (`etcdstart.urls1`). -/
abbrev urlsOk (U : BootURLs) : Prop := etcdstart.urls1 name peerAddr clientAddr U

/-- **The peer-URL directory of the cluster** (`etcdstart.dir1`): the member's one peer URL. -/
abbrev dir (id : w64) : w64 → List GoString := etcdstart.dir1 peerAddr id

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`Run`'s named premises** (persistent; see the file header), at the bound `N`, the member id
`id`, the peers' contexts `ctxs` and the bootstrap log `boot`: a one-member `Main`'s
(`etcdstart.premises`) and `bootstrap`'s restart contract on the member's stopped data directory
(`etcdstart.bootPremiseR`, at the same configuration, URLs and directory). -/
def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) : IProp GF :=
  iprop(etcdstart.premises name peerAddr clientAddr N id ctxs boot ∗
    etcdstart.bootPremiseR N [id] (LogEntry.toEntries boot 0) ctxs (dir id) name name urlsOk id)

instance premises_persistent (N : Nat) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Persistent (premises (GF := GF) N id ctxs boot) := by
  unfold premises; infer_instance

/-- **A started member that is written in-process, then stopped** (see the file header; probe P1's
`probe_P1_split`): from `memberUp`, at one apply environment `E` agreeing with the stand-in, auth
off: the request and read views, the revocation's built part, the `GoAttach` resources, the right to
stop the server and its unused serving readers. -/
theorem memberUp_splitStop (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) (s : Loc) (ρ : ReqNames)
    (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64) (m : lease.Mode) :
    etcdstart.memberUp (GF := GF) s ρ E₀ lg γn id m ⊢
      ∃ (E : apply.AEnv GF) (γw : GName) (dd : GoString),
        ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
        isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvRevokeBuilt s E ∗
        srvGoRes s ∗
        srvStopRight s E ρ.rd.raft.raft ρ id dd ∗ srvStopReaders E := by
  iintro Hup
  iunfold etcdstart.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, Hstk, -, #Hreq, #Hrd, Hgo, -, -, -, -, -, -, -, %dd, Hr⟩
  ihave #Hb : srvRevokeBuilt s E $$ [Hstk]
  · iunfold srvServeStock at Hstk
    icases Hstk with ⟨#Hb, -⟩
    iexact Hb
  iexists E, γw, dd
  isplitr
  · ipureintro; exact ⟨HEc.1, HEc.2.1⟩
  iframe Hreq Hrd Hb Hgo Hr
  iapply srvStopReaders_intro hRS s E $$ Hstk

end defs

end etcd_restart1
end EtcdGrove
end Perennial
