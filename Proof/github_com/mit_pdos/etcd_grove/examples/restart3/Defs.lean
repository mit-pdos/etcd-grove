/-
**restart3's `Run` and its functions: their named premises and vocabulary** (the restart plan's
R2a, 2026-11-02, `notes/restart-plan.md`; DRAFT). Lean-first (no Rocq counterpart). putget3's
(`putget3/Defs.lean`) for the members of `examples/restart3/restart3.go`, with a member's stop and
restart.

**The pure facts** (`BootFacts`): putget3's, for `restart3`'s three configurations (the cluster
token `restart3`; `TestMemberIDs` in `restart3_test.go` prints the ids).

**The Iris premises** (`premises`, persistent): `bootstrap`'s contract for each member's first
start (`common.bootPremise`, in the shared start's form) and, for members 2 and 3 (either may be the
one stopped), its restart case (`common.bootPremiseR`, R2c); `proto.Marshal`'s contract at the
bootstrap log (`bootMarshal`); the members' shared premises (`common.commonPremises`).

**A stoppable member** (`memberStop`): what `startMember` returns besides the started member
(`common.memberUp`) and `stop` takes: the `member` record, the right to stop its server
(`srvStopRight`, R2b) once started (`srvStartRet`), and the right to close its peer listener
(`http.httpListenerCloser`, the draft boundary of `Proof/net/http/ListenerClose.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.restart3.Base
public import Proof.net.http.ListenerClose

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s results, as Go computes them** (pure facts of the program; see the file
header). (2026-10-27, the server port: the bootstrap log `bl` with the peers' contexts `ctxs` the
node API's `BootLog`, each entry a conf change of id `0` that the server's `applyConfChange` takes;
until then `srvBootLogOk (ccOk [id₁, id₂, id₃]) [id₁, id₂, id₃] bootLog`, under the conf-change
policy `ccOk`, over raft's records.) -/
structure BootFacts (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (bl : List LogEntry) :
    Prop where
  idLow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup
  idLow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0
  boot : BootLog [id₁, id₂, id₃] ctxs bl
  cc : ∀ e ∈ LogEntry.toEntries bl 0,
    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id₁, id₂, id₃]) e.Data'

/-- The members' names. -/
abbrev name₁ : GoString := go!"restart3-1"
abbrev name₂ : GoString := go!"restart3-2"
abbrev name₃ : GoString := go!"restart3-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:23861"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:23862"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:23863"

/-- The members' client addresses (served by `serveClient`: member 1's, and the restarted member's after its restart). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:23864"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:23865"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:23866"

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [common.httpURL peerAddr₁] else if k = name₂ then [common.httpURL peerAddr₂]
  else if k = name₃ then [common.httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration** (D19r (F), putget's at three members): its peer
URLs `[http://peerAddr]`, its client URLs `[http://client]`, the initial cluster's map (`Main`'s
`cluster`: the three members' names to their peer URL slices) and its URLs by name `initURLs3`. -/
def urlsOk (peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [common.httpURL peerAddr] ∧ U.client = [common.httpURL client] ∧
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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The token of `restart3`'s cluster.** -/
abbrev token : GoString := go!"restart3"

/-- **`Run`'s named premises** (persistent; see the file header), at the bound `N`, the member ids,
the peers' contexts and the bootstrap log. -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List LogEntry) :
    IProp GF :=
  iprop(
    common.bootPremise N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₁ (urlsOk peerAddr₁ clientAddr₁) id₁ ∗
    common.bootPremise N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₂ (urlsOk peerAddr₂ clientAddr₂) id₂ ∗
    common.bootPremise N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₃ (urlsOk peerAddr₃ clientAddr₃) id₃ ∗
    common.bootPremiseR N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₂ (urlsOk peerAddr₂ clientAddr₂) id₂ ∗
    common.bootPremiseR N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      token name₃ (urlsOk peerAddr₃ clientAddr₃) id₃ ∗
    bootMarshal [id₁, id₂, id₃] ctxs (LogEntry.toEntries boot 0) ∗
    common.commonPremises)

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8))
    (boot : List LogEntry) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ ctxs boot) := by
  unfold premises; infer_instance

/-- **A stoppable member** (DRAFT; see the file header): the `member` record at `m` (its server
`s`, its peer listener `pl`), the right to stop `s` once started, and the right to close `pl`,
served at `peerAddr` with member `id`'s raft protocol in the network `γn`. -/
def memberStop (m s : Loc) (pl : GoInterface) (γ : SrvRaft) (id : w64) (peerAddr : GoString)
    (γn : NetNames GF) : IProp GF :=
  iprop(m ↦ (github_com.mit_pdos.etcd_grove.examples.restart3.member.mk s pl) ∗
    srvStopRight s γ id ∗ ⌜srvStartRet s ∧ ∃ li : GoInterfaceOk, pl = GoInterface.ok li⌝ ∗
    http.httpListenerCloser pl peerAddr (raftProto (netRh γn)))

end defs

end restart3
end EtcdGrove
end Perennial
