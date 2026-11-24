/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the definitions `putgetK_safe`'s statement is written in (DRAFT for review)

`putgetK_safe` (`Spec/.../examples/etcd/dist/putgetk/TopLevelRobustness.lean`, `notes/putget-dist-plan.md`
§13) is about `k = 3` member machines and one client machine, none of which crashes: member `i`'s machine
runs `putgetk.Member(i, peers, clients)`, the client machine `putgetk.Client(client₀)`
(`examples/etcd/dist/putgetk`), each after the package's initializer. This file defines, over the
extensions `etcdNetExts` (`examples/lib/etcdstart/NetExts.lean`) and at `putget_safe`'s ghost-state bundle
`putgetGF` (`dist/putget/TopLevelDefs.lean`), the deployment's members and addresses (fixed: the
namespace test's, `TestPutGetK`), the boot programs, the system, the members' named premises and the
member machines' file premise.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
  etcdstart

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem

/-! ## The deployment (`k = 3`, fixed addresses) -/

section deployment
variable [GooseExts]

/-- **The cluster's members** (Go's `etcdstart.Member` values: name, peer address, client address): member
`i` (from `0`) is named `putgetk-i` (`putgetk.Name(i)`) and runs on the machine `10.77.(i+1).1`, its peer
address on port `2380`, its client address on port `2379` (the namespace test's machines,
`examples/lib/robust`'s `AddMachine`). -/
def members : List GMember :=
  [⟨go!"putgetk-0", go!"10.77.1.1:2380", go!"10.77.1.1:2379"⟩,
   ⟨go!"putgetk-1", go!"10.77.2.1:2380", go!"10.77.2.1:2379"⟩,
   ⟨go!"putgetk-2", go!"10.77.3.1:2380", go!"10.77.3.1:2379"⟩]

/-- The members' peer addresses, in the members' order (`Member`'s `peers`). -/
abbrev peers : List GoString := members.map (·.Peer')

/-- The members' client addresses, in the members' order (`Member`'s `clients`). -/
abbrev clients : List GoString := members.map (·.Client')

/-- The client machine's endpoint: member `0`'s client address. -/
abbrev endpoint : GoString := go!"10.77.1.1:2379"

/-- The cluster's token (`putgetk.Token`). -/
abbrev token : GoString := go!"putgetk"

/-- **The deployment's addresses**: every member's peer address (its raft handler's listener, which the
other members dial) and client address (its gRPC listener; member `0`'s is the client's endpoint). -/
def addrs : List GoString := peers ++ clients

end deployment

/-! ## The programs and the system -/

section programs
variable [GoGlobalContext]

/-- **The Go slice literal `[]string{l₀, …, lₙ}`** (goose's translation of a composite literal of
`[]string` whose elements are the constant strings `l`: a new slice of them). -/
def strSliceLit [GooseExts] (l : List GoString) : Expr :=
  App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (LiteralValue (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))))

/-- **Member `i`'s machine's boot program**: `putgetk`'s initialization, then
`putgetk.Member(i, []string{peers…}, []string{clients…})` (the binary `cmd/member` passes its arguments,
the index and the two comma-separated lists: the parsing is not translated, a trusted gap). -/
def bootMember [GoSemanticsFunctions] (i : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.initialize' #() ;;
  App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Member))
    (Val #(W64 i))) (strSliceLit peers)) (strSliceLit clients)

/-- **The client machine's boot program**: `putgetk`'s initialization, then `putgetk.Client(endpoint)`,
member `0`'s client address verbatim, its result discarded (`cmd/client` only prints it). -/
def bootClient [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.initialize' #() ;;
  (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Client)) (Val #endpoint) ;;
    Val #())

/-- **The system**: member `i`'s machine from the local state `σs[i]`, for each `i < σs.length`, then the
client machine from `σc`. -/
def system [GoSemanticsFunctions] (σs : List state) (σc : state) : List (Expr × state) :=
  σs.mapIdx (fun i σ => (bootMember i, σ)) ++ [(bootClient, σc)]

end programs

/-! ## The members' named premises -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The members' named premises** (persistent): putget's `etcdstart.premises` per member, in the
multi-member form of the in-process `putgetN` (`etcd_putgetN.premises` at these members and token), at
the bound `N` of each member's apply thread's write tokens, the member ids `ids` (in the members' order),
the peers `ps`, their contexts and the bootstrap log: per member, `bootstrap`'s contract
(`etcdstart.bootPremise`) for its configuration (`cfgOk token name`) and URLs (`urlsN members m`: its peer
URL, its client URL, the initial cluster's map of every member's peer URL) at the peer-URL directory
`dirN` (each member id's one peer URL); `proto.Marshal`'s contract at the bootstrap log
(`bootMarshal`); the raft wrapper's trust-boundary contracts (`etcdstart.commonPremises`). -/
def premises (N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    ([∗list] m; id ∈ members; ids,
      etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN members ids) token
        m.Name' (urlsN members m) id) ∗
    bootMarshal ps ctxs (LogEntry.toEntries boot 0) ∗
    etcdstart.commonPremises)

instance premises_persistent (N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Persistent (premises (GF := GF) N ids ps ctxs boot) := by
  unfold premises; infer_instance

end defs

/-! ## The machines' files -/

/-- **Member `i`'s machine's files at the start**: as on disk (`FsInit`), and member `i`'s data directory
and WAL area roots of its file system, empty of what a member creates (`etcdWalAreasInit`, one directory:
putget's `MemberFiles` at member `i`'s name). -/
def MemberFiles [ElemExt Fs.fsExt] (i : Nat) (σ : state) : Prop :=
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  ∃ m, members[i]? = some m ∧ etcdWalAreasInit (extLocal Fs.fsExt σ.world) [memberDataDir m.Name']

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
