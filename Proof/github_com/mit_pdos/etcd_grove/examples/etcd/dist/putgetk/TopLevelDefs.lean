/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the definitions `putgetK_safe`'s statement is written in (n members; `notes/putget-dist-plan.md` §13)

`putgetK_safe` (`Spec/.../examples/etcd/dist/putgetk/TopLevelRobustness.lean`) is about a cluster of any
number of members, each on a machine of its own, and one client machine, none of which crashes: member `i`'s
machine runs `putgetk.Member(i, peers, clients)`, the client machine `putgetk.Client(clients[0])`
(`examples/etcd/dist/putgetk`), each after the package's initializer. The configuration (`peers`,
`clients`: the members' peer and client addresses) is the statement's parameter, unconstrained: the
program checks what etcd needs of it (`putgetk.Valid`) and stops if it does not hold. This file defines,
over the extensions `etcdNetExts` and at `putget_safe`'s ghost-state bundle `putgetGF`, the members
(`membersOf`), their ids as etcd computes them (`memberIdOf`, `idsOf`), the boot programs, the system, the
members' named premises (`premises`, the in-process `putgetN`'s audited form), `bootstrap`'s log facts
(`BootLogFacts`) and the machines' file premises.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
  etcdstart

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem

/-! ## The programs and the system -/

section programs
variable [GoGlobalContext]

/-- **The Go slice literal `[]string{l₀, …, lₙ}`** (goose's translation of a composite literal of
`[]string` whose elements are the constant strings `l`: a new slice of them). -/
def strSliceLit [GooseExts] [GoGlobalContext] (l : List GoString) : Expr :=
  App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (LiteralValue (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))))

/-- **Member `i`'s machine's boot program**: `putgetk`'s initialization, then
`putgetk.Member(i, []string{peers…}, []string{clients…})` (the binary `cmd/member` passes its arguments,
the index and the two comma-separated lists: the parsing is not translated, a trusted gap). -/
def bootMember [GoSemanticsFunctions] (peers clients : List GoString) (i : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.initialize' #() ;;
  App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Member))
    (Val #(W64 i))) (strSliceLit peers)) (strSliceLit clients)

/-- **The client machine's boot program**: `putgetk`'s initialization, then `putgetk.Client(ep)`, its
result discarded (`cmd/client` only prints it). -/
def bootClient [GoSemanticsFunctions] (ep : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.initialize' #() ;;
  (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Client)) (Val #ep) ;;
    Val #())

/-- **The system**: member `i`'s machine from the local state `σs i`, one per peer address, then the
client machine from `σc`, against member `0`'s client address (`""` if there is none: `Client` stops). -/
def system [GoSemanticsFunctions] (peers clients : List GoString) (σs : Nat → state) (σc : state) :
    List (Expr × state) :=
  peers.mapIdx (fun i _ => (bootMember peers clients i, σs i)) ++ [(bootClient (clients.headD go!""), σc)]

end programs

/-! ## The machines' files -/

/-- **Member `i`'s machine's files at the start**: as on disk (`FsInit`), and member `i`'s data directory
and WAL area roots of its file system, empty of what a member creates (`etcdWalAreasInit`, one directory:
putget's `MemberFiles` at member `i`'s name). -/
def MemberFiles [GooseExts] [ElemExt Fs.fsExt] (i : Nat) (σ : state) : Prop :=
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  etcdWalAreasInit (extLocal Fs.fsExt σ.world) [memberDataDir (nameOf i)]

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
