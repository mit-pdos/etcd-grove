/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the definitions `putget_safe`'s statement is written in

`putget_safe` (`Spec/.../examples/etcd/dist/putget/TopLevelRobustness.lean`, `notes/putget-dist-plan.md`) is
about two machines that never crash: the member machine, running `putget.Member(peer, client)`, and the
client machine, running `putget.Client(client)` (`examples/etcd/dist/putget`), each after the package's
initializer. This file defines, over the extensions `etcdNetExts` (`examples/lib/etcdstart/NetExts.lean`: the
request ids' issue record, the Linux file extension at `etcdFsSem`, the net extension), the ghost-state bundle the
statement's Iris premises are stated at (`putgetGF`), the two boot programs, the system and its
addresses, and the member machine's file premise (`MemberFiles`).
-/
module

public import Robustness.Statement
public import Perennial.GooseLang.InitAdequacy
public import Net.Statement.DistDeploy
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Init

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem

/-! ## The ghost-state bundle -/

/-- **The functors** the statement's Iris premises are stated at: the universal camera `AllG` at slot
0 (every extension's and the proofs' ghost state), invariants, later credits, GooseLang's heap,
prophecies and package state, a ghost variable at slot 7 (`netGF`'s and the retired single-process
`etcdGF`'s layout). Every other slot is the unit functor. -/
def putgetGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def putgetGF_allG : AllG putgetGF := ⟨⟨0, rfl⟩⟩

/-- The ghost state of GooseLang over `etcdNetExts` (each extension's at the universal camera). -/
instance putgetGF_gooseGpreS : GooseGpreS putgetGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨putgetGF_allG⟩, ⟨putgetGF_allG⟩, ⟨putgetGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := putgetGF_allG

/-- **A ghost-state instance at the local context `lctx`** (the Iris premises are stated over every
instance of the ghost state whose Go local context is the semantics' own, as the retired
single-process `etcdHeapAt`). -/
abbrev putgetHeapAt (hG : HeapGS .hasLC putgetGF) (lctx : GoLocalContext) : HeapGS .hasLC putgetGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-! ## The programs and the system -/

section programs
variable [GoGlobalContext]

/-- The member's name (`putget.Name`): its cluster's token, its data directory
`/tmp/etcd-grove-data/putgetd.etcd` and WAL area `/tmp/etcd-grove-wal/putgetd.etcd`. -/
abbrev name : GoString := go!"putgetd"

/-- **The member machine's boot program**: `putget`'s initialization, then `putget.Member(peer, client)`
(the binary `cmd/member` passes its arguments: the parsing is not translated, a trusted gap). -/
def bootMember [GoSemanticsFunctions] (peer client : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.initialize' #() ;;
  App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Member)) (Val #peer))
    (Val #client)

/-- **The client machine's boot program**: `putget`'s initialization, then `putget.Client(client)`, the
member's client address verbatim (`cmd/client`). -/
def bootClient [GoSemanticsFunctions] (client : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.initialize' #() ;;
  App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Client)) (Val #client)

/-- **The system**: the member machine and the client machine, from the local states `σm`, `σc`. -/
def system [GoSemanticsFunctions] (peer client : GoString) (σm σc : state) : List (Expr × state) :=
  [(bootMember peer client, σm), (bootClient client, σc)]

/-- **The deployment's addresses**: the member's peer address (in its URLs; with one member nothing
listens there or dials it) and its client address (its gRPC listener, the client's endpoint). -/
def addrs (peer client : GoString) : List GoString := [peer, client]

end programs

/-! ## The member machine's files -/

/-- **The member machine's files at the start**: as on disk (`FsInit`: `etcdFsSem`, `Fs.fsSemWithS`, keeps
`ExtSemantics`'s default `initLocal`, so `Robust` does not give it; `notes/putget-dist-plan.md` section 5),
and the member's data directory and WAL area roots of its file system, empty of what a member creates
(`etcdWalAreasInit`, one directory: the single-process examples' premise, per machine). -/
def MemberFiles [ElemExt Fs.fsExt] (σ : state) : Prop :=
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  etcdWalAreasInit (extLocal Fs.fsExt σ.world) [memberDataDir name]

/-- **The client machine's files at the start**: as on disk (`FsInit`; its `fileutil` initializer probes
the file system, review F11 of `notes/etcd-dist-plan.md`). -/
def ClientFiles [ElemExt Fs.fsExt] (σ : state) : Prop :=
  Fs.FsInit (extLocal Fs.fsExt σ.world)

end etcd_putget_dist
end EtcdGrove
end Perennial

end
