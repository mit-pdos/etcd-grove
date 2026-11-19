/- Lean-first (no Rocq counterpart).

# `etcd/auth3`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The program: `auth3`'s initialization, then `Main()`. -/
def auth3Program [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.auth3.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Main) #()

/-- The program's addresses: the three members' peer and client addresses. -/
def auth3Addrs : List GoString :=
  [etcd_auth3.peerAddr₁, etcd_auth3.peerAddr₂, etcd_auth3.peerAddr₃, etcd_auth3.clientAddr₁,
    etcd_auth3.clientAddr₂, etcd_auth3.clientAddr₃]

/-- The read package's two metric names, which `auth3`'s initialization registers. -/
def auth3Names : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

end adequacy
end EtcdGrove
end Perennial

end

end
