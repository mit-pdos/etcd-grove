/- Lean-first (no Rocq counterpart).

# `etcd/all`: the definitions its top-level statement is written in

The program the single-process closed etcd theorem (`etcd_restart_safe_single_process`, `notes/etcd-unified-scope.md`;
retired at the net swap as `etcd_safe`, restored 2026-11-23 over the net extension, `notes/single-process-restore.md`)
is about, and the
other definitions its statement names: the ghost-state bundle (partition's `linkvGF`, renamed: the
superset of the slots the drivers' triples use), and the two clusters' addresses and data directories:
restartN's `k₅` members and restart1's one, which listens on no address. (Until 2026-11-27 the program
also ran the KV, Auth and Lease parts, nine more clusters.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
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

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

/-- The functors: putget's (the universal camera `AllG` at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state), a ghost variable at slot 7, and iris-lean's
non-atomic invariants at slot 11 (porcupine's): partition's `linkvGF`, a superset of the slots every
driver's triple uses (each is GF-polymorphic). Every other slot is the unit functor. -/
def etcdGF : BundledGFunctors := fun i =>
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
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses are stated over every
instance of the ghost state whose Go local context is the semantics' own). -/
abbrev etcdHeapAt (hG : HeapGS .hasLC etcdGF) (lctx : GoLocalContext) : HeapGS .hasLC etcdGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **The program**: `etcdall`'s initialization, then `MainChecked(k5)`: restartN's member count `k₅`.
`MainChecked` returns at once unless the count is in the range `Main`'s proof covers (`ParamsOk`;
until the pure-premises plan's P4, 2026-11-24, the program was `Main` with the count's range a premise
of the statement). -/
def etcdProgram [GoSemanticsFunctions] (k₅ : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.all.initialize' #() ;;
  App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked)) (Val #k₅)

/-- **The program's addresses** (those it listens on): restartN's `k₅` peer addresses. (restart1
listens on none.) -/
def etcdAddrs (k₅ : Nat) : List GoString :=
  etcd_restartN.restartNAddrs k₅

/-- **The program's data directories**, one per member (`/tmp/etcd-grove-data/<name>.etcd`): restartN's,
then restart1's. -/
def etcdDirs (k₅ : Nat) : List GoString :=
  etcd_restartN.restartNDirs k₅ ++ [go!"/tmp/etcd-grove-data/restart1.etcd"]

/-- **The member count `MainChecked` starts the clusters at** (`ParamsOk`, 2026-11-24, the
pure-premises plan's P4): `3 ≤ k₅ ≤ 300`. -/
def etcdCountsOk (k₅ : w64) : Prop :=
  3 ≤ uint.nat k₅ ∧ uint.nat k₅ ≤ 300

instance (k₅ : w64) : Decidable (etcdCountsOk k₅) := by
  unfold etcdCountsOk; infer_instance

/-- **The addresses `etcdProgram` may listen on** (P4):
`etcdAddrs` at the member count when it is in range, none otherwise (`MainChecked` then returns
without starting a member). -/
def etcdProgAddrs (k₅ : w64) : List GoString :=
  if etcdCountsOk k₅ then etcdAddrs (uint.nat k₅) else []

/-- **The data directories `etcdProgram` may use**: `etcdDirs` at the member count when it is in
range, none otherwise (as `etcdProgAddrs`). -/
def etcdProgDirs (k₅ : w64) : List GoString :=
  if etcdCountsOk k₅ then etcdDirs (uint.nat k₅) else []

end adequacy
end EtcdGrove
end Perennial

end
