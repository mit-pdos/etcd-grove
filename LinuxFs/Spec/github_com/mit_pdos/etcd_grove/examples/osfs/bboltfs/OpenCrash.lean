/- Lean-first (no Rocq counterpart). `Open(path)`'s crash-aware spec: `Open.spec` (`Open.lean`)
over the crash invariant of the database file (`csInv dbCrashN path R γc Good dbOk`,
`DBCrash.lean`). The client holds its part of the file at `d/b` (in the roots `R`, the
history `V`) as a generation starts with it (`StartSt`: no file, or a file as on disk, all of it
clean and durable, `Good`, as `csInv_alloc` and `csInv_crash_keep` give). Its transaction `t`, value `vo` and high water mark `n` are `freshTx`'s, as in
`Open.spec`, and the client's predicate on transactions `vp` holds of them and implies
`BootMinibolt`'s check (`bootOk`), which the crash invariant needs of every committed root page.
On success, an open database over the crash invariant (`isDBC`) as `Open.spec`'s; on an error,
some state of the file. -/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DBCrash
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

/-- A state the generation starts the database file with: absent, or as on disk and `Good`. -/
def StartSt [GooseExts] (s : CState) : Prop :=
  s = none ∨ ∃ i vs sz, s = csStart i (OsFile.ofDisk vs sz) ∧
    Good (some (OsFile.ofDisk vs sz))

/-- The bytes of the file of a state: none if absent. -/
def startImg : CState → List w8
  | none => []
  | some (_, x) => x.bs.map Prod.fst

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev Open.specCrash : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (d b : GoString) (R : Roots) (V : Hist) (j : Ino) (γc : GName)
    (s : CState) (t : Nat) (vo : Option w64) (n : Nat) (vp : Nat → Option w64 → Prop),
  NameOk b → lookupH R V d = some (.dir j) → StartSt s →
  freshTx ((startImg s).map durB) = (t, vo, n) → vp t vo →
  (∀ t vo, vp t vo → bootOk t vo) →
  {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ csInv (GF := GF) dbCrashN (child d b) R γc Good dbOk ∗
      csOwn (GF := GF) (child d b) R γc s V }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Open)) (Val #(child d b)))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err);
      (⌜err = interface.nil⌝ ∗ ∃ γ : DBNames, ⌜γ.vp = vp⌝ ∗
          isDBC (GF := GF) γ γc db ∗ db.[DB, go!"path"] ↦□ (child d b) ∗ dbOwner (GF := GF) γ t n ∗
          dbLast (GF := GF) γ t ∗ dbTx (GF := GF) γ t vo) ∨
      (⌜err ≠ interface.nil ∧ db = null⌝ ∗ ∃ s' : CState, csOwnF (GF := GF) γc s') }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
