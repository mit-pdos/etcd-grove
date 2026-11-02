/- Lean-first (no Rocq counterpart). `Open(path)`'s crash-aware spec: `Open.spec` (`Open.lean`)
over the crash invariant of the database file (`csInv dbCrashN path γc (dbOk path)`,
`DBCrash.lean`). The client holds its part of the file as a generation starts with it
(`csOwn path γc (csStart fo)`, as `csInv_alloc` and `csInv_crash_keep` give): no file, or a file
`f` whose bytes `f.cur` are all clean and durable, a `Good` image (`goodImg`, what a crash
leaves). Its transaction `t`, value `vo` and high water mark `n` are `freshTx`'s, as in
`Open.spec`, and the client's predicate on transactions `vp` holds of them and implies
`BootMinibolt`'s check (`bootOk`), which the crash invariant needs of every committed root page.
On success, an open database over the crash invariant (`isDBC`) as `Open.spec`'s; on an error,
some state of the file. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DBCrash
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

/-- The bytes of the file a generation starts with: none if absent. -/
def startImg : Option OsFile → List w8
  | none => []
  | some f => f.cur

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev Open.specCrash : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (path : GoString) (γc : GName) (fo : Option OsFile) (t : Nat)
    (vo : Option w64) (n : Nat) (vp : Nat → Option w64 → Prop),
  Good fo → freshTx ((startImg fo).map (·, true)) = (t, vo, n) → vp t vo →
  (∀ t vo, vp t vo → bootOk t vo) →
  {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ csInv (GF := GF) dbCrashN path γc (dbOk path) ∗
      csOwn (GF := GF) path γc (csStart fo) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.Open)) (Val #path))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err);
      (⌜err = interface.nil⌝ ∗ ∃ γ : DBNames, ⌜γ.vp = vp⌝ ∗
          isDBC (GF := GF) γ γc db ∗ db.[DB, go!"path"] ↦□ path ∗ dbOwner (GF := GF) γ t n ∗
          dbLast (GF := GF) γ t ∗ dbTx (GF := GF) γ t vo) ∨
      (⌜err ≠ interface.nil ∧ db = null⌝ ∗ ∃ s' : CState, csOwn (GF := GF) path γc s') }}

end spec

end bboltfs
end EtcdGrove
end Perennial
