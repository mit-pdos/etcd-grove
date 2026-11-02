/- Lean-first (no Rocq counterpart). `db.readPageSize()` (`examples/bboltfs/minibolt.go`, db.go's `getPageSize`): reads meta pages 0 and 1 of `db.file` with `ReadAt`, before the file is mapped, and answers the page size of the first that it read and that validates. The file holds at least those two pages (`Open` calls it when `filesz ≥ 4 * pageSize`); the client holds a fraction of their bytes `xs` and of the file's `OsMeta`. A read may fail (an environmental failure), which is an error (never "no valid meta": `Open` would initialize over the database). Without an error, `ok` says whether a meta of the two is valid (`fileMeta`), and the size is that of the first valid one. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Store
public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.readPageSize.spec : Prop :=
  ∀ (db f : Loc) (dqd : DFrac) (fd : w64) (name : GoString) (dqf dq dqm dqb : DFrac) (d : OsFd)
    (m : OsMeta) (xs : List (w8 × Bool)),
  d.readable = true → xs.length = 2 * 4096 → 2 * 4096 ≤ m.size →
  {{ osInv (GF := GF) ∗ db.[DB, go!"file"] ↦{dqd} f ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path dqm (some m) ∗
      osBytes (GF := GF) d.path 0 dqb xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"readPageSize")) (Val #()))
  {{ (ps : w64) (ok : Bool) (err : GoInterface), RET (PairV (PairV #ps #ok) #err);
      db.[DB, go!"file"] ↦{dqd} f ∗ os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      osMeta d.path dqm (some m) ∗ osBytes d.path 0 dqb xs ∗
      ⌜err = interface.nil →
        (ok = true → ∃ i < 2, metaValid (fileMeta (xs.map Prod.fst) i) ∧
          ps = W64 (uint.Z (fileMeta (xs.map Prod.fst) i).pageSize')) ∧
        (ok = false → ∀ i < 2, ¬ metaValid (fileMeta (xs.map Prod.fst) i))⌝ }}

end spec

end bboltfs
end EtcdGrove
end Perennial
