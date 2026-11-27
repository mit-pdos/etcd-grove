/-
`DB.needsInit` (bbolt, internal; the fork's crash-safe `init`, `issues/bbolt-init-not-crash-safe.md`):
whether `Open` initializes the file, in `Open`'s owned phase (U11, `notes/bbolt-proof-plan.md`).
Proof: `Proof/go_etcd_io/bbolt/DB__needsInit.lean`; `Open/InitPartial.lean` shows that a well-formed
file it accepts holds no data.
-/
module

public import Spec.go_etcd_io.bbolt.DB__initImage
public import Proof.go_etcd_io.bbolt.Open.ReadHeld
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.needsInit(size)`**, `size` the file's size (`Stat`'s), the file's bytes `xs` held from
offset 0, the page size `4096` and `readOnly` any value: no error, initialization for an empty
file, and initialization only for an empty file or bytes an interrupted `init` can leave
(`initPartial`: at most four pages, each byte zero or `initImg`'s); or a read error (`fmt` formats
it). (The code also refuses `initImg` itself and, read-only, every nonempty file; the spec does not
say so.) -/
abbrev DB.needsInit.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (dqdb dqf dq dqb : DFrac) (d : OsFd) (ro : Bool)
    (xs : List ByteG),
  d.readable = true → d.ino = p.ino → xs.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      db.[DB, go!"readOnly"] ↦{dqdb} ro ∗
      fileOwn f fd p.path dqf ∗ osFd fd dq d ∗ osBytes p.ino 0 dqb xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"needsInit"))
      (Val #(W64 (xs.length : Int))))
  {{ (z : Bool) (err : GoInterface), RET (PairV #z #err);
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      db.[DB, go!"readOnly"] ↦{dqdb} ro ∗
      fileOwn f fd p.path dqf ∗ osFd fd dq d ∗ osBytes p.ino 0 dqb xs ∗
      ((⌜err = interface.nil ∧ (xs.length = 0 → z = true) ∧
          (z = true → xs.length = 0 ∨ initPartial (xs.map Prod.fst))⌝) ∨
       (⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗ fmtErrorOk err)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
