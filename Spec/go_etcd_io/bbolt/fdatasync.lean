/-
`fdatasync` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U10 (`Tx.write`, `writeMeta`). Proof:
`Proof/go_etcd_io/bbolt/fdatasync.lean` (a `sorry` until U4).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `fdatasync(db)` (`syscall.Fdatasync` of the file's fd): in-process, nothing but the file's
sync bookkeeping changes (durability is out of scope); an error is a `fmtErrorOk` one. -/
abbrev fdatasync.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (m : OsMeta) (dqf dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p dq ∗ osFd fd dq ⟨p, true, true⟩ ∗
      osMeta p (DFrac.own 1) (some m) }}
    (App (Val #(functions fdatasync [])) (Val #db))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p dq ∗
      osFd fd dq ⟨p, true, true⟩ ∗
      (∃ m' : OsMeta, osMeta p (DFrac.own 1) (some m') ∗ ⌜m'.size = m.size ∧ m'.maps = m.maps⌝) ∗
      (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err) }}

end spec

end bbolt
end EtcdGrove
end Perennial
