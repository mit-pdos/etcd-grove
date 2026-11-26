/-
`DB.grow` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U10 (`Commit`). Proof:
`Proof/go_etcd_io/bbolt/DB__grow.lean` (a `sorry` until U4).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WdbFlag
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.grow(sz)` by the live writer: the file truncated up to (about) `sz` and synced unless
`NoGrowSync` (`wdbGrown`: only the file's size and the `W` slots it adds change); an error is a
`fmtErrorOk` one, the file's size possibly changed. Batch 37: `sz + AllocSize` is an `int64`
(`grow` truncates to it above `AllocSize`; session S3g: at most `maxMapSize`, the file's bound,
`wdbSz`) and `sz` a whole number of pages (so is the grown file,
`wdbOK`'s page clause); `Commit` passes `(pgid + 1) · 4096`. W1 (crash mode, stage B step 4): on
success with `NoGrowSync` off the file is at least `sz` or the mapping, whichever is smaller (`grow`
truncates to the mapping's length up to `AllocSize`, else past `sz`), so every page below the new
high-water mark is inside the file and a commit's writes are in-file. Batch 44.1: over the flagged writer side `wdbW' fr` (`Commit`
grows after the old freelist page's free; `wdbW_wdbW'`/`wdbW'_wdbW` convert at `fr = false`). -/
abbrev DB.grow.spec : Prop :=
  ∀ (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) (sz : w64),
  0 ≤ sint.Z sz → sint.Z sz + 0x1000000 ≤ 0xFFFFFFFFFFFF → sint.Z sz % 4096 = 0 →
  {{ K.core (GF := GF) ∗ wdbW' fr K tx v w }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"grow")) (Val #sz))
  {{ (err : GoInterface), RET #err; ∃ w' : WDb, wdbW' fr K tx v w' ∗ ⌜wdbGrown w w'⌝ ∗
      ((⌜err = interface.nil⌝ ∗
        (K.db.[DB, go!"NoGrowSync"] ↦□ false -∗ ⌜min (sint.Z sz).toNat (mapLen w.ms) ≤ w'.m.size⌝)) ∨
        ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err) }}

end spec

end bbolt
end EtcdGrove
end Perennial
