/- Lean-first (no Rocq counterpart). `db.Close()` (`examples/bboltfs/minibolt.go`, db.go's `Close`): all three locks, unmap, unlock the file, close it. It takes every reader token and the committer's token: nothing may use the handle afterwards (the locks' resources then hold no mapping and no open file). Unless the handle failed, it gives back the file (`dbClosed`): its `OsMeta`, its bytes, and what the current transaction `t` holds, for the caller to reopen it. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapCells
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

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

/-- A database closed while not failed, at transaction `t`, on the path `p`: the whole of the
file's `OsMeta` `m` (no byte lost by a failed sync, `ok`), the meta pages' bytes (clean, valid,
`metaPagesOk`, the current meta at `t`), the
committed pages (`pageIs`, discarded), the current root page holding `dbTx γ t`'s value, and the
bytes from the high water mark on, whole. The mapping is gone, or (a failed `Munmap`) still there,
with its cells' client halves. -/
def dbClosed (γ : DBNames) (p : GoString) (t : Nat) : IProp GF :=
  iprop(∃ (m : OsMeta) (mp : List w8) (mxc tail : List (w8 × Bool)) (B : List w8),
    osMeta (GF := GF) p (DFrac.own 1) (some m) ∗ osBytes (GF := GF) p 0 (DFrac.own 1) mxc ∗
    ([∗list] r ∈ List.range' 2 (curPgid mp - 2), ∃ B', pageIs (GF := GF) p r B') ∗
    osBytes (GF := GF) p (4096 * curPgid mp) (DFrac.own 1) tail ∗
    pageIs (GF := GF) p (curRoot mp) B ∗ dbTx (GF := GF) γ t (pageVal B) ∗
    ⌜mxc.map Prod.fst = mp ∧ (∀ x ∈ mxc, x.2 = true) ∧ metaPagesOk mp ∧
      (curMeta mp).txid'.toNat = t ∧ 4096 * curPgid mp ≤ m.size ∧
      tail.length = m.size - 4096 * curPgid mp ∧ m.ok = true⌝ ∗
    (⌜m.maps = ∅⌝ ∨ ∃ (base : Loc) (len : Nat) (vf : Nat → val),
      ⌜m.maps = {[base := len]}⌝ ∗ cellsR (GF := GF) base 0 len vf))

/-- See the file header. -/
abbrev DB.Close.spec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t n : Nat),
  {{ isDB (GF := GF) γ db ∗ dbOwner (GF := GF) γ t n ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        dbReader (GF := GF) γ db) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ RET #(); ∃ p : GoString, db.[DB, go!"path"] ↦□ p ∗
      (dbClosed (GF := GF) γ p t ∨ dbFailed (GF := GF) γ) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
