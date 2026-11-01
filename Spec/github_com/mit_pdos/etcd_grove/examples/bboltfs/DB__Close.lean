/- Lean-first (no Rocq counterpart). `db.Close()` (`examples/bboltfs/minibolt.go`, db.go's `Close`): all three locks, unmap, unlock the file, close it. It takes the committer's token: no `Commit` or `Close` may follow, and a read afterwards finds no mapping and refuses (the locks' resources then hold no mapping and no open file). It returns `close`'s error. On success, unless the handle failed, it gives back the file (`dbClosed`): its `OsMeta`, its bytes, and what the current transaction `t` holds, at the token's high water mark `n`, for the caller to reopen it. A failed handle's token is at high water mark 0 (`Commit`), so a caller whose token has a positive one knows `Close` gives the file back if it returns no error. -/
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

/-- A database closed while not failed, at transaction `t` and high water mark `n`, on the path `p`: the whole of the
file's `OsMeta` `m` (no byte lost by a failed sync, `ok`), the meta pages' bytes (clean, valid,
`metaPagesOk`, the current meta at `t`), the
committed pages (`pageIs`, discarded), the current root page holding `dbTx γ t`'s value, and the
bytes from the high water mark on, whole. The mapping is gone, and the file is at least four pages
and at most 1 GiB: what `Open` accepts (`dbClosed_reopen`). -/
def dbClosed (γ : DBNames) (p : GoString) (t n : Nat) : IProp GF :=
  iprop(∃ (m : OsMeta) (mp : List w8) (mxc tail : List (w8 × Bool)) (B : List w8),
    osMeta (GF := GF) p (DFrac.own 1) (some m) ∗ osBytes (GF := GF) p 0 (DFrac.own 1) mxc ∗
    ([∗list] r ∈ List.range' 2 (curPgid mp - 2), ∃ B', pageIs (GF := GF) p r B') ∗
    osBytes (GF := GF) p (4096 * curPgid mp) (DFrac.own 1) tail ∗
    pageIs (GF := GF) p (curRoot mp) B ∗ dbTx (GF := GF) γ t (pageVal B) ∗
    ⌜mxc.map Prod.fst = mp ∧ (∀ x ∈ mxc, x.2 = true) ∧ metaPagesOk mp ∧
      (curMeta mp).txid'.toNat = t ∧ curPgid mp = n ∧ 4096 * curPgid mp ≤ m.size ∧
      tail.length = m.size - 4096 * curPgid mp ∧ m.ok = true ∧ m.maps = ∅ ∧
      4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 30⌝)

/-- See the file header. -/
abbrev DB.Close.spec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t n : Nat),
  {{ isDB (GF := GF) γ db ∗ dbOwner (GF := GF) γ t n }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ p : GoString, db.[DB, go!"path"] ↦□ p ∗
      ((⌜err = interface.nil⌝ ∗ dbClosed (GF := GF) γ p t n) ∨ ⌜err ≠ interface.nil⌝ ∨
        (⌜n = 0⌝ ∗ dbFailed (GF := GF) γ)) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
