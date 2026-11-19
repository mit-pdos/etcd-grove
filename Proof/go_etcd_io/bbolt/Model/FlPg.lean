/-
A synced freelist page's validity, over its bytes (session S4, for `Tx.WriteTo`): what a file
image asks of its freelist page (`Inv/FileImg.lean`'s `flFileOK`), stated over the page's bytes,
so that the store can record it of the bytes it holds and a reader can carry it.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Mvcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

section flpg
variable [GooseExts]

/-- **A synced freelist page's bytes `pg` at page `f` are valid for the committed state `C`** (session
S4): what `flFileOK` asks of a file's freelist page (`Inv/FileImg.lean`), over the page's bytes. -/
def flPgOK (C : CommitSt) (f : Nat) (pg : List w8) : Prop :=
  2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat ∧ x.toNat < C.hwm) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg)) ∧
      ¬ coversSlot C.pages x.toNat) ∧
    (∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s) ∧
    pageId pg = f

end flpg

end bbolt
end EtcdGrove
end Perennial
