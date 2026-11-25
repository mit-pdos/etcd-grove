/- Lean-first (no Rocq counterpart).

# `ReadAll`'s handle, the ghost facts (W3/W5 of `notes/wal-fsext-plan.md`, twenty-sixth session)

* `walDirKey_agree`: two keys of one directory agree (the directory's key is a persistent element of
  the keys' map): `w.dirFile`'s inode (`walOpeningF`'s key) is the read tie's `j`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode

section iris
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- **Two keys of one WAL directory's incarnation agree.** -/
theorem walDirKey_agree (dir : GoString) (i : Nat) (j j' : Fs.Ino) (X X' : List GoString) :
    ⊢@{IProp GF} walDirKey (W := W) dir i j X -∗ walDirKey (W := W) dir i j' X' -∗ ⌜j = j' ∧ X = X'⌝ := by
  unfold walDirKey
  letI := walAllG (W := W)
  iintro ⟨#H1, -⟩ ⟨#H2, -⟩
  ihave %h := ghostMapElem_agree (dir, i) W.γdk _ _ (j, X) (j', X') $$ H1 H2
  ipureintro
  simpa only [Prod.mk.injEq] using h

end iris

end WalFs
end EtcdGrove
end Perennial

end
