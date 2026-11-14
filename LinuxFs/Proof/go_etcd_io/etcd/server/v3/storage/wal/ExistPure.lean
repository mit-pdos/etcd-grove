/- Lean-first (no Rocq counterpart).

# `wal.Exist`'s pure facts (W12, `notes/wal-fsext-plan.md`)

* `extModel_of_walNameP`: a `.wal` name's extension (`filepath.Ext`) is `.wal`.
* `readDirOut_wal_ne`: `ReadDir(dir, WithExt(".wal"))`'s result is not empty when a `.wal` name was
  read.
* `existFalseOk_of_le`: `Exist`'s `false` arm (no WAL in the real state) for the client's lower bound.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove

open Fs WalFs

/-- The extension of `q ++ ".wal"` is `.wal`. -/
theorem extModel_append_wal (q : List w8) : filepath.extModel (q ++ go!".wal") = go!".wal" := by
  unfold filepath.extModel
  have hl : (q ++ go!".wal").length = q.length + 3 + 1 := by simp
  rw [hl]
  simp only [filepath.extFrom]
  simp [List.getD_eq_getElem?_getD, path.slash, path.dot]

/-- A `.wal` name's extension is `.wal`. -/
theorem extModel_of_walNameP {b : GoString} (hb : walNameP b = true) :
    filepath.extModel b = go!".wal" := by
  unfold walNameP at hb
  obtain ⟨q, rfl⟩ := of_decide_eq_true hb
  exact extModel_append_wal q

/-- A name outside `X` (which holds no `.wal` name) when it is a `.wal` name. -/
theorem except_mem_of_walNameP {X : List GoString} (hX : ∀ b ∈ X, walNameP b = false) {b : GoString}
    (hb : walNameP b = true) : (NameSet.except X).Mem b := fun hbX => by
  rw [hX b hbX] at hb; cases hb

/-- `ReadDir` with the option `WithExt(".wal")`, having read a `.wal` name, returns some name. -/
theorem readDirOut_wal_ne {names rs : List GoString} {b : GoString}
    (h : fileutil.ReadDirOut names (fileutil.optsExt [go!".wal"]) rs) (hb : b ∈ names)
    (hw : walNameP b = true) : rs ≠ [] := by
  obtain ⟨srt, hp, -, hrs⟩ := h
  have he : fileutil.optsExt [go!".wal"] = go!".wal" := rfl
  rw [he] at hrs
  have hne : (go!".wal" : GoString) ≠ "" := by simp [stringToGoString]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hne)] at hrs
  have hm : b ∈ rs := by
    rw [hrs, List.mem_filter]
    exact ⟨hp.mem_iff.1 hb, by simp [extModel_of_walNameP hw]⟩
  exact List.ne_nil_of_mem hm

/-- **`Exist`'s `false` arm**: the client's lower bound `o` below no WAL. -/
theorem existFalseOk_of_le {o od : Option WalDur} (h : walOptLe o od) (hod : od = none) :
    wal.ExistFalseOk o := by
  subst hod
  left
  cases o with
  | none => rfl
  | some d => exact absurd h (by simp [walOptLe])

/-- A `.wal` name. -/
theorem walNameP_ex : walNameP go!"a.wal" = true := by decide

end EtcdGrove
end Perennial

end
