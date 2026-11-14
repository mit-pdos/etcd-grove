/- Lean-first (no Rocq counterpart).

# The crash boot's WALs found, pure (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log", (b))

`walBootCrash` builds `walInv_alloc`'s claim list from the WALs present in the crashed tree: each name of
the area `jr` that is a WAL name holding a directory (`bootWals m jr`, with the directory). In a well-formed
tree (`TreeWf`, which `crashRest_treeWf` gives the crashed one) the directories are distinct
(`bootWals_inj`, unique naming), none is the area's (`bootWals_ne_root`: an entry never names a root), and
each name is valid (`bootWals_nameOk`): what `hdirs1`, `hJm`, `hnames` and `hnok` need.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrashPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

open Classical in
/-- **The WALs the crash boot finds**: each WAL name of the area `jr` holding a directory, with it. -/
def bootWals (m : Tree) (jr : Ino) : List (GoString × Ino) :=
  (GMap.toList (entsOf m jr)).filterMap (fun an => match an.2 with
    | .dir J => if walNameOk an.1 then some (an.1, J) else none
    | .file _ => none)

theorem mem_bootWals {m : Tree} {jr : Ino} {nm : GoString} {J : Ino} :
    (nm, J) ∈ bootWals m jr ↔ walNameOk nm ∧ m.entry jr nm = some (.dir J) := by
  unfold bootWals
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, n⟩, hm, hf⟩
    have he := (GMap.mem_toList _ _ _).1 hm
    rw [entsOf_lookup] at he
    cases n with
    | dir J' =>
      simp only at hf
      split at hf
      · next hw => cases hf; exact ⟨hw, he⟩
      · cases hf
    | file _ => simp at hf
  · rintro ⟨hw, he⟩
    refine ⟨(nm, .dir J), (GMap.mem_toList _ _ _).2 (by rw [entsOf_lookup]; exact he), ?_⟩
    simp only
    rw [if_pos hw]

open Classical in
omit [GooseExts] in
theorem bootWals_f_some {an : GoString × Node} {p : GoString × Ino}
    (h : (match an.2 with
      | .dir J => if walNameOk an.1 then some (an.1, J) else none
      | .file _ => none) = some p) : an = (p.1, .dir p.2) := by
  obtain ⟨a, n⟩ := an
  cases n with
  | dir J =>
    simp only at h
    split at h
    · cases h; rfl
    · cases h
  | file _ => simp at h

/-- The WALs found are distinct. -/
theorem bootWals_nodup (m : Tree) (jr : Ino) : (bootWals m jr).Nodup := by
  unfold bootWals
  refine nodup_filterMap_of (toList_nodup _) (fun a _ a' _ p h h' => ?_)
  rw [bootWals_f_some h, bootWals_f_some h']

/-- A name finds one directory. -/
theorem bootWals_fun {m : Tree} {jr : Ino} {nm : GoString} {J J' : Ino}
    (h : (nm, J) ∈ bootWals m jr) (h' : (nm, J') ∈ bootWals m jr) : J = J' := by
  have e := (mem_bootWals.1 h).2
  rw [(mem_bootWals.1 h').2] at e
  cases e; rfl

/-- **Two WALs found have distinct directories** (unique naming). -/
theorem bootWals_inj {m : Tree} {jr : Ino} (hu : UniqNames m) {nm nm' : GoString} {J : Ino}
    (h : (nm, J) ∈ bootWals m jr) (h' : (nm', J) ∈ bootWals m jr) : nm = nm' :=
  (hu _ _ _ _ _ (mem_bootWals.1 h).2 (mem_bootWals.1 h').2).2

/-- **A WAL found is not the area's directory** (no entry names a root's directory). -/
theorem bootWals_ne_root {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) {nm : GoString} {J : Ino} (h : (nm, J) ∈ bootWals m jr) : J ≠ jr := by
  rintro rfl
  exact hw.2.2.2.1 _ _ _ (mem_bootWals.1 h).2 r hr

/-- A WAL found has a valid name. -/
theorem bootWals_nameOk {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {jr : Ino}
    {nm : GoString} {J : Ino} (h : (nm, J) ∈ bootWals m jr) : NameOk nm :=
  (hw.2.2.1 _ _ _ (mem_bootWals.1 h).2).1

/-- A WAL found's directory is one of the tree's. -/
theorem bootWals_mem {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {jr : Ino}
    {nm : GoString} {J : Ino} (h : (nm, J) ∈ bootWals m jr) : J ∈ m :=
  (hw.2.2.1 _ _ _ (mem_bootWals.1 h).2).2 J (List.mem_singleton_self _)

end pure

end WalFs
end EtcdGrove
end Perennial

end
