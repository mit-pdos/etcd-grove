/- Lean-first (no Rocq counterpart). minibolt's crash invariant: `Good`, the database files a
crash may leave (`BootMinibolt`'s crash safety, `BootP1.lean`), and why `Open` and `BootMinibolt`'s
checks accept them.

A crash image `img` of the database file is `Good` (`goodImg`) if it is at most 1 GiB and:
* **short** (fewer than four pages), with no valid meta in a slot it holds whole: `Open` redoes
  `init`. The slot condition makes the property inductive: `init` writes over a short file, and
  a valid slot it left in place would survive its writes;
* **uninitialized** (four pages or more, neither meta valid): `Open` redoes `init`;
* **committed**: the meta pages are an open database's (`metaPagesOk`), the high water mark is
  inside the file, and the current meta's root page holds what `BootMinibolt` checks of it
  (`bootOk`: no value at transactions 0 and 1, `init`'s, and its txid at every later one), and
  it is in slot `txid % 2` (`curInSlot`), so that the next commit writes the other slot; its
  txid is at least 1 and below the high water mark (`txOk`).

`goodImg_fileOk` and `goodImg_freshTx` give `Open`'s precondition (`dbFresh`: `fileOk`, with all
bytes clean, as after a crash) and `BootMinibolt`'s first check (`bootOk` of `freshTx`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- What `BootMinibolt` checks of the transaction `t` and its root page's value `vo`: none at
`init`'s transactions (0 and 1), the txid at every later one. -/
def bootOk (t : Nat) (vo : Option w64) : Prop :=
  (t ≤ 1 ∧ vo = none) ∨ (1 < t ∧ vo = some (W64 t))

/-- The meta pages of `img`. -/
abbrev imgMetas (img : List w8) : List w8 := img.take 8192

/-- The current meta of the meta pages `mp` is in slot `txid % 2`, which the next commit (writing
slot `(txid + 1) % 2`) does not touch. -/
def curInSlot (mp : List w8) : Prop :=
  curMeta mp = fileMeta mp ((curMeta mp).txid'.toNat % 2)

/-- The current txid of the meta pages `mp` is at least 1 (`init` makes transaction 1 current
before any meta of txid 0 is valid) and below the high water mark (each commit adds one to
both), so that the next txid does not overflow. -/
def txOk (mp : List w8) : Prop :=
  1 ≤ (curMeta mp).txid'.toNat ∧ (curMeta mp).txid'.toNat < curPgid mp

/-- A crash image `img` of the database file that a boot accepts (see the file header). -/
def goodImg (img : List w8) : Prop :=
  img.length ≤ 2 ^ 30 ∧
  ((img.length < 4 * 4096 ∧ ∀ i < 2, 4096 * i + 80 ≤ img.length → ¬ metaValid (fileMeta img i)) ∨
   (4 * 4096 ≤ img.length ∧ ¬ metaValid (fileMeta (imgMetas img) 0) ∧
      ¬ metaValid (fileMeta (imgMetas img) 1)) ∨
   (4 * 4096 ≤ img.length ∧ metaPagesOk (imgMetas img) ∧
      4096 * curPgid (imgMetas img) ≤ img.length ∧
      bootOk (curMeta (imgMetas img)).txid'.toNat
        (pageVal ((img.drop (4096 * curRoot (imgMetas img))).take 4096)) ∧
      curInSlot (imgMetas img) ∧ txOk (imgMetas img)))

/-- **minibolt's crash invariant**: the database file is absent, or a `Good` image. -/
def Good : Option OsFile → Prop
  | none => True
  | some f => goodImg f.cur

theorem goodImg_fileOk (img : List w8) (h : goodImg img) :
    fileOk (img.map (·, true)) := by
  have hfst : (img.map (·, true)).map Prod.fst = img := by
    simp [List.map_map, Function.comp_def]
  have hcl : ∀ x ∈ img.map (·, true), x.2 = true := by simp
  obtain ⟨-, h | ⟨h4, h0, h1⟩ | ⟨h4, hok, hpg, -⟩⟩ := h
  · exact Or.inl (by simpa using h.1)
  · refine Or.inr ⟨hcl, ?_⟩
    simp only [hfst]
    exact Or.inl ⟨h0, h1⟩
  · refine Or.inr ⟨hcl, ?_⟩
    simp only [hfst, List.length_map]
    exact Or.inr ⟨hok, hpg⟩

theorem goodImg_freshTx (img : List w8) (h : goodImg img) :
    bootOk (freshTx (img.map (·, true))).1 (freshTx (img.map (·, true))).2.1 := by
  have hfst : (img.map (·, true)).map Prod.fst = img := by
    simp [List.map_map, Function.comp_def]
  unfold freshTx
  simp only [hfst, List.length_map]
  obtain ⟨-, h | ⟨h4, h0, h1⟩ | ⟨h4, hok, -, hb, -⟩⟩ := h
  · split
    · rename_i hc; exact absurd hc.1 (by omega)
    · exact Or.inl ⟨by omega, rfl⟩
  · split
    · rename_i hc; rcases hc.2 with hc | hc <;> contradiction
    · exact Or.inl ⟨by omega, rfl⟩
  · have hv := hok.2.1
    simp only [imgMetas] at hv hb
    simp only [h4, hv, and_self, ↓reduceIte]
    exact hb

end pure

end bboltfs
end EtcdGrove
end Perennial
