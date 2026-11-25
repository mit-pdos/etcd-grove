/- Lean-first (no Rocq counterpart).

# The writer's slots are not protected data (W1's link to the crash model)

A commit's dirty-page writes (`Tx.write`'s `pwrite`s, `commitFreelist`'s page) touch only the
writer's `W` slots but the synced freelist page's (`W \ X`, `X = flxS`: the slots the store keeps half
of while the page is the committed state's, `Inv/Locks.lean`'s `wBytesX`). `wSlot_unprot`: every byte
of such a slot is past the meta pages and no protected data byte of the committed state
(`protData`, `Crash/Good.lean`), as `bDur_write_idle` asks (`hun`).

Why: a `W` slot is at least 2, no tree slot and no pending slot (`wdbOK`). A tree page's extent is
tree slots (`coversSlot`). The synced freelist page `f`'s extent: `f` is not pending (its slots are
not among the freelist's ids, `flCurOK`), so its extent is `X` (`flxS`), whose overflow the writer's
bytes `wb` give; the reference image `xcur` has the same first page there (the file's bytes agree with
`wb` on `X`, the store's half, and with `xcur` on protected bytes, `PSync`).
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Dur
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Model.StoreFlOK

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs Spill
open go_etcd_io.bbolt.internal.common

section link
variable [GooseExts]

omit [GooseExts] in
theorem xb_some' (X : List w8) (b : Nat) (hb : b < X.length) : some (xb X b) = X[b]? := by
  show some (X.getD b 0) = _
  rw [List.getElem?_eq_getElem hb, getD_eq_getElem' _ _ _ hb]

/-- **The bytes of the writer's slots but the synced freelist page's are not protected**: with the
writer's facts (`wdbOK`), the idle facts of its committed state (`a.cur = w.C`), and the file's
page-cache bytes agreeing with the writer's on the slots of `X = flxS` (the store's half of them),
every byte `b` of a slot `s ∈ W \ X` is past the meta pages and no protected data byte. -/
theorem wSlot_unprot {a : BAbs} {st : CSt} {w : WDb} (hw : wdbOK w)
    (hI : IdleOk a.cur a.xcur st) (hC : a.cur = w.C)
    (hag : ∀ s ∈ flxS w.C w.fl w.wb, ∀ k < (w.wb s).length,
      (st.bs[4096 * s + k]?).map Prod.fst = (w.wb s)[k]?)
    (s : Nat) (hs : s ∈ w.W.filter (fun s => decide (s ∉ flxS w.C w.fl w.wb)))
    (b : Nat) (hb1 : 4096 * s ≤ b) (hb2 : b < 4096 * s + 4096) :
    8192 ≤ b ∧ ¬ protData a.xcur a.cur b := by
  obtain ⟨-, -, hhwm, hWi, -, hflc, -, -, -, -, -, -, -, -, hWlen, -⟩ := hw
  rw [List.mem_filter] at hs
  obtain ⟨hsW, hsX⟩ := hs
  have hsX' : s ∉ flxS w.C w.fl w.wb := by simpa using hsX
  obtain ⟨hs2, -, hsT, hsP⟩ := (hWi s).1 hsW
  rw [hC] at hI ⊢
  obtain ⟨hR, -, hdata, -, -, -⟩ := hI
  have hXl := hR.len
  refine ⟨by omega, ?_⟩
  rintro (⟨id, pg, hp, h1, h2⟩ | ⟨f, hf, h1, h2⟩)
  · -- a tree page's extent: tree slots
    obtain ⟨-, -, hl, -⟩ := refImg_page hR hp
    apply hsT
    rw [treeSlots, mem_pagesSlots_iff]
    rw [hl] at h2
    exact ⟨id, pg, hp, by omega, by omega⟩
  · -- the synced freelist page's extent: `X`
    obtain ⟨hf2, hfh, -, -, -, -, -, -, hext, -⟩ := hflc f hf f hf
    have hfin : f < f + (1 + pageOverflow (extentBytes w.wb f)) := by omega
    -- `f` is not pending
    have hfnp : f ∉ pendSlots w.fl := fun hp => (hext f (Nat.le_refl f) hfin).2
      (mem_allIds_of_pend w.fl f hp).1
    have hX : flxS w.C w.fl w.wb = flExt w.wb f := by
      unfold flxS; rw [hf]; exact if_neg hfnp
    -- `f` is a `W` slot inside the file, so its bytes are a page
    have hfW : f ∈ w.W := by
      refine (hWi f).2 ⟨hf2, ?_, ?_, hfnp⟩
      · omega
      · rw [treeSlots, mem_pagesSlots_iff]; exact (hext f (Nat.le_refl f) hfin).1
    have hfl : (w.wb f).length = 4096 := hWlen f hfW (by omega)
    -- the writer's page `f` is the reference image's
    have hfX : f ∈ flxS w.C w.fl w.wb := by
      rw [hX]; unfold flExt; rw [List.mem_range'_1]; omega
    have hpg : bytesAt a.xcur (4096 * f) 4096 = w.wb f := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < 4096
      · rw [bytesAt_getElem? _ _ _ _ hk, ← hag f hfX k (by omega)]
        have hps := (hdata (4096 * f + k) (.inr ⟨f, hf, by omega, by omega⟩)).1
        rw [hps, ← xb_some' a.xcur (4096 * f + k) (by omega)]
        rfl
      · rw [List.getElem?_eq_none (by simp [bytesAt]; omega), List.getElem?_eq_none (by omega)]
    have hov : pageOverflow (filePage a.xcur f) = pageOverflow (w.wb f) := by
      rw [cr_filePage_overflow, hpg]
    -- so `s` is a slot of `X`
    apply hsX'
    rw [hX]; unfold flExt; rw [List.mem_range'_1]
    rw [hov] at h2
    constructor <;> omega

end link

end bbolt
end EtcdGrove
end Perennial
