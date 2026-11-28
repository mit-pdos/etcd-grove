-- The copy for the part `Dsverify/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/Inv.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: the invariant's laws (W4c U2, `notes/wal-fsext-w4c-plan.md`)

* `DurOk.curIs`, `DurPhys.curIs_unique`: the state's `cur` is what the name holds under the physical
  state (the candidates at distinct inodes).
* `durInv_open`: the invariant opened with the generation's `notCrashed` (its crash branch excluded).
* `durInv_okAt`: the facts of the handle's physical state, read off the invariant at a step.
* `durInv_readAU`: a read's update committed at a step, the state's `cur` what the name holds.
-/
module

public import Dsverify.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace DurFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

/-! ## Pure facts -/

theorem DurOk.curIs {f : DFile} {s : DurSt} {p : DurPhys} (h : DurOk f s p) : p.CurIs f s.cur := by
  have hc := h.cur
  unfold DurPhys.CurIs
  cases hs : s.cur with
  | none =>
    rw [hs] at hc
    simp only at hc
    rw [hc]
  | some v =>
    rw [hs] at hc
    obtain ⟨c, hc, hv, he⟩ := hc
    rw [he]
    exact ⟨c, hc, rfl, by rw [hv]⟩

theorem nodup_map_inj {α β : Type} {g : α → β} :
    ∀ {l : List α}, (l.map g).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → g x = g y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨ha, h⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx <;> rcases List.mem_cons.1 hy with rfl | hy
    · rfl
    · exact absurd (by rw [he]; exact List.mem_map_of_mem hy) ha
    · exact absurd (by rw [← he]; exact List.mem_map_of_mem ‹x ∈ l›) ha
    · exact nodup_map_inj h hx hy he

theorem DurPhys.curIs_unique {f : DFile} {p : DurPhys} {v v' : Option GoString}
    (hinj : (p.cands.map DCand.i).Nodup) (h : p.CurIs f v) (h' : p.CurIs f v') : v = v' := by
  unfold DurPhys.CurIs at h h'
  cases hx : p.hb.cur !! f.b with
  | none =>
    rw [hx] at h h'
    simp only at h h'
    rw [h, h']
  | some n =>
    rw [hx] at h h'
    cases n with
    | file i =>
      simp only at h h'
      obtain ⟨c, hc, hci, rfl⟩ := h
      obtain ⟨c', hc', hci', rfl⟩ := h'
      have : c = c' := nodup_map_inj hinj hc hc' (hci.trans hci'.symm)
      rw [this]
    | dir J => simp only at h

theorem durAuMask_sub : durAuMask ⊆ (⊤ : CoPset) \ ↑durN := by
  intro x hx
  unfold durAuMask at hx
  obtain ⟨-, hn⟩ := LawfulSet.mem_diff.1 hx
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, hn⟩

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem durPhys_agree (γ : DurGS) (p p' : DurPhys) :
    ⊢ durPhys (GF := GF) γ p -∗ durPhys γ p' -∗ ⌜p = p'⌝ := by
  unfold durPhys
  exact ghostVar_agree γ.γp p _ p' _

theorem durSt_agree (γ : DurGS) (s s' : DurSt) :
    ⊢ durSt (GF := GF) γ s -∗ ghostVar γ.γs (1 : Qp).half s' -∗ ⌜s = s'⌝ := by
  unfold durSt
  exact ghostVar_agree γ.γs s _ s' _

instance osBytes_timeless' (i : Ino) (off : Nat) (dq : DFrac) (xs : List ByteG) :
    Timeless (osBytes (L := L) i off dq xs) := by
  unfold osBytes bytesG; infer_instance

instance durInvBody_timeless (γ : DurGS) (f : DFile) : Timeless (durInvBody (L := L) γ f) := by
  unfold durInvBody durPhys candRes; infer_instance

theorem curRes_file (f : DFile) (p : DurPhys) (i : Ino) (hx : p.hb.cur !! f.b = some (.file i)) :
    curRes (L := L) f p ⊣⊢
      ∃ c : DCand, ⌜c ∈ p.cands ∧ c.i = i⌝ ∗ candRes (L := L) c (DFrac.own (1 : Qp).half) := by
  unfold curRes; rw [hx]; exact .rfl

theorem curRes_none (f : DFile) (p : DurPhys) (hx : p.hb.cur !! f.b = none) :
    curRes (L := L) f p ⊣⊢ emp := by
  unfold curRes; rw [hx]; exact .rfl

/-- **The invariant opened** at a step (`notCrashed`). -/
theorem durInv_open (γ : DurGS) (f : DFile) (E : CoPset) (hE : ↑durN ⊆ E) :
    ⊢ durInv (L := L) γ f -∗ notCrashed (hC := L.goose_crashGS) ={E, E \ ↑durN}=∗
      durInvBody (L := L) γ f ∗ notCrashed (hC := L.goose_crashGS) ∗
      (durInvBody (L := L) γ f ={E \ ↑durN, E}=∗ True) := by
  iintro #Hinv Hnc
  unfold durInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hb | ⟨>Hc, -⟩)
  · imodintro
    iframe Hb Hnc
    iintro Hb
    iapply Hclose
    inext; ileft; iexact Hb
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **The handle's physical state's facts**, read off the invariant at a step. -/
theorem durInv_okAt (γ : DurGS) (f : DFile) (p : DurPhys) :
    ⊢ durInv (L := L) γ f -∗ notCrashed (hC := L.goose_crashGS) -∗ durPhys γ p ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ durPhys γ p ∗ ⌜∃ s, DurOk f s p⌝ := by
  iintro #Hinv Hnc Hp
  imod durInv_open γ f ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  unfold durInvBody
  icases Hb with ⟨%s, %p', Hs, Hp', Hn1, Hn2, Hlb, Hc, %hok⟩
  icases durPhys_agree γ p p' $$ Hp Hp' with %he
  subst he
  imod Hcl $$ [Hs Hp' Hn1 Hn2 Hlb Hc] with -
  · iexists s, p; iframe; ipureintro; exact hok
  imodintro
  iframe
  ipureintro; exact ⟨s, hok⟩

/-- **A read's update committed** at a step: the state `s` the client's half names, whose `cur` is
what the name holds under the handle's physical state (`CurIs`). -/
theorem durInv_readAU (γ : DurGS) (f : DFile) (p : DurPhys) (v : Option GoString)
    (Q : DurSt → IProp GF) (hv : p.CurIs f v) :
    ⊢ durInv (L := L) γ f -∗ notCrashed (hC := L.goose_crashGS) -∗ durPhys γ p -∗
      (AU <{ ∃∃ s : DurSt, durSt γ s }> @ durAuMask, ∅ <{ durSt γ s, COMM Q s }>) ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ durPhys γ p ∗ ∃ s, ⌜s.cur = v⌝ ∗ Q s := by
  iintro #Hinv Hnc Hp Hau
  imod durInv_open γ f ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  unfold durInvBody
  icases Hb with ⟨%s, %p', Hs, Hp', Hn1, Hn2, Hlb, Hc, %hok⟩
  icases durPhys_agree γ p p' $$ Hp Hp' with %he
  subst he
  ihave Hau := atomic_update_mask_weaken durAuMask_sub $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%s', Hs', Hucl⟩
  icases durSt_agree γ s' s $$ Hs' Hs with %he
  subst he
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_nil, Std.Tele.app] at Hcommit
  imod Hcommit $$ Hs' with HQ
  imod Hcl $$ [Hs Hp' Hn1 Hn2 Hlb Hc] with -
  · iexists s', p; iframe; ipureintro; exact hok
  imodintro
  iframe Hnc Hp
  iexists s'
  iframe HQ
  ipureintro
  exact DurPhys.curIs_unique hok.inj hok.curIs hv

/-- `durInv_okAt` with the handle. -/
theorem durInv_okHandle (γ : DurGS) (f : DFile) (R : Roots) (p : DurPhys) :
    ⊢ durInv (L := L) γ f -∗ notCrashed (hC := L.goose_crashGS) -∗ durHandleP (L := L) γ f R p ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ durHandleP (L := L) γ f R p ∗ ⌜∃ s, DurOk f s p⌝ := by
  iintro #Hinv Hnc Hh
  unfold durHandleP
  icases Hh with ⟨%qd, Hp, Hh⟩
  imod durInv_okAt γ f p $$ Hinv Hnc Hp with ⟨Hnc, Hp, %hok⟩
  imodintro
  iframe Hnc
  isplitl [Hp Hh]
  · iexists qd; iframe
  ipureintro; exact hok

/-- `durInv_readAU` with the handle. -/
theorem durInv_readHandle (γ : DurGS) (f : DFile) (R : Roots) (p : DurPhys) (v : Option GoString)
    (Q : DurSt → IProp GF) (hv : p.CurIs f v) :
    ⊢ durInv (L := L) γ f -∗ notCrashed (hC := L.goose_crashGS) -∗ durHandleP (L := L) γ f R p -∗
      (AU <{ ∃∃ s : DurSt, durSt γ s }> @ durAuMask, ∅ <{ durSt γ s, COMM Q s }>) ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ durHandleP (L := L) γ f R p ∗ ∃ s, ⌜s.cur = v⌝ ∗ Q s := by
  iintro #Hinv Hnc Hh Hau
  unfold durHandleP
  icases Hh with ⟨%qd, Hp, Hh⟩
  imod durInv_readAU γ f p v Q hv $$ Hinv Hnc Hp Hau with ⟨Hnc, Hp, HQ⟩
  imodintro
  iframe Hnc HQ
  iexists qd; iframe

end iris

end DurFs
end EtcdGrove
end Perennial
