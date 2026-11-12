/-
`tx.write()`'s pages (U10c, `notes/bbolt-proof-plan.md`): a dirty page `e = (id, buffer, bytes)`
while it waits (`pgRest`: the bytes after its header, its slots holding anything) and once written
(`pgDone`: its slots holding its chunks); a page's buffer as its header and the rest
(`page_split`), taken from the dirty pages' resources per key (`wr_entry`); a chunk of the buffer
as `WriteAt`'s slice (`chunk_acc`); the client halves of a range of the one mapping as `WriteAt`
takes them (`mcells_single`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteRun
public import Proof.go_etcd_io.bbolt.Read.Bytes

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- A dirty page `e = (id, buffer, bytes)` waiting to be written: its bytes after the header,
its slots holding anything. -/
def pgRest (b : Loc) (p : GoString) (e : w64 × Loc × List w8) : IProp GF :=
  iprop(⌜0 < e.2.1.addr⌝ ∗ bytesPointsto (e.2.1 +ₗ 16) (DFrac.own 1) (e.2.2.drop 16) ∗
    [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2), slotAny b p s)

/-- A dirty page written: its bytes after the header, its slots holding its chunks. -/
def pgDone (b : Loc) (p : GoString) (e : w64 × Loc × List w8) : IProp GF :=
  iprop(⌜0 < e.2.1.addr⌝ ∗ bytesPointsto (e.2.1 +ₗ 16) (DFrac.own 1) (e.2.2.drop 16) ∗
    [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
      slotDone b p s (pageChunk e.2.2 (s - e.1.toNat)))

theorem pageHdr_encode (bs : List w8) (h : 16 ≤ bs.length) :
    encode (pageHdr bs) ++ bs.drop 16 = bs := by
  have h16 : (bs.take 16).length = 16 := by simp only [List.length_take]; omega
  unfold pageHdr bytesAt
  rw [List.drop_zero, ByteEncoding.encode_decode _ h16, List.take_append_drop]

/-- **A page's buffer is its header and the rest.** -/
theorem page_split (l : Loc) (bs : List w8) (h : 16 ≤ bs.length) (hp : 0 < l.addr) :
    bytesPointsto (GF := GF) l (DFrac.own 1) bs ⊣⊢
      l ↦ pageHdr bs ∗ bytesPointsto (l +ₗ 16) (DFrac.own 1) (bs.drop 16) := by
  have e := Spill.pageBuf_split (GF := GF) l (DFrac.own 1) (pageHdr bs) (bs.drop 16) hp
  rw [pageHdr_encode bs h] at e
  exact e

/-- **A dirty page, per key**: its buffer's header and the rest, its slots. -/
theorem wr_entry (b : Loc) (p : GoString) (pm : GMap w64 Loc) (bufs : GMap w64 (List w8))
    (lim : Nat) (hok : bufsOK bufs lim) (key : w64) (v : Loc) (hv : pm !! key = some v) :
    (∃ pl, ⌜pm !! key = some pl⌝ ∗ ∃ bs, ⌜bufs !! key = some bs⌝ ∗
        bytesPointsto (GF := GF) pl (DFrac.own 1) bs) ∗
      (∃ pg, ⌜bufs !! key = some pg⌝ ∗
        [∗list] s ∈ List.range' key.toNat (1 + pageOverflow pg), slotAny (GF := GF) b p s) ⊢
    ∃ bs, ⌜bufs !! key = some bs⌝ ∗ v ↦ pageHdr bs ∗ pgRest b p (key, v, bs) := by
  iintro ⟨⟨%pl, %hpl, %bs, %hbs, Hb⟩, ⟨%pg, %hpg, Hs⟩⟩
  rw [hv] at hpl; cases hpl
  rw [hbs] at hpg; cases hpg
  have hl := (hok key bs hbs).2.1
  have hne : bs ≠ [] := List.ne_nil_of_length_pos (by omega)
  icases persistent_entails_left (bytesPointsto_pos _ _ _ hne) $$ Hb with ⟨Hb, %Hp⟩
  icases (page_split v bs (by omega) Hp).1 $$ Hb with ⟨Hh, Hr⟩
  iexists bs
  isplitr
  · ipureintro; exact hbs
  iframe Hh
  unfold pgRest
  iframe
  ipureintro; exact Hp


/-- **A waiting page, with its header, for its write**: its whole buffer, and its slots as one
run. -/
theorem rest_run (b : Loc) (p : GoString) (e : w64 × Loc × List w8) (h16 : 16 ≤ e.2.2.length) :
    e.2.1 ↦ pageHdr e.2.2 ∗ pgRest (GF := GF) b p e ⊢
      ⌜0 < e.2.1.addr⌝ ∗ bytesPointsto e.2.1 (DFrac.own 1) e.2.2 ∗
        oAny p (4096 * e.1.toNat) (4096 * (1 + pageOverflow e.2.2)) ∗
        cAny b (4096 * e.1.toNat) (4096 * (1 + pageOverflow e.2.2)) := by
  unfold pgRest
  iintro ⟨Hh, %Hp, Hr, Hs⟩
  isplitr
  · ipureintro; exact Hp
  isplitl [Hh Hr]
  · iapply (page_split e.2.1 e.2.2 h16 Hp).2; iframe
  iapply (slotsAny_run b p _ _).1; iexact Hs

/-- **A written page**: its header back, and its slots each holding its chunk. -/
theorem run_pgDone (b : Loc) (p : GoString) (e : w64 × Loc × List w8) (ys : List ByteG)
    (hy : ys.map Prod.fst = e.2.2) (hl : e.2.2.length = 4096 * (1 + pageOverflow e.2.2))
    (hp : 0 < e.2.1.addr) :
    bytesPointsto (GF := GF) e.2.1 (DFrac.own 1) e.2.2 ∗
      osBytes p.ino (4096 * e.1.toNat) (DFrac.own 1) ys ∗
      bytesPointsto (b +ₗ ((4096 * e.1.toNat : Nat) : Int)) (DFrac.own (1 : Qp).half) e.2.2 ⊢
      e.2.1 ↦ pageHdr e.2.2 ∗ pgDone b p e := by
  iintro ⟨Hb, Hy, Hc⟩
  icases (page_split e.2.1 e.2.2 (by omega) hp).1 $$ Hb with ⟨Hh, Hr⟩
  iframe Hh
  unfold pgDone
  isplitr
  · ipureintro; exact hp
  iframe Hr
  iapply run_done b p _ _ e.2.2 ys hy hl
  iframe

/-- A written page's slots, holding anything. -/
theorem pgDone_any (b : Loc) (p : GoString) (e : w64 × Loc × List w8)
    (hl : e.2.2.length = 4096 * (1 + pageOverflow e.2.2)) :
    pgDone (GF := GF) b p e ⊢
      [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2), slotAny b p s := by
  unfold pgDone
  iintro ⟨-, -, H⟩
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro i s hs
  have hm := List.mem_range'_1.1 (List.mem_of_getElem? hs)
  exact slotDone_any b p s _ (pageChunk_length _ _ _ hl (by omega))

/-- A waiting page's slots. -/
theorem pgRest_any (b : Loc) (p : GoString) (e : w64 × Loc × List w8) :
    pgRest (GF := GF) b p e ⊢
      [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2), slotAny b p s := by
  unfold pgRest
  iintro ⟨-, -, H⟩
  iexact H

/-- **On an error at the page `j`**: the written pages, the page `j`'s slots and the waiting
pages are every page's slots. -/
theorem err_assemble (b : Loc) (p : GoString) (L : List (w64 × Loc × List w8)) (j : Nat)
    (c : w64 × Loc × List w8) (hc : L[j]? = some c)
    (hl : ∀ e ∈ L, e.2.2.length = 4096 * (1 + pageOverflow e.2.2)) :
    ([∗list] e ∈ L.take j, pgDone (GF := GF) b p e) ∗
      ([∗list] s ∈ List.range' c.1.toNat (1 + pageOverflow c.2.2), slotAny b p s) ∗
      ([∗list] e ∈ L.drop (j + 1), pgRest b p e) ⊢
      [∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotAny b p s := by
  have hj : j < L.length := (List.getElem?_eq_some_iff.1 hc).1
  have hd : L.drop j = c :: L.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj]
    rw [List.getElem?_eq_getElem hj] at hc
    rw [Option.some.inj hc]
  iintro ⟨Hd, Hc, Hr⟩
  iapply (BigSepL.bigSepL_take_drop (n := j)).2
  isplitl [Hd]
  · iapply BigSepL.bigSepL_mono ?_ $$ Hd
    intro i e he
    exact pgDone_any b p e (hl e (List.mem_of_mem_take (List.mem_of_getElem? he)))
  rw [hd]
  iapply BigSepL.bigSepL_cons.2
  iframe Hc
  iapply BigSepL.bigSepL_mono ?_ $$ Hr
  intro i e he
  exact pgRest_any b p e

/-- **A chunk of a buffer as a slice**, and back. -/
theorem chunk_acc (pl : Loc) (bs : List w8) (w sz : Nat) (h : w + sz ≤ bs.length) (hsz : 0 < sz)
    (hlen : sz < 2 ^ 63) :
    bytesPointsto (GF := GF) pl (DFrac.own 1) bs ⊢
      slice.mk (pl +ₗ (w : Int)) (W64 (sz : Int)) (W64 (sz : Int)) ↦* bytesAt bs w sz ∗
      (slice.mk (pl +ₗ (w : Int)) (W64 (sz : Int)) (W64 (sz : Int)) ↦* bytesAt bs w sz -∗
        bytesPointsto pl (DFrac.own 1) bs) := by
  have hcl : (bytesAt bs w sz).length = sz := by
    unfold bytesAt; simp only [List.length_take, List.length_drop]; omega
  have hcne : bytesAt bs w sz ≠ [] := List.ne_nil_of_length_pos (by omega)
  iintro H
  icases Read.bytesPointsto_sub_acc pl (DFrac.own 1) bs (bytesAt bs w sz) w (by omega)
    (by rw [hcl]) $$ H with ⟨Hc, Hback⟩
  icases persistent_entails_left (bytesPointsto_pos _ _ _ hcne) $$ Hc with ⟨Hc, %Hp⟩
  have e := Read.bytesPointsto_ownSlice (GF := GF) (pl +ₗ (w : Int)) (DFrac.own 1) _ Hp
    (by rw [hcl]; exact hlen)
  rw [hcl] at e
  isplitl [Hc]
  · iapply e.1; iexact Hc
  iintro Hc
  iapply Hback
  iapply e.2; iexact Hc

/-- **The client halves of a range of the one mapping**, as `WriteAt` takes and gives them. -/
theorem mcells_single (b : Loc) (l lo n : Nat) (h : lo + n ≤ l) :
    mcellsAny (GF := GF) {[b := l]} lo (lo + n) ⊣⊢ cAny b lo n := by
  unfold mcellsAny cAny
  refine BigSepM.bigSepM_singleton.trans ?_
  rw [show min lo l = lo by omega, show min (lo + n) l - lo = n by omega]
  exact .rfl

end res

end bbolt
end EtcdGrove
end Perennial
