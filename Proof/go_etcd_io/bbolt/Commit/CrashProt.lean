/-
**The dirty pages' bytes are no protected data** (W1 of `plans/bbolt-crash-plan.md` §7, step 5;
Lean-first, no Rocq counterpart).

In crash mode a write may not touch a byte the crash invariant protects for the committed state `C`:
the extents of `C`'s tree pages and of its synced freelist page as the invariant's reference image
`X` (`a.xcur`) holds it (`protData X C`, `Crash/Good.lean`). `wp_bWriteAt` asks it through `bMetaP`.

* The tree pages: their slots are `C`'s `treeSlots`, which the writer's `W` slots avoid.
* The synced freelist page `f` (`C.flpg = some f`): its extent is `X`'s header's, and no slot of
  the writer's view knows `X`. But by the time `Commit` writes, `f` is pending (`flxS = []`), so the
  store holds its slot whole (`pagesInv`'s `osSlot f (σ.bytes f)`); the crash invariant's half of
  the file agrees with it (`csOwnIL_agree`), and `X` agrees with the file on `f`'s first page (its
  bytes are protected, `IdleOk`'s `PSync`): `X`'s extent is `flExt σ.bytes f`, all pending
  (`flxOK`), so none of it is a `W` slot.

`bMeta_prot` turns `bMeta` into `bMetaP P` for any `P` avoiding the tree's and the pending slots,
with the writer's ghost state (agreeing with `pagesInv`'s); `cm_file_accP` is `cm_file_acc` with it.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailAcc
public import Proof.go_etcd_io.bbolt.Inv.BFileWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem bytesAt_take16 (xs : List w8) (o n : Nat) (h : 16 ≤ n) :
    bytesAt (bytesAt xs o n) 0 16 = bytesAt xs o 16 := by
  unfold bytesAt
  rw [List.drop_zero, List.take_take, Nat.min_eq_left h]

/-- A file page's overflow is its first page's (the header). -/
theorem pageOverflow_filePage (X : List w8) (f : Nat) :
    pageOverflow (filePage X f) = pageOverflow (bytesAt X (4096 * f) 4096) := by
  unfold pageOverflow pageHdr filePage
  rw [bytesAt_take16 _ _ _ (by omega), bytesAt_take16 _ _ _ (by omega)]

/-- **A tree page's byte is in a tree slot.** -/
theorem protPg_slot {X : List w8} {C : CommitSt} (hR : RefImg X C) {k : Nat} (h : protPg C k) :
    k / 4096 ∈ treeSlots C := by
  obtain ⟨id, pg, hp, h1, h2⟩ := h
  obtain ⟨-, -, hl, -⟩ := refImg_page hR hp
  unfold treeSlots
  rw [mem_pagesSlots_iff]
  refine ⟨id, pg, hp, by omega, ?_⟩
  rw [hl] at h2
  have : k < 4096 * (id + (1 + pageOverflow pg)) := by rw [Nat.mul_add]; rw [Nat.mul_comm] at h2; omega
  omega

end pure

section prot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`bMeta` with the bytes `P` named** (see the file header): `P` avoids `C`'s tree slots and the
pending slots of `fl`, the synced freelist page (if any) is pending (`flxS = []`), the store is
mapped (`ms`), and the crash invariant's namespace is outside `pagesInv`'s. -/
theorem bMeta_prot (K : BC) (C : CommitSt) (fl : FLPg) (ms : MapSt) (m : OsMeta) (P : Nat → Prop)
    (hP : ∀ k, P k → k / 4096 ∉ treeSlots C ∧ k / 4096 ∉ pendSlots fl)
    (hX : ∀ wb : Nat → List w8, flxS C fl wb = []) (hms : ms ≠ none)
    (hN : ∀ c, K.p.cs = some c → (↑c.N : CoPset) ⊆ ⊤ \ ↑(pagesN K.N)) :
    K.core (GF := GF) ∗ bCsInv K.p ∗ ghostVar K.B.cur (1 : Qp).half.half C ∗
      ghostVar K.B.fl (1 : Qp).half fl ∗ ghostVar K.B.map (1 : Qp).half ms ∗ bMeta K.p C [] m
      ={⊤}=∗ ghostVar K.B.cur (1 : Qp).half.half C ∗ ghostVar K.B.fl (1 : Qp).half fl ∗
        ghostVar K.B.map (1 : Qp).half ms ∗ bMetaP P K.p C [] m := by
  iintro ⟨#Hcore, #Hci, Hcur, Hfl, Hmap, Hm⟩
  cases hc : K.p.cs with
  | none =>
    rw [bMeta_none hc, bMetaP_none hc]
    imodintro; iframe
  | some c =>
    ihave #Hci := bCsInv_some K.p c hc $$ Hci
    icases bMeta_own K.p c hc C [] m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, hlh⟩ := Hf
    imod csOwnIL_ok c.N K.p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hci Hown with ⟨Hown, %Hok⟩
    have hD : BDur a ⟨m, bs, 0, 0, .idle⟩ := Hok.1 hfs
    obtain ⟨hW0, hI⟩ := (bDur_idle_iff hph).1 hD
    obtain ⟨hR, -, hPS, hlo, -⟩ := hI
    rw [hcur] at hR hPS hlo
    have hbl : bs.length = m.size := hW0.1
    have hlosz : m.lo ≤ m.size := hW0.2.2.1
    simp only at hlo
    -- the protected bytes avoid `P`, given the freelist page's extent's
    have hfin : ∀ (hfl : ∀ f, C.flpg = some f → ∀ k, protFl a.xcur C k → k / 4096 ∈ pendSlots fl),
        ∀ k, protData a.xcur a.cur k → ¬ P k := by
      intro hfl k hk hPk
      rw [hcur] at hk
      rcases hk with hk | ⟨f, hf, h1, h2⟩
      · exact (hP k hPk).1 (protPg_slot hR hk)
      · exact (hP k hPk).2 (hfl f hf k ⟨f, hf, h1, h2⟩)
    rcases hflpg : C.flpg with _ | f
    · -- no synced freelist page
      imodintro
      iframe Hcur Hfl Hmap
      iapply bMetaP_of_own P K.p c hc C [] m bs a ⟨hph, hcur, hdur, hfs, hlh⟩
        (hfin (fun f hf => by rw [hflpg] at hf; cases hf)) $$ [Hown Ha]
      iframe
    · -- the synced freelist page `f`, pending
      have hfp : f ∈ pendSlots fl := by
        have h := hX (fun _ => [])
        unfold flxS at h
        rw [hflpg] at h
        dsimp only at h
        by_cases hm : f ∈ pendSlots fl
        · exact hm
        · rw [if_neg hm] at h; unfold flExt at h; simp at h
      -- `f`'s extent in the reference image, inside the high-water mark
      obtain ⟨hf2, hfh, -⟩ := hR.fl f hflpg
      have hXl : C.hwm * 4096 ≤ a.xcur.length := hR.len
      have hfm : 4096 * f + 4096 ≤ bs.length := by
        have := Nat.mul_le_mul_left 4096 hfh
        rw [hbl]; rw [Nat.mul_comm C.hwm 4096] at hlo; rw [Nat.mul_add, Nat.mul_add] at this
        omega
      -- the store's bytes of `f`
      ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
      · unfold BC.core; iexact Hcore
      unfold isBoltCoreP
      icases Hcore' with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
      have : Timeless (pagesInv (GF := GF) K.B K.p) := by
        have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
          intro σ; unfold storeCells; split <;> infer_instance
        have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) K.B σ) := by
          intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
        have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) K.B σ W) := by
          intro σ W; unfold bytesWit; split <;> infer_instance
        unfold pagesInv
        infer_instance
      imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hpi with ⟨Hp, Hclose⟩
      icases Hp with >Hp
      unfold pagesInv
      icases Hp with ⟨%σ, %Wb, Hcur', Hfl', Hmap', Hwv', Hrds, Hrk, Hsc, Hso, Hbw, Hml, %Hsok, %Hfx⟩
      icombine Hcur Hcur' gives %e1
      icombine Hfl Hfl' gives %e2
      icombine Hmap Hmap' gives %e3
      have hσC : σ.C = C := e1.2.symm
      have hσfl : σ.fl = fl := e2.2.symm
      have hσms : σ.ms = ms := e3.2.symm
      icases slotsOs_open_m K.B K.p _ _ _ _ _ (by rw [hσms]; exact hms) $$ Hso with ⟨Hcls, Hss, Hsx⟩
      have hfS : f ∈ storeSlots σ := by
        unfold storeSlots
        rw [mem_list_dedup, hσfl]
        exact List.mem_append_right _ hfp
      have hfl4 : (σ.bytes f).length = 4096 :=
        (Hsok.2.2.2.2.2.2.2.2.2.2.2.1 f hfS).2
      icases BigSepL.bigSepL_mem_acc hfS $$ Hss with ⟨Hfs, Hssb⟩
      iunfold osSlot at Hfs
      icases Hfs with ⟨%xs, Hxs, %hxs⟩
      have hxl : xs.length = 4096 := by rw [← hfl4, ← hxs, List.length_map]
      icases (bBytes_os K.p (4096 * f) (DFrac.own 1) xs).1 $$ Hxs with ⟨Hxo, Hxg⟩
      have hdq : K.p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by
        unfold BFile.dq; rw [hc]; rfl
      rw [hdq]
      imod csOwnIL_agree c.N K.p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a (⊤ \ ↑(pagesN K.N))
        (hN c hc) (4096 * f) (DFrac.own (1 : Qp).half) xs (by show _ ≤ bs.length; omega)
        $$ Hci Hown Hxo with ⟨Hown, Hxo, %hag⟩
      -- the store's bytes back
      ihave Hfs : osSlot K.p f (σ.bytes f) $$ [Hxo Hxg]
      · unfold osSlot; iexists xs
        isplitl
        · iapply (bBytes_os K.p (4096 * f) (DFrac.own 1) xs).2; rw [hdq]; iframe
        ipureintro; exact hxs
      ihave Hss := Hssb $$ Hfs
      imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hrk Hsc Hcls Hss Hsx Hbw Hml] with -
      · inext
        iexists σ, Wb
        iframe
        isplitl
        · iapply slotsOs_intro; unfold slotsOsO; iframe
        ipureintro; exact ⟨Hsok, Hfx⟩
      -- the reference image's first page of `f` is the store's
      have hpage : σ.bytes f = bytesAt a.xcur (4096 * f) 4096 := by
        apply List.ext_getElem?
        intro j
        rw [← hxs, List.getElem?_map]
        by_cases hj : j < 4096
        · have hb : protFl a.xcur C (4096 * f + j) := ⟨f, hflpg, by omega, by
            rw [Nat.mul_add, Nat.mul_add]; omega⟩
          have hps := (hPS (4096 * f + j) (Or.inr hb)).1
          simp only at hps
          have hx : xs[j]? = bs[4096 * f + j]? := by
            rw [hag, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
          rw [hx, hps]
          unfold bytesAt
          rw [List.getElem?_take, if_pos hj, List.getElem?_drop]
          simp only [Option.map_some, durB, xb]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          rfl
        · rw [List.getElem?_eq_none (by omega)]
          unfold bytesAt
          rw [List.getElem?_take, if_neg hj]
          rfl
      have hext : ∀ k, protFl a.xcur C k → k / 4096 ∈ pendSlots fl := by
        intro k hk
        obtain ⟨f', hf', h1, h2⟩ := hk
        rw [hflpg] at hf'
        cases hf'
        rw [pageOverflow_filePage, ← hpage] at h2
        have hsx : k / 4096 ∈ flExt σ.bytes f := by
          unfold flExt
          exact List.mem_range'_1.2 ⟨by omega, by rw [Nat.mul_add, Nat.mul_add] at h2; omega⟩
        have := ((Hfx.1 f (by rw [hσC]; exact hflpg)).2.1 _ hsx).2.2.1
        rw [hσfl] at this
        exact this.2 hfp
      imodintro
      iframe Hcur Hfl Hmap
      iapply bMetaP_of_own P K.p c hc C [] m bs a ⟨hph, hcur, hdur, hfs, hlh⟩
        (hfin (fun f' hf' => by rw [hflpg] at hf'; cases hf'; exact hext)) $$ [Hown Ha]
      iframe

/-- **`cm_file_acc` with the dirty bytes named** (see the file header). -/
theorem cm_file_accP (K : BC) (tx : Loc) (ws : WSt) (w : WDb)
    (hX : ∀ wb : Nat → List w8, flxS w.C w.fl wb = []) (P : Nat → Prop)
    (hP : ∀ k, P k → k / 4096 ∉ treeSlots w.C ∧ k / 4096 ∉ pendSlots w.fl) (hms : w.ms ≠ none)
    (hN : ∀ c, K.p.cs = some c → (↑c.N : CoPset) ⊆ ⊤ \ ↑(pagesN K.N)) :
    K.core (GF := GF) ∗ bCsInv K.p ∗ wdbLive K.B K.db K.p K.sp K.t0 tx ws w ={⊤}=∗
      K.db.[DB, go!"file"] ↦{DFrac.own (1 : Qp).half} w.f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f ∗
      fileOwn w.f w.fd K.p.path (DFrac.own (1 : Qp).half) ∗
      osFd w.fd (DFrac.own (1 : Qp).half) (dbFd K.p.ino) ∗
      bMetaP P K.p w.C [] w.m ∗ wCells w.ms w.W ∗ wBytes K.p w.W w.wb w.m.size ∗
      (∀ (m : OsMeta) (W : List Nat) (wb : Nat → List w8),
        K.db.[DB, go!"file"] ↦{DFrac.own (1 : Qp).half} w.f -∗
        (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
          methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f -∗
        fileOwn w.f w.fd K.p.path (DFrac.own (1 : Qp).half) -∗
        osFd w.fd (DFrac.own (1 : Qp).half) (dbFd K.p.ino) -∗
        bMeta K.p w.C [] m -∗ wCells w.ms W -∗ wBytes K.p W wb m.size -∗
        wdbLive K.B K.db K.p K.sp K.t0 tx ws (w.reslot m W wb)) := by
  unfold wdbLive wdbCoreG
  iintro ⟨#Hcore, #Hci, ⟨Hcur, Hfl, Hmap, Hout, Hwv, Hfli, Hopn, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf,
    Hom, Hfo, Hfd, Hmc, Hmb, Hwc, Hwb, Hjk⟩, Hflo, Hsp, Hrc⟩
  imod bMeta_prot K w.C w.fl w.ms w.m P hP hX hms hN $$ [Hcur Hfl Hmap Hom]
    with ⟨Hcur, Hfl, Hmap, Hom⟩
  · iframe; iframe #
  rw [hX w.wb] at *
  ihave Hwb := (wBytesX_nil K.p w.W w.wb w.m.size).1 $$ Hwb
  imodintro
  iframe Hfile Hwa Hfo Hfd Hom Hwc Hwb
  iintro %m %W %wb Hfile Hwa Hfo Hfd Hom Hwc Hwb
  ihave Hwb := (wBytesX_nil K.p W wb m.size).2 $$ Hwb
  simp only [WDb.reslot]
  rw [hX wb]
  iframe

end prot

end bbolt
end EtcdGrove
end Perennial
