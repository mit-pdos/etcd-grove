/-
`Tx.WriteTo`'s helpers (session S4): a reader's parts `WriteTo` reads (its `WriteFlag`, meta copy,
`db`, committed state, registration in the store, share of the file handle and mapping), out of
`rdTx` and back; the meta pages' buffer between iterations; the relation of the store's bytes a
reader's `pread`s see (`wtRs`), and the bridge from `io.CopyN`'s per-byte guarantee to
`writeTo_fileOK`'s slots.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Inv.WriteToImage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common
open Spill Read

section pure
variable [GooseExts]

/-- The meta `WriteTo` writes at slot `j` (`0`, `1`): the reader's at its txid's parity, the
decremented one at the other. -/
def wtM (mv : Meta) (j : Nat) : Meta := if mv.txid'.toNat % 2 = j then mv else metaDec mv

theorem wtMeta0_eq (mv : Meta) : wtMeta0 mv = metaBuf (wtM mv 0) := by
  unfold wtMeta0 wtM; split <;> rfl

theorem wtMeta1_eq (mv : Meta) : wtMeta1 mv = metaBuf (wtM mv 1) := by
  unfold wtMeta1 wtM
  by_cases h : mv.txid'.toNat % 2 = 0
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

/-- The header after `SetFlags(MetaPageFlag)` and `SetId(j)` is `metaBuf (wtM mv j)`'s. -/
theorem wtM_hdr (mv : Meta) (j : Nat) (hj : j < 2) (h1 : 1 ≤ mv.txid'.toNat) :
    ({ zeroHdr with flags' := W16 4, id' := W64 (j : Int) } : Page) = metaHdr (wtM mv j) := by
  have e : W64 (j : Int) = (wtM mv j).txid' % W64 2 := by
    apply BitVec.eq_of_toNat_eq
    unfold wtM
    by_cases h : mv.txid'.toNat % 2 = j
    · rw [if_pos h, BitVec.toNat_umod]; simp; omega
    · rw [if_neg h, BitVec.toNat_umod, metaDec_txid]
      simp only [BitVec.toNat_sub]
      simp; omega
  unfold metaHdr; rw [e]

/-- The page header `WriteTo` keeps in its buffer: the meta flag, the id `hid`. -/
def wtHdr (hid : w64) : Page := { zeroHdr with flags' := W16 4, id' := hid }

theorem wtHdr_eq (mv : Meta) (j : Nat) (hj : j < 2) (h1 : 1 ≤ mv.txid'.toNat) :
    wtHdr (W64 (j : Int)) = metaHdr (wtM mv j) := wtM_hdr mv j hj h1

/-- What `WriteTo` has written after `k` meta pages. -/
def wtPre (mv : Meta) (k : Nat) : List w8 :=
  if k = 0 then [] else if k = 1 then wtMeta0 mv else wtMetas mv

/-- The parity test of the loop. -/
theorem wtM_test (mv : Meta) (j : Nat) (hj : j < 2) :
    (mv.txid' % W64 2 = W64 (j : Int)) ↔ mv.txid'.toNat % 2 = j := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_umod] at this; simp at this; omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod]; simp; omega

/-- **The bytes a reader's `pread`s see exactly** (session S4): its view's pages at their file
offsets and its freelist page's bytes, as held byte ranges (`os.heldByte` reads only the bytes). -/
def wtRs (P : Pages) (fx : Option (Nat × List w8)) : List (Nat × DFrac × List ByteG) :=
  P.toList.map (fun ip => (4096 * ip.1, DFrac.own 1, ip.2.map (fun b => (b, ([] : Cands))))) ++
  (match fx with
   | some (f, bs) => [(4096 * f, DFrac.own 1, bs.map (fun b => (b, ([] : Cands))))]
   | none => [])

theorem wtRs_page (P : Pages) (fx : Option (Nat × List w8)) (id : Nat) (pg : List w8)
    (hp : P !! id = some pg) (j : Nat) (b : w8) (hb : pg[j]? = some b) :
    os.heldByte (wtRs P fx) (4096 * id + j) b := by
  refine ⟨(4096 * id, DFrac.own 1, pg.map (fun b => (b, ([] : Cands)))), ?_, by simp, ?_⟩
  · unfold wtRs
    apply List.mem_append_left
    rw [List.mem_map]
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, rfl⟩
  · simp [hb]

theorem wtRs_fx (P : Pages) (f : Nat) (bs : List w8) (j : Nat) (b : w8) (hb : bs[j]? = some b) :
    os.heldByte (wtRs P (some (f, bs))) (4096 * f + j) b := by
  refine ⟨(4096 * f, DFrac.own 1, bs.map (fun b => (b, ([] : Cands)))), ?_, by simp, ?_⟩
  · unfold wtRs; simp
  · simp [hb]

/-- Every byte `wtRs` holds is one the store's ranges `P`'s pages and the page `fx` give. -/
theorem wtRs_held (P : Pages) (fx : Option (Nat × List w8)) (rs : List (Nat × DFrac × List ByteG))
    (hP : ∀ id pg, P !! id = some pg → ∀ j b, pg[j]? = some b → os.heldByte rs (4096 * id + j) b)
    (hF : ∀ f bs, fx = some (f, bs) → ∀ j b, bs[j]? = some b → os.heldByte rs (4096 * f + j) b) :
    ∀ i b, os.heldByte (wtRs P fx) i b → os.heldByte rs i b := by
  rintro i b ⟨r, hr, hle, hb⟩
  unfold wtRs at hr
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨⟨id, pg⟩, hip, rfl⟩ := List.mem_map.1 hr
    simp only at hle hb
    have hp := (GMap.mem_toList _ _ _).1 hip
    have : pg[i - 4096 * id]? = some b := by
      rw [List.getElem?_map] at hb
      cases h : pg[i - 4096 * id]? <;> simp_all
    have := hP id pg hp _ _ this
    rwa [show 4096 * id + (i - 4096 * id) = i by omega] at this
  · rcases fx with _ | ⟨f, bs⟩
    · simp at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      simp only at hle hb
      have : bs[i - 4096 * f]? = some b := by
        rw [List.getElem?_map] at hb
        cases h : bs[i - 4096 * f]? <;> simp_all
      have := hF f bs rfl _ _ this
      rwa [show 4096 * f + (i - 4096 * f) = i by omega] at this

/-- A list given by its bytes at an offset of `xs`. -/
theorem bytesAt_of_get (xs pg : List w8) (o : Nat) (hl : o + pg.length ≤ xs.length)
    (h : ∀ j < pg.length, xs[o + j]? = pg[j]?) : bytesAt xs o pg.length = pg := by
  apply List.ext_getElem?
  intro j
  unfold bytesAt
  rw [List.getElem?_take, List.getElem?_drop]
  split
  · exact h j ‹_›
  · rw [List.getElem?_eq_none (by omega)]

/-- The slot function of `WriteTo`'s bytes: slot `s` of the metas' room followed by `ys`. -/
def wtG (ys : List w8) (s : Nat) : List w8 :=
  bytesAt (List.replicate 8192 (W8 0) ++ ys) (4096 * s) 4096

theorem wt_tree_page (C : CommitSt) (h : treeOK C) (id : Nat) (pg : List w8)
    (hp : C.pages !! id = some pg) :
    2 ≤ id ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧ id + (1 + pageOverflow pg) ≤ C.hwm := by
  have h4 := h.2.2.2.1 id pg hp
  obtain ⟨⟨hwf, -⟩, htp, -⟩ := h
  have hhas : treeHas C.pages C.root id := by
    rw [← htp] at hp
    rw [treePages_lookup] at hp
    split at hp
    · assumption
    · cases hp
  cases treeHas_treeWF C.pages C.hwm hhas hwf with
  | page _ pg' h2 _ hp' _ hl _ =>
    rw [hp] at hp'; cases hp'
    exact ⟨h2, hl, h4⟩

/-- **From `io.CopyN`'s per-byte guarantee to `writeTo_fileOK`'s slots** (session S4). -/
theorem wt_bridge (C : CommitSt) (fx : Option (Nat × List w8)) (ys : List w8)
    (htree : treeOK C) (hfx : fxOK C fx) (hlen : ys.length = (C.hwm - 2) * 4096)
    (hy : ∀ j x, ys[j]? = some x → ∀ b, os.heldByte (wtRs C.pages fx) (8192 + j) b → x = b) :
    pagesFromBytes (wtG ys) C.pages ∧
    (∀ s ∈ treeSlots C, ((wtG ys) s).length = 4096 ∧
      ∀ j < 4096, ys[4096 * s + j - 8192]? = ((wtG ys) s)[j]?) ∧
    (∀ f, C.flpg = some f →
      flPgOK C f (extentBytes' (wtG ys) f) ∧
      ∀ s, f ≤ s → s < f + (1 + pageOverflow ((wtG ys) f)) → ((wtG ys) s).length = 4096 ∧
        ∀ j < 4096, ys[4096 * s + j - 8192]? = ((wtG ys) s)[j]?) := by
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = List.replicate 8192 (W8 0) ++ ys := ⟨_, rfl⟩
  have hxl : xs.length = C.hwm * 4096 := by
    have : 2 ≤ C.hwm := by
      obtain ⟨⟨hwf, -⟩, -⟩ := htree
      cases hwf with
      | page _ _ h2 h3 _ _ _ _ => omega
    rw [hxs, List.length_append, List.length_replicate, hlen]; omega
  -- the held bytes: `xs` at file offset `i ≥ 8192` is `ys`'s
  have hget : ∀ i, 8192 ≤ i → xs[i]? = ys[i - 8192]? := by
    intro i hi
    rw [hxs, List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate]
  have hheld : ∀ i b, 8192 ≤ i → i < xs.length → os.heldByte (wtRs C.pages fx) i b →
      xs[i]? = some b := by
    intro i b hi hil hb
    rw [hget i hi]
    have hil' : i - 8192 < ys.length := by omega
    rw [List.getElem?_eq_getElem hil',
      hy _ _ (List.getElem?_eq_getElem hil') b (by rwa [show 8192 + (i - 8192) = i by omega])]
  -- a slot inside the high-water mark
  have hslot : ∀ s, 2 ≤ s → s < C.hwm → ((wtG ys) s).length = 4096 ∧
      ∀ j < 4096, ys[4096 * s + j - 8192]? = ((wtG ys) s)[j]? := by
    intro s h2 hs
    refine ⟨?_, fun j hj => ?_⟩
    · unfold wtG bytesAt; rw [← hxs, List.length_take, List.length_drop]; omega
    · unfold wtG bytesAt; rw [← hxs, List.getElem?_take, if_pos hj, List.getElem?_drop,
        hget _ (by omega)]
  -- an extent of held bytes
  have hext : ∀ id (pg : List w8), 2 ≤ id → pg.length = (1 + pageOverflow pg) * 4096 →
      id + (1 + pageOverflow pg) ≤ C.hwm →
      (∀ j b, pg[j]? = some b → os.heldByte (wtRs C.pages fx) (4096 * id + j) b) →
      (List.range' id (1 + pageOverflow pg)).flatMap (wtG ys) = pg ∧
        pageOverflow ((wtG ys) id) = pageOverflow pg := by
    intro id pg h2 hl hle hb
    have heq : bytesAt xs (4096 * id) pg.length = pg := by
      apply bytesAt_of_get _ _ _ (by rw [hxl]; omega)
      intro j hj
      rw [List.getElem?_eq_getElem hj, hheld _ _ (by omega) (by rw [hxl]; omega)
        (hb j _ (List.getElem?_eq_getElem hj))]
    have hfm : (List.range' id (1 + pageOverflow pg)).flatMap (wtG ys) = pg := by
      unfold wtG; rw [← hxs, ← wt_bytesAt_slots, ← hl]; exact heq
    refine ⟨hfm, ?_⟩
    have h16 : 16 ≤ pg.length := by rw [hl]; omega
    have : (wtG ys) id = bytesAt pg 0 4096 := by
      unfold wtG; rw [← hxs]
      conv => rhs; rw [← heq]
      unfold bytesAt; rw [List.drop_zero, List.take_take]; congr 1; rw [hl]; omega
    rw [this]
    unfold pageOverflow pageHdr bytesAt
    simp only [List.drop_zero, List.take_take]
    congr 3
  refine ⟨fun id pg hp => ?_, fun s hs => ?_, fun f hf => ?_⟩
  · obtain ⟨h2, hl, hle⟩ := wt_tree_page C htree id pg hp
    exact ((hext id pg h2 hl hle (fun j b hb => wtRs_page _ _ id pg hp j b hb)).1).symm
  · simp only [treeSlots, pagesSlots, List.mem_flatMap, List.mem_range'] at hs
    obtain ⟨⟨id, pg⟩, hip, j, hj, rfl⟩ := hs
    obtain ⟨h2, -, hle⟩ := wt_tree_page C htree id pg ((GMap.mem_toList _ _ _).1 hip)
    exact hslot _ (by omega) (by simp only at hj ⊢; omega)
  · unfold fxOK at hfx
    rw [hf] at hfx
    obtain ⟨bs, rfl, hok, hbl⟩ := hfx
    have h2 := hok.1
    have hle := hok.2.1
    obtain ⟨hfm, hov⟩ := hext f bs h2 (by rw [hbl]; omega) hle
      (fun j b hb => wtRs_fx _ f bs j b hb)
    refine ⟨?_, fun s h1 h3 => hslot s (by omega) (by rw [hov] at h3; omega)⟩
    unfold extentBytes'; rw [hov, hfm]; exact hok

end pure

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`WriteTo`'s page buffer** as its header, its meta and the rest. -/
theorem pageBuf_typed (l : Loc) (h : Page) (mm : Meta) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l (DFrac.own 1)
        (encode h ++ encode mm ++ List.replicate 4016 (W8 0)) ⊣⊢
      l ↦ h ∗ (l +ₗ 16) ↦ mm ∗ bytesPointsto (l +ₗ 80) (DFrac.own 1) (List.replicate 4016 (W8 0)) := by
  have hl16 : 0 < (l +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
  have e : l +ₗ ((16 : Nat) : Int) +ₗ ((64 : Nat) : Int) = l +ₗ 80 := by
    rw [loc_add_assoc]; rfl
  rw [List.append_assoc]
  refine (bytesPointsto_app _ _ _ _).trans ?_
  rw [ByteEncoding.encode_length]
  refine (sep_congr (typedPointsto_bytes (V := Page) _ _ _ hl).symm
    ((bytesPointsto_app _ _ _ _).trans ?_))
  rw [ByteEncoding.encode_length, e]
  exact sep_congr (typedPointsto_bytes (V := Meta) _ _ _ hl16).symm .rfl

/-- `metaBuf` as `WriteTo`'s page buffer. -/
theorem metaBuf_eq_buf (mv : Meta) :
    metaBuf mv = encode (metaHdr mv) ++ encode (metaSummed mv) ++ List.replicate 4016 (W8 0) := rfl

/-- **What `Tx.WriteTo` reads of a reader**, out of `rdTx` and back. -/
theorem rdTx_wt_acc (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) :
    rdTx (GF := GF) B N tx .loan q T ⊢
      ∃ (K : BC) (v : View) (mv : Meta) (k : Nat) (m : Loc) (l : Nat)
        (fx : Option (Nat × List w8)),
      ⌜K.B = B ∧ K.N = N ∧ T = TxView.ro v.data⌝ ∗ K.core ∗
      tx.[Tx, go!"WriteFlag"] ↦{DFrac.own q} (W64 0) ∗ tx.[Tx, go!"meta"] ↦{DFrac.own q} m ∗
      m ↦{DFrac.own q} mv ∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} K.db ∗
      rdxC v mv fx ∗ k ↪[K.B.rds]{DFrac.own q.half} (⟨v, fx⟩ : RdInfo) ∗
      rdxFile K.B K.db (DFrac.own (QpMul q sync.rfrac).half) ∗
      ghostVar K.B.map (QpMul q sync.rfrac).half.half (some (v.base, l) : MapSt) ∗
      (tx.[Tx, go!"WriteFlag"] ↦{DFrac.own q} (W64 0) -∗ tx.[Tx, go!"meta"] ↦{DFrac.own q} m -∗
        m ↦{DFrac.own q} mv -∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} K.db -∗
        k ↪[K.B.rds]{DFrac.own q.half} (⟨v, fx⟩ : RdInfo) -∗
        rdxFile K.B K.db (DFrac.own (QpMul q sync.rfrac).half) -∗
        ghostVar K.B.map (QpMul q sync.rfrac).half.half (some (v.base, l) : MapSt) -∗
        rdTx B N tx .loan q T) := by
  unfold rdTx rtxFrac
  iintro ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hmg, Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hmv, Hvc, ⟨%l, Hmap, Hmf, %Hl⟩, Hvo,
      Hrdx, %Hf⟩, Hpool⟩
  unfold rdx
  icases Hrdx with ⟨⟨%fx, #HC, Hk⟩, Hfile⟩
  obtain ⟨hT, hdb, hrw, hsrc⟩ := Hc
  iexists ⟨B, N, db, p, sp, t0⟩, v, mv, k, t.meta', l, fx
  isplitr
  · ipureintro; exact ⟨rfl, rfl, Hf.1⟩
  rw [hdb]
  unfold BC.core
  iframe Hcore Hwf Hme Hmv Hdb HC Hk Hfile Hmap
  iintro Hwf Hme Hmv Hdb Hk Hfile Hmap
  iexists db, p, sp, t0, r, c, v, mv, k
  isplitr
  · ipureintro; exact ⟨hT, hdb, hrw, hsrc⟩
  iframe Hreg Hcore Hv Hex Hpool
  iexists t
  rw [← hdb]
  iframe Hw Hmg Hme Hrb Hfp Hpg Hch Hwf Hdb Hmv Hvc Hvo
  isplitl [Hmap Hmf]
  · iexists l; rw [hdb]; iframe; ipureintro; exact Hl
  isplitl [Hk Hfile]
  · rw [hdb]; iframe Hfile; iexists fx; iframe Hk; iexact HC
  ipureintro; exact Hf

end acc

end bbolt
end EtcdGrove
end Perennial
