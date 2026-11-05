/-
`tx.write()` (U10 of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 6): the dirty pages
`tx.pages` (the records' `pm`, their bytes `bufs`) sorted by id and written with
`db.ops.writeAt` (`File.WriteAt`) in chunks of at most `MaxAllocSize - 1` bytes, each page at
`id · 4096`; then `fdatasync` unless `NoSync`; then the one-page buffers zeroed and put back in
the page pool. `tx.pages` is replaced by a fresh empty map first.

The spec is over local resources, as `Tx.writeMeta`'s (the writer side's file and the target
slots, which `Commit` carves out of `wdbLive`'s `W` slots: `wCells`' halves and `wBytes`' bytes):
the slots of every page's extent, whole inside the file and the mapping (`Commit` writes after
`grow`; spill's pages are below the high-water mark, inside the mapping). Afterwards, on success
every slot holds its page's chunk (page-cache bytes and cells, `slotsOwn`); on an error the slots hold some 4096 bytes each (a write may
stop part-way).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteDefs
public import Proof.go_etcd_io.bbolt.Commit.WriteLoop
public import Proof.go_etcd_io.bbolt.Commit.PagesSort
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Perennial.Proof.sync.Link
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.os.File__WriteAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.write()`** (see the file header): the dirty pages `pm` (`tx.pages`, its buffers holding
`bufs`; every page of `pm` has its buffer, `bufs`' domain is `pm`'s) of a file `om` mapped once at
`b` (`l` bytes), all inside both; the target slots `bufSlots bufs`. Afterwards `tx.pages` is a
fresh empty map, the buffers are gone (the one-page ones to the pool), the file's size and
mappings unchanged, and on success each slot `id + j` of the page `pg` at `id` holds
`pageChunk pg j`, its cells' client halves too (`slotsOwn`, as `store_publish` takes the new slots:
the proof reads them back with `cellsR_agree_bytes` after each `WriteAt`, as `writeMeta` does). -/
abbrev Tx.write.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (sm : Bool) (q : Qp) (dq : DFrac) (pml : Loc)
    (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (wb : Nat → List w8)
    (f : Loc) (fd : w64) (om : OsMeta) (b : Loc) (l : Nat) (dqf dqw : DFrac),
  (∀ id, (pm !! id).isSome = (bufs !! id).isSome) →
  bufsOK bufs (min om.size l / 4096) → om.size < 2 ^ 63 → om.maps = GMap.singleton b l →
  (∀ s ∈ bufSlots bufs, (wb s).length = 4096) →
  {{ K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r sm q ∗
      tx.[Tx, go!"db"] ↦{dq} K.db ∗ tx.[Tx, go!"pages"] ↦ pml ∗ pml ↦$ pm ∗
      ([∗map] id ↦ pl ∈ pm, ∃ bs, ⌜bufs !! id = some bs⌝ ∗ bytesPointsto pl (DFrac.own 1) bs) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗
      osMeta K.p (DFrac.own 1) (some om) ∗ wrSlots b K.p (bufSlots bufs) wb }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
  {{ (err : GoInterface), RET #err; statsTok r sm q ∗ tx.[Tx, go!"db"] ↦{dq} K.db ∗
      (∃ pml' : Loc, tx.[Tx, go!"pages"] ↦ pml' ∗ pml' ↦$ (∅ : GMap w64 Loc)) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗
      (∃ om' : OsMeta, osMeta K.p (DFrac.own 1) (some om') ∗
        ⌜om'.size = om.size ∧ om'.maps = om.maps⌝) ∗
      ∃ wb' : Nat → List w8, ⌜∀ s ∈ bufSlots bufs, (wb' s).length = 4096⌝ ∗
        ((⌜err = interface.nil⌝ ∗ ⌜∀ id pg, bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
            wb' (id.toNat + j) = pageChunk pg j⌝ ∗
            slotsOwn (some (b, l) : MapSt) K.p (bufSlots bufs) wb') ∨
         (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ wrSlots b K.p (bufSlots bufs) wb')) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- **`tx.write()`** proved (see the file header): the dirty pages collected from `tx.pages`
(`wr_start`, `wr_entry`: each page's header lent to `sort.Sort`, its slots as one run), sorted
(`pages_sorter`, a permutation), written chunk by chunk (`WriteAt`, the cells read back by
`cellsR_agree_bytes`), synced unless `NoSync`, and the one-page buffers zeroed into the pool; the
slots assembled into the spec's `slotsOwn` (`done_final`) or, on an error, `wrSlots`
(`err_final`). -/
theorem Tx.write.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».anyLessSpec (GF := GF) (hG := hG))
    (hOv : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hUBS : internal.common.UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG)) :
    Tx.write.spec (GF := GF) (hG := hG) := by
  intro K tx r sm q dq pml pm bufs wb f fd om b l dqf dqw hdom hok hsz hmaps hwb
  wp_start as ⟨#Hcore, #Hreg, Hst, Hdb, Hpg, Hpm, Hbufs, Hf, Hwa, Hfo, Hfd, Hm, Hslots⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  iunfold dbFixed at Hfix
  icases Hfix with ⟨#Hps, #Hsp, ⟨%lg, #Hlg, #Hlgok⟩, -, -, -, ⟨%ns, #Hns⟩, -, -, -, -, -, -, -, -, -,
    -, ⟨%pf, #Hpool, -⟩, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hpks : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  wp_auto
  iunfold dbLogger at Hlgok
  wp_apply hLogger K.db lg Ht0.2.1 $$ []
  · iframe #
  wp_apply (wp_map_len_lt (K := w64) (V := Loc) pml pm (DFrac.own 1)) $$ [Hpm] as ⟨Hpm, %Hpms⟩
  · iexact Hpm
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 (pm.size : Int)) ⟨by word, by word⟩)
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc)
    (fun (keys : List w64) (i : Int) => iprop(∃ (sl : GoSlice) (L : List (w64 × Loc × List w8))
      (pv : Loc),
      "Hpgs" ∷ pages_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* L.map (·.2.1) ∗
      "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗ "Hpv" ∷ p_ptr ↦ pv ∗
      "%HL" ∷ ⌜0 ≤ i ∧ L.map Prod.fst = keys.take i.toNat ∧ ∀ e ∈ L, bufs !! e.1 = some e.2.2⌝ ∗
      "HLh" ∷ ([∗list] e ∈ L, e.2.1 ↦ pageHdr e.2.2) ∗
      "HLr" ∷ ([∗list] e ∈ L, pgRest b K.p e) ∗
      "Hrest" ∷ ([∗list] k ∈ keys.drop i.toNat, wrKey b K.p pm bufs k)))
    _ _ _ pml pm _ $$ Hpm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  have hkb : ∀ k, k ∈ keys ↔ (bufs !! k).isSome := fun k => (Hkset k).trans (by rw [hdom k])
  ihave Hb := wr_bigSepM_keys (fun k pl => iprop(∃ bs, ⌜bufs !! k = some bs⌝ ∗
    bytesPointsto (GF := GF) pl (DFrac.own 1) bs)) keys pm Hknd Hkset $$ Hbufs
  icases wr_start b K.p bufs wb keys Hknd hkb hwb $$ Hslots with ⟨%Hnd, Hs⟩
  ihave Hrest : [∗list] k ∈ keys, wrKey b K.p pm bufs k $$ [Hb Hs]
  · unfold wrKey
    iapply BigSepL.bigSepL_sep_eqv.2
    iframe
  isplitl [pages Hsl0 Hcap0 p Hrest]
  · iexists sl0, [], _
    simp only [Int.toNat_zero, List.drop_zero, List.take_zero, List.map_nil, List.replicate,
      show sint.nat (W64 0) = 0 from rfl]
    iframe
    isplitr
    · ipureintro; simp
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨Hi0, HLk, HLm⟩ := HL
    try wp_auto
    rw [wr_drop_cons _ _ _ Hkey]
    icases BigSepL.bigSepL_cons.1 $$ Hrest with ⟨Hk, Hrest⟩
    unfold wrKey
    icases wr_entry b K.p pm bufs _ hok key v Hv $$ Hk with ⟨%bs, %Hbs, Hh, Hr⟩
    wp_apply wp_slice_literal (V := Loc) [v]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl', L ++ [(key, v, bs)], v
    have Hi : (i + 1).toNat = i.toNat + 1 := by omega
    rw [Hi]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe Hpgs Hcap Hsl Hrest Hpv
    isplitr
    · ipureintro
      refine ⟨by omega, ?_, fun e he => ?_⟩
      · rw [HLk, List.take_add_one, Hkey]; rfl
      · rcases List.mem_append.1 he with he | he
        · exact HLm e he
        · rw [List.mem_singleton] at he; subst he; exact Hbs
    isplitl [HLh Hh]
    · iapply BigSepL.bigSepL_snoc.2; iframe
    · iapply BigSepL.bigSepL_snoc.2; iframe
  iintro HP Hpm
  iNamed HP
  obtain ⟨-, HLk, HLm⟩ := HL
  rw [show (GMap.size pm : Int).toNat = keys.length by omega, List.take_length] at HLk
  rw [show (GMap.size pm : Int).toNat = keys.length by omega, List.drop_length]
  iclear Hrest
  have hlim : min om.size l / 4096 < 2 ^ 52 := by
    have : min om.size l ≤ om.size := Nat.min_le_left _ _
    omega
  have hLlen : L.length ≤ min om.size l / 4096 := by
    have := wr_keys_le keys (min om.size l / 4096) Hknd (fun k hk => by
      obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 ((hkb k).1 hk)
      have := (hok k pg hpg).2.2.2
      omega)
    rw [← HLk, List.length_map] at this
    exact this
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) Pgid.ty Page.ty.PointerType) as %pl' Hpl'
  try wp_auto
  ihave #Hsorter := pages_sorter (E := w64 × Loc × List w8) sl (fun e => e.2.1)
    (fun e => pageHdr e.2.2) $$ Hpkc
  wp_apply (hSort (w64 × Loc × List w8) (interface.mk Pages.ty #sl)
    (pagesR sl (fun e => e.2.1) (fun e => pageHdr e.2.2)) L) $$ [Hsl HLh] as %L' ⟨HR, %Hperm⟩
  · iframe #
    unfold pagesR
    iframe
    ipureintro; omega
  unfold pagesR
  icases HR with ⟨Hsl, HLh⟩
  ihave HLr := (BigSepL.bigSepL_perm (Φ := fun e => pgRest (GF := GF) b K.p e) Hperm).1 $$ HLr
  have HL'k : (L'.map Prod.fst).Perm (bufs.toList.map Prod.fst) := by
    refine (Hperm.map Prod.fst).symm.trans ?_
    rw [HLk]
    exact keys_perm bufs keys Hknd hkb
  have HL'm : ∀ e ∈ L', bufs !! e.1 = some e.2.2 := fun e he => HLm e (Hperm.mem_iff.2 he)
  have HL'len : L'.length ≤ min om.size l / 4096 := by rw [← Hperm.length_eq]; exact hLlen
  clear HLk HLm Hperm
  have hlenL : ∀ e ∈ L', e.2.2.length = 4096 * (1 + pageOverflow e.2.2) :=
    fun e he => (hok e.1 e.2.2 (HL'm e he)).2.1
  try wp_auto
  ihave IH : (∃ (j : w64) (pv : Loc) (om' : OsMeta),
      "i" ∷ i_ptr ↦ j ∗ "p" ∷ p_ptr ↦ pv ∗ "Hst" ∷ statsTok r sm q ∗
      "Hm" ∷ osMeta K.p (DFrac.own 1) (some om') ∗
      "Hdone" ∷ ([∗list] e ∈ L'.take (sint.nat j), pgDone b K.p e) ∗
      "Htodo" ∷ ([∗list] e ∈ L'.drop (sint.nat j), pgRest b K.p e) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ L'.length ∧ om'.size = om.size ∧
        om'.maps = om.maps⌝ : IProp GF) $$ [i p Hst Hm HLr]
  · iexists W64 0, _, om
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    simp only [named]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for IH
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map] at Hsll
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z sl.len := by simpa using Hif
    clear Hif
    have Hjn : sint.nat j < L'.length := by have := Hsll.1; word
    obtain ⟨c, Hc⟩ : ∃ c, L'[sint.nat j]? = some c := ⟨_, List.getElem?_eq_getElem Hjn⟩
    have Hcm : c ∈ L' := List.mem_of_getElem? Hc
    have Hget : (L'.map (fun e => e.2.1))[(sint.Z j).toNat]? = some c.2.1 := by
      rw [List.getElem?_map, show (sint.Z j).toNat = sint.nat j from rfl, Hc]; rfl
    try rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len
      from ⟨Hj.1, Hlt⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ c.2.1 Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hget
    try wp_auto
    icases BigSepL.bigSepL_mem_acc Hcm $$ HLh with ⟨Hh, HLhb⟩
    wp_apply hOv c.2.1 (pageHdr c.2.2) (DFrac.own 1) $$ [$Hpkc $Hh] as Hh
    try wp_auto
    wp_apply hId c.2.1 (pageHdr c.2.2) (DFrac.own 1) $$ [$Hpkc $Hh] as Hh
    try wp_auto
    -- the page's values
    obtain ⟨hcid, hclen, hc2, hcin⟩ := hok c.1 c.2.2 (HL'm c Hcm)
    have hov : pageOverflow c.2.2 < 2 ^ 32 := by
      unfold pageOverflow; exact BitVec.isLt _
    have e1 : (decode (List.drop 2 (List.drop 2 (List.drop 8 (bytesAt c.2.2 0 16)))) : w32) =
        (pageHdr c.2.2).overflow' := rfl
    have e2 : (decode (List.take 8 (bytesAt c.2.2 0 16)) : w64) = (pageHdr c.2.2).id' := rfl
    have hremv : (W64 (uint.Z (pageHdr c.2.2).overflow') + W64 1) * W64 4096 =
        W64 ((c.2.2.length - 0 : Nat) : Int) := by
      rw [hclen]; unfold pageOverflow at hov ⊢; word
    have hoffv : (pageHdr c.2.2).id' * W64 4096 = W64 ((4096 * c.1.toNat + 0 : Nat) : Int) := by
      unfold pageId at hcid
      have : c.1.toNat < 2 ^ 52 := by omega
      rw [← hcid] at this ⊢; word
    rw [e1, e2, hremv, hoffv, show (zero_val w64 : w64) = W64 ((0 : Nat) : Int) from rfl]
    -- the page's buffer and its slots as one run
    rw [wr_drop_cons _ _ _ Hc]
    icases BigSepL.bigSepL_cons.1 $$ Htodo with ⟨Hcr, Htodo⟩
    icases rest_run b K.p c (by omega) $$ [Hh Hcr] with ⟨%Hcp, Hpb, Hro, Hrc⟩
    · iframe
    rw [← hclen]
    have hcne : c.2.2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    icases Read.bytesPointsto_bounds _ _ _ hcne $$ Hpb with ⟨Hpb, %Hcb⟩
    ihave Hd1 : osBytes (GF := GF) K.p (4096 * c.1.toNat) (DFrac.own 1) [] $$ []
    · iapply (osBytes_nil' (GF := GF) K.p _ _).2; iempintro
    ihave Hd2 : bytesPointsto (GF := GF) (b +ₗ ((4096 * c.1.toNat : Nat) : Int))
        (DFrac.own (1 : Qp).half) (c.2.2.take 0) $$ []
    · rw [List.take_zero]; unfold bytesPointsto; iempintro
    ihave IH2 : (∃ (w : Nat) (ysd : List (w8 × Bool)) (om2 : OsMeta),
        "rem" ∷ rem_ptr ↦ W64 ((c.2.2.length - w : Nat) : Int) ∗
        "offset" ∷ offset_ptr ↦ W64 ((4096 * c.1.toNat + w : Nat) : Int) ∗
        "written" ∷ written_ptr ↦ W64 ((w : Nat) : Int) ∗ "Hst" ∷ statsTok r sm q ∗
        "Hm" ∷ osMeta K.p (DFrac.own 1) (some om2) ∗
        "Hd1" ∷ osBytes K.p (4096 * c.1.toNat) (DFrac.own 1) ysd ∗
        "Hd2" ∷ bytesPointsto (b +ₗ ((4096 * c.1.toNat : Nat) : Int)) (DFrac.own (1 : Qp).half)
          (c.2.2.take w) ∗
        "Hro" ∷ oAny K.p (4096 * c.1.toNat + w) (c.2.2.length - w) ∗
        "Hrc" ∷ cAny b (4096 * c.1.toNat + w) (c.2.2.length - w) ∗
        "%Hw" ∷ ⌜w < c.2.2.length ∧ ysd.map Prod.fst = c.2.2.take w ∧ om2.size = om.size ∧
          om2.maps = om.maps⌝ : IProp GF) $$ [rem offset written Hst Hm Hd1 Hd2 Hro Hrc]
    · iexists 0, [], om'
      simp only [named, Nat.sub_zero, Nat.add_zero]
      iframe
      ipureintro
      exact ⟨by omega, by simp, Hj.2.2.1, Hj.2.2.2⟩
    wp_for IH2
    obtain ⟨Hwlt, Hysd, Hom2s, Hom2m⟩ := Hw
    obtain ⟨cs, Hcs⟩ : ∃ cs : Nat, cs = min (c.2.2.length - w) 2147483646 := ⟨_, rfl⟩
    have Hcs0 : 0 < cs := by omega
    have hcin' : 4096 * c.1.toNat + c.2.2.length ≤ min om.size l := by
      have := Nat.div_mul_le_self (min om.size l) 4096
      omega
    have hnw : c.2.2.length - w < 2 ^ 62 := by
      have : min om.size l ≤ om.size := Nat.min_le_left _ _
      omega
    wp_if_destruct
    focus
      have : 2147483646 < c.2.2.length - w := by
        have h := Hif; rw [show uint.Z (W64 2147483646) = 2147483646 from rfl] at h
        have : uint.Z (W64 ((c.2.2.length - w : Nat) : Int)) = ((c.2.2.length - w : Nat) : Int) := by
          word
        omega
      try wp_auto
      rw [show (W64 2147483646 : w64) = W64 ((cs : Nat) : Int) by rw [Hcs]; congr 1; omega]
    rotate_left
    focus
      have : ¬ 2147483646 < c.2.2.length - w := by
        intro h; apply Hif
        rw [show uint.Z (W64 2147483646) = 2147483646 from rfl]
        have : uint.Z (W64 ((c.2.2.length - w : Nat) : Int)) = ((c.2.2.length - w : Nat) : Int) := by
          word
        omega
      try wp_auto
      rw [show c.2.2.length - w = cs by omega]
      ihave rem : (rem_ptr ↦ W64 ((c.2.2.length - w : Nat) : Int) : IProp GF) $$ [rem]
      · rw [show c.2.2.length - w = cs by omega]; iexact rem
      ihave Hro : oAny (GF := GF) K.p (4096 * c.1.toNat + w) (c.2.2.length - w) $$ [Hro]
      · rw [show c.2.2.length - w = cs by omega]; iexact Hro
      ihave Hrc : cAny (GF := GF) b (4096 * c.1.toNat + w) (c.2.2.length - w) $$ [Hrc]
      · rw [show c.2.2.length - w = cs by omega]; iexact Hrc
    all_goals
      have hsw : sint.Z (W64 ((w : Nat) : Int)) = (w : Int) := by word
      have hscs : sint.Z (W64 ((cs : Nat) : Int)) = (cs : Int) := by word
      wp_apply hUBS c.2.1 (W64 ((w : Nat) : Int)) (W64 0) (W64 ((cs : Nat) : Int))
        (by simp only [Loc.add, hsw]; omega) (by simp only [Loc.add, hsw, hscs]; omega)
        (by decide) (by rw [hscs]; simp)
      have Hsle : slice.mk (c.2.1 +ₗ sint.Z (W64 ((w : Nat) : Int)) +ₗ sint.Z (W64 0))
          (W64 ((cs : Nat) : Int) - W64 0) (W64 ((cs : Nat) : Int) - W64 0) =
          slice.mk (c.2.1 +ₗ ((w : Nat) : Int)) (W64 ((cs : Nat) : Int)) (W64 ((cs : Nat) : Int)) := by
        have hs0 : (W64 ((cs : Nat) : Int) - W64 0 : w64) = W64 ((cs : Nat) : Int) := by word
        rw [hsw, show sint.Z (W64 0) = 0 from rfl, loc_add_0, hs0]
      rw [Hsle]
      try wp_auto
      -- the chunk, its file bytes and its cells
      icases chunk_acc c.2.1 c.2.2 w cs (by omega) Hcs0 (by omega) $$ Hpb with ⟨Hck, Hpbb⟩
      have eo := oAny_app (GF := GF) K.p (4096 * c.1.toNat + w) cs (c.2.2.length - w - cs)
      have ec := cAny_app (GF := GF) b (4096 * c.1.toNat + w) cs (c.2.2.length - w - cs)
      rw [show cs + (c.2.2.length - w - cs) = c.2.2.length - w by omega] at eo ec
      icases eo.1 $$ Hro with ⟨Hro1, Hro2⟩
      icases ec.1 $$ Hrc with ⟨Hrc1, Hrc2⟩
      iunfold oAny at Hro1
      icases Hro1 with ⟨%xs, Hxs, %Hxl⟩
      have hcl : (bytesAt c.2.2 w cs).length = cs := by
        unfold bytesAt; simp only [List.length_take, List.length_drop]; omega
      have htn : (W64 ((4096 * c.1.toNat + w : Nat) : Int)).toNat = 4096 * c.1.toNat + w := by
        have : 4096 * c.1.toNat + w < 2 ^ 63 := by omega
        word
      have hmin2 : min (4096 * c.1.toNat + w) om2.size = 4096 * c.1.toNat + w := by omega
      ihave Hc : mcellsAny om2.maps (min (W64 ((4096 * c.1.toNat + w : Nat) : Int)).toNat om2.size)
          ((W64 ((4096 * c.1.toNat + w : Nat) : Int)).toNat + (bytesAt c.2.2 w cs).length) $$ [Hrc1]
      · rw [Hom2m, hmaps, htn, hmin2, hcl]
        iapply (mcells_single b l _ cs (by omega)).2
        iexact Hrc1
      have h0 : 0 ≤ (W64 ((4096 * c.1.toNat + w : Nat) : Int)).toInt := by
        have : 4096 * c.1.toNat + w < 2 ^ 63 := by omega
        rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
      wp_apply hWriteAt f fd K.p (DFrac.own 1) _ (bytesAt c.2.2 w cs) (DFrac.own 1)
        (W64 ((4096 * c.1.toNat + w : Nat) : Int)) (DFrac.own 1) ⟨K.p, true, true⟩ 1 om2 xs rfl h0
        (by rw [hcl]; omega) (by rw [hcl, htn]; omega) (by rw [hcl, htn]; omega) (fun _ => rfl)
        $$ [Hfo Hck Hfd Hm Hxs Hc] as %nn %err ⟨Hfo, Hck, Hfd, %jj, %ys, %hh, %Hjj, Hm, Hys, Hc, Herr⟩
      · iframe #
        rw [htn, hmin2, ← fileOwn_eq]
        iframe
      obtain ⟨hjjle, hysp, -, -, hres⟩ := Hjj
      rw [htn] at hysp ⊢
      have hsize : pwSize om2.size (4096 * c.1.toNat + w) jj = om2.size :=
        pwSize_inside _ _ _ cs (by rw [hcl] at hjjle; exact hjjle) (by omega)
      rw [hsize, hmin2, hcl]
      have hyl : ys.length = cs := by
        have := congrArg List.length hysp
        simp only [List.length_map] at this
        rw [this, pwBytes_length, hsize, hcl]; omega
      ihave Hc : cAny b (4096 * c.1.toNat + w) cs $$ [Hc]
      · rw [Hom2m, hmaps]; iapply (mcells_single b l _ cs (by omega)).1; iexact Hc
      cases err with
      | ok ei =>
        have hyd : ysd.length = w := by
          have := congrArg List.length Hysd; simp only [List.length_map, List.length_take] at this
          omega
        cases lg with
        | nil => unfold boltLogger; iexfalso; iexact Hlgok
        | ok li =>
        simp only [fmtErrorOkOrNil]
        icases Herr with #Herr
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 100, W8 118] _
          [interface.mkOk go.int64 #(W64 ((4096 * c.1.toNat + w : Nat) : Int)), GoInterface.ok ei]
          _ iprop(True) _ (by decide) (by decide) rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
        · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ,
            List.set_cons_zero]
          iexact Hsl3
        · log_args_ok
        try wp_auto
        wp_for_post
        wp_for_post
        try wp_auto
        ihave Hcur := cur_any b K.p c.1.toNat (1 + pageOverflow c.2.2) w cs (c.2.2.length - w - cs)
          ysd ys (c.2.2.take w) hyd (by simp only [List.length_take]; omega) hyl (by omega)
          $$ [Hd1 Hd2 Hys Hc Hro2 Hrc2]
        · iframe
        ihave Hall := err_assemble b K.p L' (sint.nat j) c Hc hlenL $$ [Hdone Hcur Htodo]
        · iframe
        icases err_final b K.p bufs L' HL'k HL'm $$ Hall with ⟨%wb', %Hwb', Hwr⟩
        iapply HΦ
        rw [fileOwn_eq]
        iframe Hst Hdb Hf Hwa Hfo Hfd
        isplitl [Hpg Hpl']
        · iexists pl'; iframe
        isplitl [Hm]
        · iexists _; iframe Hm; ipureintro; exact ⟨Hom2s, Hom2m⟩
        iexists wb'
        isplitr
        · ipureintro; exact Hwb'
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        isplitr
        · iexact Herr
        iexact Hwr
      | nil =>
        have hjj : jj = cs := by
          rcases hres with ⟨h1, -, -⟩ | ⟨-, h2⟩
          · rw [hcl] at h1; exact h1
          · exact absurd rfl h2
        subst jj
        have hys : ys.map Prod.fst = bytesAt c.2.2 w cs := by
          rw [hysp]
          have := pwBytes_inside_fst om2.size (4096 * c.1.toNat + w) (bytesAt c.2.2 w cs) cs xs
            (by rw [hcl]; omega) (by rw [hcl]; exact Hxl) (Or.inr hcl.symm)
          rw [this, if_neg (by omega)]
        try wp_auto
        iunfold cAny at Hc
        icases Hc with ⟨%vf, Hc⟩
        ihave Hc : cellsR b (4096 * c.1.toNat + w) ys.length vf $$ [Hc]
        · rw [hyl]; iexact Hc
        have hbm : ({ om2 with hi := hh } : OsMeta).maps !! b = some l := by
          show om2.maps !! b = some l
          rw [Hom2m, hmaps]; exact GMap.lookup_singleton_eq b l
        have hyl' : 4096 * c.1.toNat + w + ys.length ≤ l := by rw [hyl]; omega
        iapply cellsR_agree_bytes _ rfl K.p (DFrac.own 1) { om2 with hi := hh } b l hbm
          (DFrac.own 1) (by simp) _ ys (4096 * c.1.toNat + w) vf hyl' $$ Hos Hm Hys Hc
        iintro Hm Hys Hc
        icases cellsR_bytes b (ys.map Prod.fst) _ $$ [Hc] with Hc
        · simp only [List.length_map]; iexact Hc
        rw [hys]
        wp_apply hInc K tx r sm q (W64 1) $$ [Hst] as %_n Hst
        · iframe #; iframe
        try wp_auto
        have hyd : ysd.length = w := by
          have := congrArg List.length Hysd; simp only [List.length_map, List.length_take] at this
          omega
        ihave Hpb := Hpbb $$ Hck
        ihave Hd1 : osBytes (GF := GF) K.p (4096 * c.1.toNat) (DFrac.own 1) (ysd ++ ys) $$ [Hd1 Hys]
        · iapply (osBytes_take_drop (GF := GF) K.p (4096 * c.1.toNat) (DFrac.own 1) (ysd ++ ys)
            ysd.length (by simp)).2
          rw [List.take_left, List.drop_left, hyd]
          iframe
        have hfst : (ysd ++ ys).map Prod.fst = c.2.2.take (w + cs) := by
          rw [List.map_append, Hysd, hys, List.take_add]; rfl
        ihave Hd2 : bytesPointsto (GF := GF) (b +ₗ ((4096 * c.1.toNat : Nat) : Int))
            (DFrac.own (1 : Qp).half) (c.2.2.take (w + cs)) $$ [Hd2 Hc]
        · iapply (bytes_cut b (4096 * c.1.toNat) _ (c.2.2.take (w + cs)) w
            (by simp only [List.length_take]; omega)).2
          rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take,
            show w + cs - w = cs by omega]
          iframe
        have hremv2 : W64 ((c.2.2.length - w : Nat) : Int) - W64 ((cs : Nat) : Int) =
            W64 ((c.2.2.length - (w + cs) : Nat) : Int) := by word
        rw [hremv2]
        wp_if_destruct
        · -- the page is written
          have hend : w + cs = c.2.2.length := by
            have h := Hif
            have : c.2.2.length - (w + cs) < 2 ^ 62 := by omega
            have h2 : (c.2.2.length - (w + cs) : Nat) = 0 := by
              have := congrArg BitVec.toNat h; simp at this; omega
            omega
          rw [hend, List.take_length] at hfst
          rw [hend, List.take_length]
          icases run_pgDone b K.p c (ysd ++ ys) hfst hclen Hcp $$ [Hpb Hd1 Hd2] with ⟨Hh, Hcd⟩
          · iframe
          ihave HLh := HLhb $$ Hh
          ihave Hdone : [∗list] e ∈ L'.take (sint.nat j) ++ [c], pgDone (GF := GF) b K.p e
            $$ [Hdone Hcd]
          · iapply BigSepL.bigSepL_snoc.2; iframe
          ihave Hdone : [∗list] e ∈ L'.take (sint.nat j + 1), pgDone (GF := GF) b K.p e $$ [Hdone]
          · rw [List.take_add_one, Hc, Option.toList_some]; iexact Hdone
          wp_for_post
          wp_for_post
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
            have : sint.nat j < 2 ^ 62 := by omega
            word
          rw [fileOwn_eq]
          iframe
          iexists j + W64 1, c.2.1, { om2 with hi := hh }
          rw [hj1]
          iframe
          ipureintro
          exact ⟨by word, by omega, Hom2s, Hom2m⟩
        · have hnend : w + cs < c.2.2.length := by
            have h := Hif
            refine Classical.byContradiction fun hc => h ?_
            rw [show c.2.2.length - (w + cs) = 0 by omega]; rfl
          try wp_auto
          have ho : W64 ((4096 * c.1.toNat + w : Nat) : Int) + W64 ((cs : Nat) : Int) =
              W64 ((4096 * c.1.toNat + (w + cs) : Nat) : Int) := by word
          have hw2 : W64 ((w : Nat) : Int) + W64 ((cs : Nat) : Int) = W64 ((w + cs : Nat) : Int) := by
            word
          rw [ho, hw2]
          ihave Hro2 : oAny (GF := GF) K.p (4096 * c.1.toNat + (w + cs)) (c.2.2.length - (w + cs))
            $$ [Hro2]
          · rw [← Nat.add_assoc, ← Nat.sub_sub]; iexact Hro2
          ihave Hrc2 : cAny (GF := GF) b (4096 * c.1.toNat + (w + cs)) (c.2.2.length - (w + cs))
            $$ [Hrc2]
          · rw [← Nat.add_assoc, ← Nat.sub_sub]; iexact Hrc2
          wp_for_post
          rw [fileOwn_eq]
          iframe
          iexists w + cs, ysd ++ ys, { om2 with hi := hh }
          iframe
          ipureintro
          exact ⟨hnend, hfst, Hom2s, Hom2m⟩
  · have Hjl : sint.nat j = L'.length := by have := Hsll.1; word
    obtain ⟨-, -, Hom's, Hom'm⟩ := Hj
    rw [Hjl, List.take_length, List.drop_length]
    iclear Htodo
    icases done_split b K.p L' $$ [HLh Hdone] with ⟨Hbufs, Hsd⟩
    · iframe
    try wp_auto
    have hlenB : ∀ id pg, bufs !! id = some pg → pg.length = 4096 * (1 + pageOverflow pg) :=
      fun id pg h => (hok id pg h).2.1
    cases ns
    focus
      -- `NoSync` off: the sync
      try wp_auto
      wp_apply hSync K.db f fd K.p om' dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
        as %e2 ⟨Hf, Hfo, Hfd, ⟨%m', Hm, %Hm'⟩, Hr⟩
      · iframe #; iframe
      icases Hr with (%He | ⟨%He, #Hfe⟩)
      rotate_left
      · cases e2 with
        | nil => exact absurd rfl He
        | ok e2 =>
        cases lg with
        | nil => unfold boltLogger; iexfalso; iexact Hlgok
        | ok li =>
        ihave %hgoos : ⌜goosLinux⌝ $$ []
        · iapply goosLinux_of_pkgInit $$ Hpkg
        ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
        · iapply goarchAmd64_of_pkgInit $$ Hpkg
        unfold goosLinux at hgoos
        unfold goarchAmd64 at hgoarch
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 118] _
          [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
            GoInterface.ok e2] _ iprop(True) _
          (by decide) (by decide) rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
        · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
            show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
          iexact Hsl3
        · log_args_ok
        try wp_auto
        ihave Hall := sd_any b K.p L' hlenL $$ Hsd
        icases err_final b K.p bufs L' HL'k HL'm $$ Hall with ⟨%wb', %Hwb', Hwr⟩
        try iapply HΦ
        iframe Hst Hdb Hf Hwa Hfo Hfd
        isplitl [Hpg Hpl']
        · iexists pl'; iframe
        isplitl [Hm]
        · iexists _; iframe Hm; ipureintro; exact ⟨Hm'.1.trans Hom's, Hm'.2.trans Hom'm⟩
        iexists wb'
        isplitr
        · ipureintro; exact Hwb'
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        isplitr
        · iexact Hfe
        iexact Hwr
      subst He
      try wp_auto
      ihave Hm : (∃ om'' : OsMeta, osMeta K.p (DFrac.own 1) (some om'') ∗
          ⌜om''.size = om.size ∧ om''.maps = om.maps⌝ : IProp GF) $$ [Hm]
      · iexists m'; iframe; ipureintro; exact ⟨Hm'.1.trans Hom's, Hm'.2.trans Hom'm⟩
    rotate_left
    focus
      try wp_auto
      ihave Hm : (∃ om'' : OsMeta, osMeta K.p (DFrac.own 1) (some om'') ∗
          ⌜om''.size = om.size ∧ om''.maps = om.maps⌝ : IProp GF) $$ [Hm]
      · iexists om'; iframe; ipureintro; exact ⟨Hom's, Hom'm⟩
    all_goals
      -- the one-page buffers back to the pool
      ihave IH3 : (∃ (j2 : w64) (pv : Loc), "i" ∷ i_ptr ↦ j2 ∗ "p" ∷ p_ptr ↦ pv ∗
          "Hbufs" ∷ ([∗list] e ∈ L'.drop (sint.nat j2), pgBuf e) ∗
          "%Hj2" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.nat j2 ≤ L'.length⌝ : IProp GF) $$ [i p Hbufs]
      · iexists W64 0, _
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
        simp only [named]
        iframe
        ipureintro; exact ⟨by decide, by omega⟩
      wp_for IH3
      wp_if_destruct
      · have Hlt2 : sint.Z j2 < sint.Z sl.len := by
          first | simpa using Hif | simpa using GoGlobalContext.intoVal_inj_bool Hif
        clear Hif
        have Hjn2 : sint.nat j2 < L'.length := by have := Hsll.1; word
        obtain ⟨c2, Hc2⟩ : ∃ c, L'[sint.nat j2]? = some c := ⟨_, List.getElem?_eq_getElem Hjn2⟩
        have Hc2m : c2 ∈ L' := List.mem_of_getElem? Hc2
        have Hget2 : (L'.map (fun e => e.2.1))[(sint.Z j2).toNat]? = some c2.2.1 := by
          rw [List.getElem?_map, show (sint.Z j2).toNat = sint.nat j2 from rfl, Hc2]; rfl
        try rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z sl.len
          from ⟨Hj2.1, Hlt2⟩))]
        wp_apply wp_load_slice_index _ (sint.Z j2) _ _ c2.2.1 Hj2.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; exact Hget2
        try wp_auto
        rw [wr_drop_cons _ _ _ Hc2]
        icases BigSepL.bigSepL_cons.1 $$ Hbufs with ⟨Hc2b, Hbufs⟩
        iunfold pgBuf at Hc2b
        icases Hc2b with ⟨Hh2, %Hp2, Hr2⟩
        wp_apply hOv c2.2.1 (pageHdr c2.2.2) (DFrac.own 1) $$ [$Hpkc $Hh2] as Hh2
        try wp_auto
        have hj21 : sint.nat (j2 + W64 1) = sint.nat j2 + 1 := by
          have : sint.nat j2 < 2 ^ 62 := by omega
          word
        have hl2 := hlenL c2 Hc2m
        have e1' : (decode (List.drop 2 (List.drop 2 (List.drop 8 (bytesAt c2.2.2 0 16)))) : w32) =
            (pageHdr c2.2.2).overflow' := rfl
        rw [e1']
        by_cases hov : pageOverflow c2.2.2 = 0
        · have hz : (W64 (uint.Z (pageHdr c2.2.2).overflow') : w64) = W64 0 := by
            unfold pageOverflow at hov
            have h0 : (pageHdr c2.2.2).overflow' = 0 := BitVec.eq_of_toNat_eq (by simpa using hov)
            rw [h0]; rfl
          rw [decide_eq_true hz]
          try wp_auto
          have hl2' : c2.2.2.length = 4096 := by rw [hl2, hov]
          ihave Hpb := (page_split c2.2.1 c2.2.2 (by omega) Hp2).2 $$ [Hh2 Hr2]
          · iframe
          icases Read.bytesPointsto_bounds _ _ _ (List.ne_nil_of_length_pos (by omega)) $$ Hpb
            with ⟨Hpb, %Hb2⟩
          have h00 : sint.Z (W64 0) = 0 := rfl
          have h4096 : sint.Z (W64 4096) = 4096 := rfl
          wp_apply hUBS c2.2.1 (W64 0) (W64 0) (W64 4096)
            (by rw [h00, loc_add_0]; exact Hp2)
            (by rw [h00, loc_add_0, h4096]; have := Hb2.2; rw [hl2'] at this; push_cast at this; omega)
            (by decide) (by decide)
          have Hsle2 : slice.mk (c2.2.1 +ₗ sint.Z (W64 0) +ₗ sint.Z (W64 0)) (W64 4096 - W64 0)
              (W64 4096 - W64 0) =
              slice.mk c2.2.1 (W64 ((c2.2.2.length : Nat) : Int)) (W64 ((c2.2.2.length : Nat) : Int)) := by
            rw [h00, loc_add_0, loc_add_0, hl2']; rfl
          rw [Hsle2]
          ihave Hbuf := (Read.bytesPointsto_ownSlice c2.2.1 _ c2.2.2 Hp2 (by omega)).1 $$ Hpb
          try wp_auto
          rename_i iu
          irename : (iu ↦ (_ : w64) : IProp GF) => Hiu
          have Hpsl : sint.Z (W64 ((c2.2.2.length : Nat) : Int)) = c2.2.2.length := by
            rw [hl2']; rfl
          ihave IH4 : (∃ (k uv : w64), "Hk" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu ↦ uv ∗
              "Hbuf" ∷ slice.mk c2.2.1 (W64 ((c2.2.2.length : Nat) : Int))
                (W64 ((c2.2.2.length : Nat) : Int)) ↦*
                (List.replicate (sint.nat k) (W8 0) ++ c2.2.2.drop (sint.nat k)) ∗
              "%Hk2" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ c2.2.2.length⌝ : IProp GF) $$ [i Hiu Hbuf]
          · iexists W64 0, _
            rw [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero, List.nil_append,
              List.drop_zero]
            simp only [named]
            iframe
            ipureintro; exact ⟨by decide, by omega⟩
          wp_for IH4
          by_cases hk : sint.Z k < sint.Z (W64 ((c2.2.2.length : Nat) : Int))
          · try rw [decide_eq_true hk]
            try simp only [_root_.decide_true, ↓reduceIte]
            have Hkn : sint.nat k < c2.2.2.length := by rw [Hpsl] at hk; word
            have Hbl2 : (List.replicate (sint.nat k) (W8 0) ++ c2.2.2.drop (sint.nat k)).length =
                c2.2.2.length := by simp; omega
            obtain ⟨bk, Hbk⟩ : ∃ bk, (List.replicate (sint.nat k) (W8 0) ++
                c2.2.2.drop (sint.nat k))[sint.nat k]? = some bk :=
              ⟨_, List.getElem?_eq_getElem (by rw [Hbl2]; exact Hkn)⟩
            have Hbd : (0 ≤ sint.Z k ∧ sint.Z k < sint.Z (W64 ((c2.2.2.length : Nat) : Int))) =
                True := eq_true ⟨Hk2.1, hk⟩
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ Hbd]
            try (wp_apply wp_load_slice_index _ (sint.Z k) _ _ bk Hk2.1 $$ [Hbuf] as Hbuf
                 focus (iframe; ipureintro; exact Hbk))
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ Hbd]
            wp_apply wp_store_slice_index _ (sint.Z k) _ (W8 0) $$ [Hbuf] as Hbuf
            · iframe; ipureintro; rw [Hbl2]; constructor <;> word
            rw [show (sint.Z k).toNat = sint.nat k from rfl, zero_step c2.2.2 _ Hkn]
            try wp_auto
            wp_for_post
            iframe
            iexists k + W64 1, _
            have Hk21 : sint.nat (k + W64 1) = sint.nat k + 1 := by
              have : sint.nat k < 2 ^ 62 := by omega
              word
            rw [Hk21]
            iframe
            ipureintro; exact ⟨by word, by omega⟩
          · try rw [decide_eq_false hk]
            try simp only [Bool.false_eq_true, ↓reduceIte, _root_.decide_false]
            have Hke : sint.nat k = c2.2.2.length := by rw [Hpsl] at hk; word
            rw [Hke, List.drop_length, List.append_nil, hl2']
            try wp_auto
            try rw [if_pos (by decide)]
            try rw [if_neg (by decide)]
            try wp_auto
            wp_apply sync.Pool.wp_Put _ pf (poolR _ _ iprop(True)) pageBuf _ $$ [Hbuf]
            · iframe #
              isplitr
              · iapply Hpool
              unfold pageBuf
              iexists _
              iframe
              ipureintro; rfl
            try wp_auto
            wp_for_post
            iframe
            iexists j2 + W64 1, c2.2.1
            rw [hj21]
            iframe
            ipureintro; exact ⟨by word, by omega⟩
        · have hnz : ¬ (W64 (uint.Z (pageHdr c2.2.2).overflow') : w64) = W64 0 := by
            unfold pageOverflow at hov
            intro h; apply hov
            have := (pageHdr c2.2.2).overflow'.isLt
            have h2 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofInt] at h2
            simp only [uint.Z] at h2 ⊢
            omega
          rw [decide_eq_false hnz]
          try wp_auto
          wp_for_post
          iframe
          iexists j2 + W64 1, c2.2.1
          rw [hj21]
          iframe
          ipureintro; exact ⟨by word, by omega⟩
      · try wp_auto
        icases done_final b l K.p bufs L' HL'k HL'm Hnd hlenB $$ Hsd with ⟨%wb', %Hwb1, %Hwb2, Hso⟩
        icases Hm with ⟨%om'', Hm, %Hom''⟩
        try iapply HΦ
        iframe Hst Hdb Hf Hwa Hfo Hfd
        isplitl [Hpg Hpl']
        · iexists pl'; iframe
        isplitl [Hm]
        · iexists om''; iframe; ipureintro; exact Hom''
        iexists wb'
        isplitr
        · ipureintro; exact Hwb1
        ileft
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; exact Hwb2
        iexact Hso
end proof

end bbolt
end EtcdGrove
end Perennial
