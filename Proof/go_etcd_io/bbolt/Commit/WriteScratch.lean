module

public import Proof.go_etcd_io.bbolt.Tx__write
public import Proof.go_etcd_io.bbolt.Commit.WritePage
public import Proof.go_etcd_io.bbolt.Commit.PagesSort
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A key of the dirty pages, before `tx.write`'s first loop: its buffer, and its slots. -/
def wrKey (b : Loc) (p : GoString) (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (k : w64) :
    IProp GF :=
  iprop((∃ pl, ⌜pm !! k = some pl⌝ ∗ ∃ bs, ⌜bufs !! k = some bs⌝ ∗
      bytesPointsto pl (DFrac.own 1) bs) ∗
    (∃ pg, ⌜bufs !! k = some pg⌝ ∗
      [∗list] s ∈ List.range' k.toNat (1 + pageOverflow pg), slotAny b p s))

omit [GooseExts] in
theorem wr_drop_cons {α : Type} (l : List α) (n : Nat) (x : α) (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons hn]
  rw [List.getElem?_eq_getElem hn] at h
  rw [Option.some.inj h]

/-- At most `lim` distinct keys below `lim`. -/
theorem wr_keys_le (keys : List w64) (lim : Nat) (hnd : keys.Nodup)
    (h : ∀ k ∈ keys, k.toNat < lim) : keys.length ≤ lim := by
  have hnd' : (keys.map BitVec.toNat).Nodup :=
    List.Pairwise.map _ (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hnd
  have hsub : keys.map BitVec.toNat ⊆ List.range lim := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (h k hk)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simpa using this

set_option maxRecDepth 20000 in
theorem Tx.write.wp_proof' (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
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
  try wp_auto
  trace_state
  all_goals sorry

end proof

end bbolt
end EtcdGrove
end Perennial
