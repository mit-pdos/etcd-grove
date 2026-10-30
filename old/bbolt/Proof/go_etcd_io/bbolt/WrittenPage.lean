/-
The page `n.write(p)` leaves (`node.write.spec`), read back: its header, its elements' flags,
keys, values and children are the node's (`writtenPage_facts`), so it is a well-formed leaf or
branch page (`writtenPage_leafWF`, `writtenPage_branchWF`); and an inline bucket's value
`b.write()` returns (`writtenBucket`) is its header followed by such a page.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__write
public import Proof.go_etcd_io.bbolt.TreeStrict
public import Proof.go_etcd_io.bbolt.MetaInj

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The page `n.write(p)` leaves on the header `hdr` (no flags, no elements) and the bytes
`rest` after it, for a node (a leaf if `leaf`) with the inodes `ins`, keys `ks`, values `vs`. -/
def writtenPage (hdr : Page) (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) : List w8 :=
  pageBytes (Page.mk hdr.id' (if leaf then W16 2 else W16 1) (W16 (ins.length : Int)) hdr.overflow') ++
    (writtenElems leaf ks vs ins ++ kvBytes ks vs ++
      rest.drop (16 * ins.length + kvLen ks vs ins.length))

/-- What a node must satisfy for its page to be read back (`node.write.spec`'s conditions on
the inodes). -/
def writeOK (ks vs : List (List w8)) (ins : List Inode) : Prop :=
  ins.length < 65535 ∧ ks.length = ins.length ∧ vs.length = ins.length ∧
  (∀ i < ins.length, 0 < (ks.getD i []).length) ∧
  16 + 16 * ins.length + kvLen ks vs ins.length ≤ 2147483647

/-! ### Reading bytes out of concatenations -/

theorem pageBytes_len (p : Page) : (pageBytes p).length = 16 := by
  unfold pageBytes; simp [leBytes_length']


theorem bytesAt_app_r (A L : List w8) (k n : Nat) (h : A.length ≤ k) :
    bytesAt (A ++ L) k n = bytesAt L (k - A.length) n := by
  obtain ⟨d, rfl⟩ : ∃ d, k = A.length + d := ⟨k - A.length, by omega⟩
  unfold bytesAt; rw [← List.drop_drop, List.drop_left, Nat.add_sub_cancel_left]

theorem bytesAt_app_l (A L : List w8) (k n : Nat) (h : k + n ≤ A.length) :
    bytesAt (A ++ L) k n = bytesAt A k n := by
  unfold bytesAt
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem bytesAt_self (A : List w8) : bytesAt A 0 A.length = A := by
  unfold bytesAt; simp

theorem bytesAt_head (A L : List w8) : bytesAt (A ++ L) 0 A.length = A := by
  rw [bytesAt_app_l _ _ _ _ (by omega), bytesAt_self]

theorem leAt_bytesAt (pg : List w8) (off n : Nat) :
    leAt pg off n = (leInt (bytesAt pg off n)).toNat := rfl

theorem leAt_of_bytesAt (pg : List w8) (off n z : Nat) (hz : z < 2 ^ (8 * n))
    (h : bytesAt pg off n = leBytes n (z : Int)) : leAt pg off n = z := by
  rw [leAt_bytesAt, h, leInt_leBytes n z hz]; rfl

theorem bytesAt_quad (a b c d : List w8) :
    bytesAt (a ++ b ++ c ++ d) 0 a.length = a ∧
    bytesAt (a ++ b ++ c ++ d) a.length b.length = b ∧
    bytesAt (a ++ b ++ c ++ d) (a.length + b.length) c.length = c ∧
    bytesAt (a ++ b ++ c ++ d) (a.length + b.length + c.length) d.length = d := by
  simp only [List.append_assoc]
  refine ⟨bytesAt_head _ _, ?_, ?_, ?_⟩
  · rw [bytesAt_app_r _ _ _ _ (by omega), Nat.sub_self, bytesAt_head]
  · rw [bytesAt_app_r _ _ _ _ (by omega), show a.length + b.length - a.length = b.length by omega,
      bytesAt_app_r _ _ _ _ (by omega), Nat.sub_self, bytesAt_head]
  · rw [bytesAt_app_r _ _ _ _ (by omega),
      show a.length + b.length + c.length - a.length = b.length + c.length by omega,
      bytesAt_app_r _ _ _ _ (by omega), show b.length + c.length - b.length = c.length by omega,
      bytesAt_app_r _ _ _ _ (by omega), Nat.sub_self, bytesAt_self]

theorem bytesAt_triple (a b c : List w8) :
    bytesAt (a ++ b ++ c) 0 a.length = a ∧
    bytesAt (a ++ b ++ c) a.length b.length = b ∧
    bytesAt (a ++ b ++ c) (a.length + b.length) c.length = c := by
  have h := bytesAt_quad a b c []
  simp only [List.append_nil] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem toNat_lt8 (n : Nat) (x : BitVec (8 * n)) : x.toNat < 2 ^ (8 * n) := x.isLt

/-! ### Splitting the elements and the keys -/

theorem writtenUpTo_split (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) (i : Nat) :
    ∀ j, i < j → ∃ S, writtenUpTo leaf ks vs ins j = writtenUpTo leaf ks vs ins i ++
      (writtenElem leaf ins.length ks vs (ins.getD i (zero_val Inode)) i ++ S)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, h => by
    rw [writtenUpTo_succ]
    by_cases e : i = j
    · subst e; exact ⟨[], by simp⟩
    · obtain ⟨S, hS⟩ := writtenUpTo_split leaf ks vs ins i j (by omega)
      exact ⟨S ++ writtenElem leaf ins.length ks vs (ins.getD j (zero_val Inode)) j,
        by rw [hS]; simp⟩

theorem kvUpTo_split (ks vs : List (List w8)) (i : Nat) :
    ∀ j, i < j → j ≤ ks.length → j ≤ vs.length → ∃ S, kvUpTo ks vs j = kvUpTo ks vs i ++
      ((ks.getD i [] ++ vs.getD i []) ++ S)
  | 0, h, _, _ => absurd h (Nat.not_lt_zero _)
  | j + 1, h, hk, hv => by
    rw [kvUpTo_succ _ _ _ (by omega) (by omega)]
    by_cases e : i = j
    · subst e; exact ⟨[], by simp⟩
    · obtain ⟨S, hS⟩ := kvUpTo_split ks vs i j (by omega) (by omega) (by omega)
      exact ⟨S ++ (ks.getD j [] ++ vs.getD j []), by rw [hS]; simp⟩

theorem kvLen_succ_le (ks vs : List (List w8)) (i n : Nat) (hi : i < n) (hk : ks.length = n)
    (hv : vs.length = n) :
    kvLen ks vs i + ((ks.getD i []).length + (vs.getD i []).length) ≤ kvLen ks vs n := by
  rw [← kvLen_succ _ _ _ (by omega) (by omega)]; exact kvLen_mono _ _ _ _ hi

theorem kvBytes_length (ks vs : List (List w8)) (n : Nat) (hk : ks.length = n)
    (hv : vs.length = n) : (kvBytes ks vs).length = kvLen ks vs n := by
  rw [kvBytes_eq ks vs n hk hv, kvUpTo_length _ _ _ (by omega) (by omega)]

theorem w32_sub_toNat (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 32) :
    (W32 ((a : Int) - (b : Int))).toNat = a - b := by
  rw [BitVec.toNat_ofInt]; omega

theorem w32_toNat (a : Nat) (ha : a < 2 ^ 32) : (W32 (a : Int)).toNat = a := by
  rw [BitVec.toNat_ofInt]; omega

theorem w16_toNat (a : Nat) (ha : a < 2 ^ 16) : (W16 (a : Int)).toNat = a := by
  rw [BitVec.toNat_ofInt]; omega

/-! ### The written page -/

/-- The bytes of a written page at an element's offset (`o + w ≤ 16`) are its element's. -/
theorem writtenPage_elem (hdr : Page) (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) (i o w : Nat) (hi : i < ins.length) (ho : o + w ≤ 16) :
    bytesAt (writtenPage hdr leaf ks vs ins rest) (elemOff i + o) w =
      bytesAt (writtenElem leaf ins.length ks vs (ins.getD i (zero_val Inode)) i) o w := by
  unfold writtenPage
  have hE : (writtenElems leaf ks vs ins).length = 16 * ins.length := by
    rw [writtenElems_eq, writtenUpTo_length]
  rw [bytesAt_app_r _ _ _ _ (by rw [pageBytes_len]; unfold elemOff; omega), pageBytes_len,
    bytesAt_app_l _ _ _ _ (by rw [List.length_append, hE]; unfold elemOff; omega),
    bytesAt_app_l _ _ _ _ (by rw [hE]; unfold elemOff; omega)]
  obtain ⟨S, hS⟩ := writtenUpTo_split leaf ks vs ins i ins.length hi
  rw [writtenElems_eq, hS, bytesAt_app_r _ _ _ _ (by rw [writtenUpTo_length]; unfold elemOff; omega),
    writtenUpTo_length, show elemOff i + o - 16 - 16 * i = o by unfold elemOff; omega,
    bytesAt_app_l _ _ _ _ (by rw [writtenElem_length]; omega)]

/-- The bytes of a written page at a key's offset are its keys' and values'. -/
theorem writtenPage_kv (hdr : Page) (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) (h : writeOK ks vs ins) (i o w : Nat) (hi : i < ins.length)
    (ho : o + w ≤ (ks.getD i []).length + (vs.getD i []).length) :
    bytesAt (writtenPage hdr leaf ks vs ins rest) (dataOff ins.length ks vs i + o) w =
      bytesAt (ks.getD i [] ++ vs.getD i []) o w := by
  obtain ⟨hn, hk, hv, -, -⟩ := h
  unfold writtenPage
  have hE : (writtenElems leaf ks vs ins).length = 16 * ins.length := by
    rw [writtenElems_eq, writtenUpTo_length]
  have hK := kvBytes_length ks vs ins.length hk hv
  have hle := kvLen_succ_le ks vs i ins.length hi hk hv
  rw [bytesAt_app_r _ _ _ _ (by rw [pageBytes_len]; unfold dataOff; omega), pageBytes_len,
    bytesAt_app_l _ _ _ _ (by rw [List.length_append, hE, hK]; unfold dataOff; omega),
    bytesAt_app_r _ _ _ _ (by rw [hE]; unfold dataOff; omega), hE]
  obtain ⟨S, hS⟩ := kvUpTo_split ks vs i ins.length hi (by omega) (by omega)
  rw [kvBytes_eq ks vs ins.length hk hv, hS,
    bytesAt_app_r _ _ _ _ (by rw [kvUpTo_length _ _ _ (by omega) (by omega)]; unfold dataOff; omega),
    kvUpTo_length _ _ _ (by omega) (by omega),
    show dataOff ins.length ks vs i + o - 16 - 16 * ins.length - kvLen ks vs i = o by
      unfold dataOff; omega,
    bytesAt_app_l _ _ _ _ (by rw [List.length_append]; omega)]

theorem writtenPage_hdr (hdr : Page) (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) (o w : Nat) (ho : o + w ≤ 16) :
    bytesAt (writtenPage hdr leaf ks vs ins rest) o w =
      bytesAt (pageBytes (Page.mk hdr.id' (if leaf then W16 2 else W16 1) (W16 (ins.length : Int))
        hdr.overflow')) o w := by
  unfold writtenPage
  rw [bytesAt_app_l _ _ _ _ (by rw [pageBytes_len]; omega)]

theorem leafElem_at (e : leafPageElement) :
    bytesAt (leafElemBytes e) 0 4 = leBytes 4 e.flags'.toNat ∧
    bytesAt (leafElemBytes e) 4 4 = leBytes 4 e.pos'.toNat ∧
    bytesAt (leafElemBytes e) 8 4 = leBytes 4 e.ksize'.toNat ∧
    bytesAt (leafElemBytes e) 12 4 = leBytes 4 e.vsize'.toNat := by
  have h := bytesAt_quad (leBytes 4 e.flags'.toNat) (leBytes 4 e.pos'.toNat)
    (leBytes 4 e.ksize'.toNat) (leBytes 4 e.vsize'.toNat)
  simp only [leBytes_length', Nat.reduceAdd] at h
  unfold leafElemBytes; exact h

theorem branchElem_at (e : branchPageElement) :
    bytesAt (branchElemBytes e) 0 4 = leBytes 4 e.pos'.toNat ∧
    bytesAt (branchElemBytes e) 4 4 = leBytes 4 e.ksize'.toNat ∧
    bytesAt (branchElemBytes e) 8 8 = leBytes 8 e.pgid'.toNat := by
  have h := bytesAt_triple (leBytes 4 e.pos'.toNat) (leBytes 4 e.ksize'.toNat)
    (leBytes 8 e.pgid'.toNat)
  simp only [leBytes_length', Nat.reduceAdd] at h
  unfold branchElemBytes; exact h

theorem pageBytes_at (p : Page) :
    bytesAt (pageBytes p) 0 8 = leBytes 8 p.id'.toNat ∧
    bytesAt (pageBytes p) 8 2 = leBytes 2 p.flags'.toNat ∧
    bytesAt (pageBytes p) 10 2 = leBytes 2 p.count'.toNat ∧
    bytesAt (pageBytes p) 12 4 = leBytes 4 p.overflow'.toNat := by
  have h := bytesAt_quad (leBytes 8 p.id'.toNat) (leBytes 2 p.flags'.toNat)
    (leBytes 2 p.count'.toNat) (leBytes 4 p.overflow'.toNat)
  simp only [leBytes_length', Nat.reduceAdd] at h
  unfold pageBytes; exact h

theorem writtenPage_facts (hdr : Page) (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) (h : writeOK ks vs ins) :
    let pg := writtenPage hdr leaf ks vs ins rest
    16 + 16 * ins.length + kvLen ks vs ins.length ≤ pg.length ∧
    pg.length = 16 + 16 * ins.length + kvLen ks vs ins.length +
      (rest.length - (16 * ins.length + kvLen ks vs ins.length)) ∧
    pageId pg = uint.nat hdr.id' ∧
    pageFlags pg = (if leaf then leafPageFlag else branchPageFlag) ∧
    pageCount pg = ins.length ∧ pageOverflow pg = uint.nat hdr.overflow' ∧
    (leaf = true → ∀ i < ins.length,
      leafFlags pg i = uint.nat (ins.getD i (zero_val Inode)).flags' ∧
      leafKsize pg i = (ks.getD i []).length ∧ leafVsize pg i = (vs.getD i []).length ∧
      elemOff i + leafPos pg i = dataOff ins.length ks vs i ∧
      leafKey pg i = ks.getD i [] ∧ leafValue pg i = vs.getD i []) ∧
    (leaf = false → ∀ i < ins.length,
      branchKsize pg i = (ks.getD i []).length ∧
      elemOff i + branchPos pg i = dataOff ins.length ks vs i ∧
      branchKey pg i = ks.getD i [] ∧
      branchPgid pg i = uint.nat (ins.getD i (zero_val Inode)).pgid') := by
  intro pg
  have hok := h
  obtain ⟨hn, hk, hv, hkp, hbig⟩ := h
  have hE : (writtenElems leaf ks vs ins).length = 16 * ins.length := by
    rw [writtenElems_eq, writtenUpTo_length]
  have hK := kvBytes_length ks vs ins.length hk hv
  have hlen : pg.length = 16 + 16 * ins.length + kvLen ks vs ins.length +
      (rest.length - (16 * ins.length + kvLen ks vs ins.length)) := by
    show (writtenPage hdr leaf ks vs ins rest).length = _
    unfold writtenPage
    simp only [List.length_append, pageBytes_len, hE, hK, List.length_drop]
    omega
  obtain ⟨H0, H8, H10, H12⟩ := pageBytes_at (Page.mk hdr.id' (if leaf then W16 2 else W16 1)
    (W16 (ins.length : Int)) hdr.overflow')
  have hhdr := fun o w ho => writtenPage_hdr hdr leaf ks vs ins rest o w ho
  -- an element's and a key's offsets
  have hdo : ∀ i < ins.length, elemOff i ≤ dataOff ins.length ks vs i ∧
      dataOff ins.length ks vs i + (ks.getD i []).length + (vs.getD i []).length ≤
        16 + 16 * ins.length + kvLen ks vs ins.length := by
    intro i hi
    have := kvLen_succ_le ks vs i ins.length hi hk hv
    unfold elemOff dataOff; omega
  refine ⟨by omega, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pageId; exact leAt_of_bytesAt _ _ _ _ (toNat_lt8 8 _) (by rw [hhdr 0 8 (by omega)]; exact H0)
  · unfold pageFlags
    rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 2 _) (by rw [hhdr 8 2 (by omega)]; exact H8)]
    cases leaf <;> rfl
  · unfold pageCount
    rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 2 _) (by rw [hhdr 10 2 (by omega)]; exact H10)]
    exact w16_toNat _ (by omega)
  · unfold pageOverflow
    exact leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [hhdr 12 4 (by omega)]; exact H12)
  · rintro rfl i hi
    obtain ⟨hd1, hd2⟩ := hdo i hi
    have hel := fun o w ho => writtenPage_elem hdr true ks vs ins rest i o w hi ho
    simp only [writtenElem, if_true] at hel
    obtain ⟨E0, E4, E8, E12⟩ := leafElem_at (leafPageElement.mk (ins.getD i (zero_val Inode)).flags'
      (W32 ((dataOff ins.length ks vs i : Int) - (elemOff i : Int)))
      (W32 ((ks.getD i []).length : Int)) (W32 ((vs.getD i []).length : Int)))
    have hF : leafFlags pg i = uint.nat (ins.getD i (zero_val Inode)).flags' := by
      unfold leafFlags
      exact leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [← hel 0 4 (by omega)] at E0; simpa using E0)
    have hP : leafPos pg i = dataOff ins.length ks vs i - elemOff i := by
      unfold leafPos
      rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [← hel 4 4 (by omega)] at E4; exact E4)]
      exact w32_sub_toNat _ _ hd1 (by omega)
    have hKs : leafKsize pg i = (ks.getD i []).length := by
      unfold leafKsize
      rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [← hel 8 4 (by omega)] at E8; exact E8)]
      exact w32_toNat _ (by omega)
    have hVs : leafVsize pg i = (vs.getD i []).length := by
      unfold leafVsize
      rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [← hel 12 4 (by omega)] at E12; exact E12)]
      exact w32_toNat _ (by omega)
    have hpos : elemOff i + leafPos pg i = dataOff ins.length ks vs i := by rw [hP]; omega
    refine ⟨hF, hKs, hVs, hpos, ?_, ?_⟩
    · unfold leafKey
      rw [hpos, hKs, show dataOff ins.length ks vs i = dataOff ins.length ks vs i + 0 from rfl,
        writtenPage_kv hdr true ks vs ins rest hok i 0 _ hi (by omega), bytesAt_head]
    · unfold leafValue
      rw [hpos, hKs, hVs, writtenPage_kv hdr true ks vs ins rest hok i _ _ hi (by omega),
        bytesAt_app_r _ _ _ _ (by omega), Nat.sub_self, bytesAt_self]
  · rintro rfl i hi
    obtain ⟨hd1, hd2⟩ := hdo i hi
    have hel := fun o w ho => writtenPage_elem hdr false ks vs ins rest i o w hi ho
    simp only [writtenElem, Bool.false_eq_true, if_false] at hel
    obtain ⟨E0, E4, E8⟩ := branchElem_at (branchPageElement.mk
      (W32 ((dataOff ins.length ks vs i : Int) - (elemOff i : Int)))
      (W32 ((ks.getD i []).length : Int)) (ins.getD i (zero_val Inode)).pgid')
    have hP : branchPos pg i = dataOff ins.length ks vs i - elemOff i := by
      unfold branchPos
      rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [← hel 0 4 (by omega), Nat.add_zero] at E0; exact E0)]
      exact w32_sub_toNat _ _ hd1 (by omega)
    have hKs : branchKsize pg i = (ks.getD i []).length := by
      unfold branchKsize
      rw [leAt_of_bytesAt _ _ _ _ (toNat_lt8 4 _) (by rw [← hel 4 4 (by omega)] at E4; exact E4)]
      exact w32_toNat _ (by omega)
    have hpos : elemOff i + branchPos pg i = dataOff ins.length ks vs i := by rw [hP]; omega
    refine ⟨hKs, hpos, ?_, ?_⟩
    · unfold branchKey
      rw [hpos, hKs, show dataOff ins.length ks vs i = dataOff ins.length ks vs i + 0 from rfl,
        writtenPage_kv hdr false ks vs ins rest hok i 0 _ hi (by omega), bytesAt_head]
    · unfold branchPgid
      exact leAt_of_bytesAt _ _ _ _ (toNat_lt8 8 _) (by rw [← hel 8 8 (by omega)] at E8; exact E8)

/-- A written leaf page is well-formed if its keys increase. -/
theorem writtenPage_leafWF (hdr : Page) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) (h : writeOK ks vs ins)
    (hs : ∀ i j, i < j → j < ins.length → go.GoStringLt (ks.getD i []) (ks.getD j [])) :
    leafWF (writtenPage hdr true ks vs ins rest) (writtenPage hdr true ks vs ins rest).length := by
  obtain ⟨F1, -, -, -, Fc, -, Fl, -⟩ := writtenPage_facts hdr true ks vs ins rest h
  obtain ⟨hn, hk, hv, -, hbig⟩ := h
  refine ⟨Nat.le_refl _, by rw [Fc]; unfold elemOff; omega, fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [Fc] at hi
    obtain ⟨-, hKs, hVs, hpos, -, -⟩ := Fl rfl i hi
    have := kvLen_succ_le ks vs i ins.length hi hk hv
    rw [hKs, hVs]
    unfold dataOff at hpos
    constructor <;> omega
  · rw [Fc] at hj
    rw [(Fl rfl i (by omega)).2.2.2.2.1, (Fl rfl j hj).2.2.2.2.1]
    exact hs i j hij hj

/-- A written branch page is well-formed if it has an element, its keys increase and its
children are below `hwm`. -/
theorem writtenPage_branchWF (hdr : Page) (ks vs : List (List w8)) (ins : List Inode)
    (rest : List w8) (hwm : Nat) (h : writeOK ks vs ins) (hn : 0 < ins.length)
    (hs : ∀ i j, i < j → j < ins.length → go.GoStringLt (ks.getD i []) (ks.getD j []))
    (hc : ∀ i < ins.length, uint.nat (ins.getD i (zero_val Inode)).pgid' < hwm) :
    branchWF (writtenPage hdr false ks vs ins rest) (writtenPage hdr false ks vs ins rest).length
      hwm := by
  obtain ⟨F1, -, -, -, Fc, -, -, Fb⟩ := writtenPage_facts hdr false ks vs ins rest h
  obtain ⟨hn', hk, hv, -, hbig⟩ := h
  refine ⟨by rw [Fc]; exact hn, Nat.le_refl _, by rw [Fc]; unfold elemOff; omega,
    fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [Fc] at hi
    obtain ⟨hKs, hpos, -, hpg⟩ := Fb rfl i hi
    have := kvLen_succ_le ks vs i ins.length hi hk hv
    rw [hKs, hpg]
    unfold dataOff at hpos
    exact ⟨by omega, by omega, hc i hi⟩
  · rw [Fc] at hj
    rw [(Fb rfl i (by omega)).2.2.1, (Fb rfl j hj).2.2.1]
    exact hs i j hij hj

/-- An inline bucket's value `b.write()` returns: its root and its page. -/
theorem writtenBucket_facts (ib : InBucket) (ks vs : List (List w8)) (ins : List Inode) :
    16 ≤ (writtenBucket ib true ks vs ins).length ∧
    inBucketRoot (writtenBucket ib true ks vs ins) = uint.nat ib.root' ∧
    inlinePage (writtenBucket ib true ks vs ins) =
      writtenPage (Page.mk (W64 0) (W16 0) (W16 0) (W32 0)) true ks vs ins [] := by
  have hib : (inBucketBytes ib).length = 16 := by unfold inBucketBytes; simp [leBytes_length']
  unfold writtenBucket
  simp only [List.append_assoc]
  refine ⟨by simp [hib], ?_, ?_⟩
  · unfold inBucketRoot
    apply leAt_of_bytesAt _ _ _ _ (toNat_lt8 8 _)
    rw [bytesAt_app_l _ _ _ _ (by omega)]
    unfold inBucketBytes
    have := bytesAt_head (leBytes 8 ib.root'.toNat) (leBytes 8 ib.sequence'.toNat)
    rw [leBytes_length'] at this
    exact this
  · unfold inlinePage writtenPage writtenHdr
    rw [show (16 : Nat) = (inBucketBytes ib).length from hib.symm, List.drop_left]
    simp

end pure

end bbolt
end EtcdGrove
end Perennial
