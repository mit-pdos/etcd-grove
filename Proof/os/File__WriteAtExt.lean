/-
The proof of `os.File.WriteAt.specExt` (`Spec/os/File__WriteAt.lean`): any write, past the end of the
file and in chunks of at most 1 GiB (`Proof/os/WriteChunks.lean`). Split from `File__WriteAt.lean`
(2026-11-15, notes/wal-lean-integration.md), so that the WAL's proofs, which use `specLong`
(`Proof/os/WriteLong.lean`), do not wait on it: under the per-byte extension's page cache known zero
(`OsMeta.cz`, raised by a write that lands whole, `pwCz`) the post is `specLong`'s `os.pwPostE`, the
page cache known zero as the last chunk that landed whole left it (`pwPostE_chunk`; ledger 2026-11-15,
restated as specLong's post).
-/
module

public import Proof.os.ForLoeb
public import Proof.os.File__WriteAt
public import Proof.os.WriteChunks
public import Proof.os.WriteLongStep
public import GooseLang.Ext.Fs.NoErrSpecsOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-! ## Any write: past the end of the file, and in chunks of at most 1 GiB -/

theorem wa_wp_call1_gen (F : val) (n0 : w64) (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n = n0⌝ -∗ WP (App (Val F) (Val #n)) {{ Φ }}) ⊢
    WP (App (Val F) (Val #n0)) {{ Φ }} := by
  iintro H
  iapply H
  ipureintro; rfl

theorem wa_sintZ_W64 (x : Nat) (h : x < 2 ^ 63) : sint.Z (W64 x) = x := by
  simp only [sint.Z, W64]; rw [BitVec.toInt_ofInt, Int.bmod]; split <;> omega

theorem wa_sintNat_W64 (x : Nat) (h : x < 2 ^ 63) : sint.nat (W64 x) = x := by
  simp only [sint.nat]; rw [show (W64 x).toInt = x from wa_sintZ_W64 x h]; simp

theorem wa_W64_add (a b : Nat) : W64 a + W64 b = W64 (a + b : Nat) := by
  show BitVec.ofInt 64 (a : Int) + BitVec.ofInt 64 (b : Int) = BitVec.ofInt 64 ((a + b : Nat) : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem wa_W64_sub (a b : Nat) (_ha : a < 2 ^ 63) (h : b ≤ a) :
    W64 a - W64 b = W64 (a - b : Nat) := by
  show BitVec.ofInt 64 (a : Int) - BitVec.ofInt 64 (b : Int) = BitVec.ofInt 64 ((a - b : Nat) : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem wa_W64_inj (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    W64 a = W64 b ↔ a = b := by
  constructor
  · intro h; have := congrArg sint.Z h; rw [wa_sintZ_W64 a ha, wa_sintZ_W64 b hb] at this; omega
  · intro h; rw [h]

theorem wa_toNat_add_W64 (off : w64) (nn : Nat) (h : off.toNat + nn < 2 ^ 63) :
    (off + W64 nn).toNat = off.toNat + nn := by
  rw [BitVec.toNat_add]
  have : (W64 nn).toNat = nn := by
    simp only [W64]; rw [BitVec.toNat_ofInt]; omega
  rw [this]; exact Nat.mod_eq_of_lt (by omega)

/-- `pwCzE_step` for a write anywhere (`off` past the size too): the announcement from
`min off size` raises the zeros known to `off + A` as one from `off` does. -/
theorem pwCzE_stepG (m : OsMeta) (off A j E nn A' k : Nat) (hA0 : 0 < A)
    (hA : A ≤ A') (hnA : nn < A') (hE : E ≤ A') :
    pwCz (os.pwPostE m off A j E) (off + nn) (A' - nn) k =
      pwCz m off (if k = A' - nn then A' else E) (if k = A' - nn then A' else E) := by
  have hz1 : (os.pwPostE m off A j E).zf = m.zf.map (fun z => max z (off + A)) := by
    simp only [os.pwPostE, pwPost, announce_zf]
    cases m.zf with
    | none => rfl
    | some z => simp only [Option.map_some, show min off m.size < off + A by omega, if_true]
  have hcz1 : (os.pwPostE m off A j E).cz = pwCz m off E E := rfl
  cases hzf : m.zf with
  | none =>
    rw [pwCz_none _ _ _ _ (by rw [hz1, hzf]; rfl), hcz1, pwCz_none _ _ _ _ hzf, pwCz_none _ _ _ _ hzf]
  | some z =>
    rw [pwCz_some _ _ _ _ (max z (off + A)) (by rw [hz1, hzf]; rfl), hcz1,
      show off + nn + (A' - nn) = off + A' by omega]
    by_cases hk : k = A' - nn
    · rw [if_pos hk, pwCz_some m off A' A' z hzf]
      by_cases hzA : z ≤ off + A'
      · rw [if_pos ⟨by omega, hk, by omega⟩, if_pos ⟨by omega, rfl, hzA⟩]
        have := pwCz_le_raise m off E A' hE z hzf hzA
        have := le_pwCz m off E E
        omega
      · rw [if_neg (by omega), if_neg (by omega), pwCz_some m off E E z hzf, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg hk]

/-- A write of `cs` bytes at `off + nn` (the chunk) over the `OsMeta` a write of `j` bytes at
`off` left, whose first steps announced `[min off size, off + a)` and whose last whole chunk ended at
`E`, leaves the `OsMeta` of a write of `max j (nn + k)` bytes whose first steps announced
`[min off size, off + nn + cs)`, whose last whole chunk is this one if it landed whole (`pwPostE_step`
for a write anywhere). -/
theorem pwPostE_chunk (m : OsMeta) (off a nn j E cs k : Nat) (hml : m.lo ≤ m.size) (hnn : nn ≤ j)
    (hja : j ≤ a) (ha : a ≤ nn + cs) (ha0 : 0 < a) (hk : k ≤ cs) (hcs0 : 0 < cs) (hE : E ≤ j) :
    pwPost (os.pwPostE m off a j E) (off + nn) cs k =
      os.pwPostE m off (nn + cs) (max j (nn + k)) (if k = cs then nn + cs else E) := by
  have hS1 : m.size ≤ pwSize m.size off j := by unfold pwSize; split <;> omega
  have hS2 : 0 < j → off + j ≤ pwSize m.size off j := by unfold pwSize; split <;> omega
  have hS3 : j = 0 → pwSize m.size off j = m.size := by intro h; simp [pwSize, h]
  have hlo' : min off m.size ≤ min (off + nn) (pwSize m.size off j) := by omega
  have hlo'' : min (off + nn) (pwSize m.size off j) ≤ off + a := by omega
  have hsz : pwSize (pwSize m.size off j) (off + nn) k = pwSize m.size off (max j (nn + k)) :=
    pwSize_chunk _ _ _ _ _ hnn
  have hszE : (os.pwPostE m off a j E).size = pwSize m.size off j := rfl
  apply os.osMeta_eq
  · show pwSize (os.pwPostE m off a j E).size (off + nn) k = pwSize m.size off (max j (nn + k))
    rw [hszE]; exact hsz
  · simp only [pwPost, os.pwPostE, announce_lo]; unfold pwSize; split <;> omega
  · simp only [pwPost, os.pwPostE, announce_hi]; unfold pwSize; split <;> omega
  · simp only [pwPost, os.pwPostE, announce_maps]
  · simp only [pwPost, os.pwPostE, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + a ≤ min off m.size by omega,
        show ¬ off + nn + cs ≤ min (off + nn) (pwSize m.size off j) by omega,
        show ¬ off + (nn + cs) ≤ min off m.size by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, os.pwPostE, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + a ≤ min off m.size by omega,
        show ¬ off + nn + cs ≤ min (off + nn) (pwSize m.size off j) by omega,
        show ¬ off + (nn + cs) ≤ min off m.size by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, os.pwPostE, announce_zf, Option.map_map]
    cases m.zf with
    | none => rfl
    | some z =>
      simp only [Option.map_some, Function.comp, Option.some.injEq,
        show min off m.size < off + a by omega,
        show min (off + nn) (pwSize m.size off j) < off + nn + cs by omega,
        show min off m.size < off + (nn + cs) by omega, if_true]
      omega
  · apply GMap.ext; intro b
    simp only [pwPost, os.pwPostE, announce_tc, announce_size, inRange, Bool.and_eq_true,
      decide_eq_true_eq]
    (repeat' split) <;> first | rfl | omega
  · simp [pwPost, os.pwPostE]
  · have h := pwCzE_stepG m off a j E nn (nn + cs) k ha0 ha (by omega) (by omega)
    rw [show nn + cs - nn = cs by omega] at h
    exact h
  · simp [pwPost, os.pwPostE]

/-- The bytes a write has landed after one more attempt, of the chunk `c` from `nn`, are a cut. -/
theorem waCut_step (off len nn j c k : Nat) (hj0 : os.WaCut off len j)
    (hcn : (off + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0)
    (hc : c = min (len - nn) 0x40000000) (hk : k ≤ c) (hnl : nn < len) (hnj : nn ≤ j)
    (hpc0 : PwCut (off + nn) c k) : os.WaCut off len (max j (nn + k)) := by
  obtain ⟨hj, hjm⟩ := hj0
  obtain ⟨hpc, hpm⟩ := hpc0
  refine ⟨?_, ?_⟩
  rotate_left
  · rcases Nat.le_total j (nn + k) with h | h
    · rw [Nat.max_eq_right h]; omega
    · rw [Nat.max_eq_left h]; exact hjm
  unfold osPageSize at *
  rcases Nat.le_total j (nn + k) with h | h
  · rw [Nat.max_eq_right h]
    rcases hpc with h0 | h0 | h0
    · subst h0; rcases hcn with h1 | h1
      · left; right; right; simpa using h1
      · right; simpa using h1
    · by_cases hcl : len - nn ≤ 0x40000000
      · left; right; left; omega
      · rcases hcn with h1 | h1
        · left; right; right; omega
        · right; omega
    · left; right; right; rw [← Nat.add_assoc]; exact h0
  · rw [Nat.max_eq_left h]; exact hj

/-- After an attempt that wrote some of its chunk and succeeded, the next starts on a page boundary
or a chunk boundary. -/
theorem waCut_short (off len nn c k : Nat)
    (hcn : (off + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0)
    (hc : c = min (len - nn) 0x40000000) (hk0 : 0 < k) (hfull : nn + k ≠ len) (hk : k ≤ c)
    (hnl : nn < len) (hpc : PwCut (off + nn) c k) :
    (off + (nn + k)) % osPageSize = 0 ∨ (nn + k) % 0x40000000 = 0 := by
  unfold PwCut osPageSize at *
  rcases hpc with h0 | h0 | h0
  · omega
  · rcases hcn with h1 | h1
    · left; omega
    · right; omega
  · left; rw [← Nat.add_assoc]; exact h0

/-- The split of the bytes `WriteAt`'s loop has read at the chunk's start, in a lemma of its own: `omega` in
the loop's context took 257s (profiled 2026-11-17). -/
theorem wa_take_split (o oc s P L yl nn : Nat) (hocN : oc = o + nn) (hnl : nn < L) (hsz : s ≤ P)
    (hyl : yl = min (o + L) P - min o s) :
    min oc P = min o s + min (min oc P - min o s) yl := by
  omega

/-- The bounds of a chunk the loop of `WriteAt` wrote (`nn + c`, `c` the chunk's length capped at
`2^30`), in a lemma of its own: `omega` in the loop's context, with the invariant's disjunctions,
took 1318s (profiled 2026-11-17). -/
theorem wa_chunk_bounds (j nn k c len : Nat) (hjc : j ≤ nn + c) (hk : k ≤ c) (hcn : nn + c ≤ len)
    (hcdef : c = min (len - nn) 1073741824) (hc0 : 0 < c) :
    max j (nn + k) ≤ nn + c ∧ nn + c ≤ len ∧ min len 0x40000000 ≤ nn + c ∧ 0 < nn + c := by
  omega

set_option maxHeartbeats 4000000 in
/-- **`WriteAt.specExt`, generic in its `pwrite`s' errnos** (as `wp_proofQ`): a failure only with
an errno `e ≠ 0` with `Pe e`, over a semantics whose `pwrite` ends at an offset below `B` return an
errno with `Pe` (`hpost`), for a write ending by `B`. `specExt` is its instance (session S6 removed the unused
`specExtNoErr`, errno 0 below `maxBytes`). -/
theorem os.File.WriteAt.wp_proofExtQ (B : Nat) (Pe : Nat → w64 → Prop)
    (hpost : ∀ (t : Nat) (p : Ino) (o : Nat) (dt : List w8) (m : OsMeta) (xs : List ByteG) (n : Nat)
      (Φ : val → IProp GF), o < B →
      ⊢ pwTokG (GF := GF) t p o dt m xs n -∗
        (pwTokG (GF := GF) t p o dt m xs n -∗
          WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t)))
            {{ r, ⌜∀ r0 (e : w64), r = PairV r0 (#e) → Pe o e⌝ -∗ Φ r }}) -∗
        WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }})
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hbig : off.toNat + data.length < 2 ^ 63)
    (hn : 0 < data.length)
    (hxl : xs.length = min (off.toNat + data.length) m.size - min off.toNat m.size)
    (hB : off.toNat + data.length ≤ B) :
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino (min off.toNat m.size) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (min off.toNat m.size) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (j a E : Nat) (ys : List ByteG),
        ⌜j ≤ a ∧ a ≤ data.length ∧ min data.length 0x40000000 ≤ a ∧ E ≤ j ∧ (j = a → E = a) ∧
          ys.map Prod.fst = pwValsG m.size off.toNat data j xs ∧
          os.WaCut off.toNat data.length j ∧
          ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
           (n = W64 0 ∧ err ≠ interface.nil ∧
             ∃ (o : Nat) (e : w64), o ≤ off.toNat + j ∧ Pe o e ∧ e ≠ W64 0))⌝ ∗
        osMeta d.ino (DFrac.own 1) (os.pwPostE m off.toNat a j E) ∗
        osBytes d.ino (min off.toNat m.size) (DFrac.own 1) ys ∗
        mcellsAny m.maps (min off.toNat m.size) (off.toNat + data.length) ∗
      fmtErrorOkOrNil err }} := by
  have hfin : ∀ (t : Nat) (p : Ino) (o : Nat) (dt : List w8) (m : OsMeta) (xs : List ByteG) (n : Nat)
      (Φ : val → IProp GF), o < B →
      ⊢ osInv (GF := GF) -∗ pwTokG (GF := GF) t p o dt m xs n -∗
        (∀ k : Nat, ∀ e : w64, ∀ zs : List Cands,
          ⌜k ≤ dt.length ∧ ((k = dt.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
            zs.length = pwSize m.size o k - m.size ∧
            ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ -∗
          ⌜PwCut o dt.length k⌝ -∗ ⌜Pe o e⌝ -∗
          osMeta (GF := GF) p (DFrac.own 1) (pwPost m o dt.length k) -∗
          osBytes (GF := GF) p (min o m.size) (DFrac.own 1) (pwBytesG m.size o dt k n xs zs) -∗
          mcells (GF := GF) m.maps (min o m.size) (o + dt.length) (pwCellG m.size o dt k xs) -∗
          Φ (PairV (#(W64 k)) (#e))) -∗
        WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
    intro t p o dt m xs n Φ hoB
    iintro #Hinv Ht HΦ
    iapply hpost t p o dt m xs n Φ hoB $$ Ht
    iintro Ht
    iapply wp_osPWriteFinishG t p o dt m xs n CoPset.subseteq_top _ $$ Hinv Ht
    iintro %k %e %zs %h1 %h2 Hm Hbs Hc %hP
    iapply HΦ $$ %k %e %zs %h1 %h2 %(hP _ _ rfl) Hm Hbs Hc
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hsys⟩, Hsl, Hosfd, Hm, Hbs, Hc⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwf
  try wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  try wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  try wp_auto
  try simp only [os.modelMaxRW]
  obtain ⟨nw, hnw⟩ : ∃ nw : w64, nw = W64 0 := ⟨_, rfl⟩
  ihave Hnnp : (nn_ptr ↦ nw : IProp GF) $$ [nn]
  · rw [hnw]; iexact nn
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  obtain ⟨nn, hnn0⟩ : ∃ nn : Nat, nn = 0 := ⟨_, rfl⟩
  have hnw' : nw = W64 nn := by rw [hnw, hnn0]; rfl
  clear hnw
  -- the invariant: the file as a write of the first `j ≥ nn` bytes left it, whose attempts
  -- announced `[min off size, off + a)`
  obtain ⟨j, hj0⟩ : ∃ j : Nat, j = 0 := ⟨_, rfl⟩
  obtain ⟨a, ha0⟩ : ∃ a : Nat, a = 0 := ⟨_, rfl⟩
  obtain ⟨E, hE0⟩ : ∃ E : Nat, E = 0 := ⟨_, rfl⟩
  obtain ⟨mj, hmj⟩ : ∃ mj, mj = m := ⟨_, rfl⟩
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) m ⊢ osMeta d.ino (DFrac.own 1) mj by
    rw [hmj]) $$ Hm
  obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
  ihave Hbs := (show osBytes (GF := GF) d.ino (min off.toNat m.size) (DFrac.own 1) xs ⊢
    osBytes d.ino (min off.toNat m.size) (DFrac.own 1) ys by rw [hy]) $$ Hbs
  have hj : j ≤ data.length := by omega
  have hnj : nn ≤ j := by omega
  have hnl : nn < data.length := by omega
  have hys : ys.map Prod.fst = pwValsG m.size off.toNat data j xs := by
    rw [hy, hj0, pwValsG_zero _ _ _ _ hxl]
  have hinv : (j = 0 ∧ nn = 0 ∧ mj = m ∧ E = 0) ∨
      (mj = os.pwPostE m off.toNat a j E ∧ E ≤ j ∧ (j = a → E = a) ∧ m.lo ≤ m.size ∧ j ≤ a ∧
        a ≤ data.length ∧ min data.length 0x40000000 ≤ a ∧ a ≤ nn + 0x40000000 ∧ 0 < a) :=
    .inl ⟨hj0, hnn0, hmj, hE0⟩
  have hcj : os.WaCut off.toNat data.length j := ⟨Or.inl (Or.inl hj0), Or.inl hj0⟩
  have hcn : (off.toNat + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0 := by
    right; rw [hnn0]
  clear hmj hy hj0 hnn0 ha0 hE0
  wp_for_bind
  iloeb as IH generalizing %nw %nn %j %a %E %mj %ys %hnw' %hj %hnj %hnl %hys %hinv %hcj %hcn
    Hm Hbs Hc Hosfd Hsl Hfd HΦ
  wp_for_step
  subst hnw'
  -- one attempt, of the chunk `[nn, nn + c)`
  have hmsz : mj.size = pwSize m.size off.toNat j := by
    rcases hinv with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -⟩
    · simp [pwSize]
    · rfl
  have hmaps : mj.maps = m.maps := by
    rcases hinv with ⟨-, -, rfl, -⟩ | ⟨rfl, -⟩ <;> simp [os.pwPostE, pwPost]
  try wp_auto
  have hlZ : sint.Z (sl.len - W64 ↑nn) = ↑(data.length - nn) := by
    rw [hsln, wa_W64_sub _ _ (by omega) (by omega), wa_sintZ_W64 _ (by omega)]
  have h30 : sint.Z (W64 1073741824) = 1073741824 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (data.length - nn) 1073741824 := ⟨_, rfl⟩
  have hcn' : nn + c ≤ data.length := by omega
  have hc0 : 0 < c := by omega
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∗ (max_ptr ↦ W64 ↑(nn + c) : IProp GF) ∗
      (nn_ptr ↦ W64 ↑nn : IProp GF)))
    at (if: _ then _ else _) with [max Hnnp] as ⟨%Hv, max, Hnnp⟩
  · by_cases hbig' : 1073741824 < data.length - nn
    · rw [decide_eq_true (by rw [hlZ, h30]; omega)]
      try wp_auto
      isplitr; · ipureintro; rfl
      rw [show (W64 ↑(nn + c) : w64) = W64 ↑nn + W64 1073741824 by
        rw [show (1073741824 : Int) = ((1073741824 : Nat) : Int) from rfl, wa_W64_add]; congr 2; omega]
      iframe
    · rw [decide_eq_false (by rw [hlZ, h30]; omega)]
      try wp_auto
      isplitr; · ipureintro; rfl
      rw [show (W64 ↑(nn + c) : w64) = sl.len by rw [hsln]; congr 2; omega]
      iframe
  subst Hv
  try wp_auto
  have hsb : 0 ≤ sint.Z (W64 ↑nn) ∧ sint.Z (W64 ↑nn) ≤ sint.Z (W64 ↑(nn + c)) ∧
      sint.Z (W64 ↑(nn + c)) ≤ sint.Z sl.cap := by
    rw [wa_sintZ_W64 _ (by omega), wa_sintZ_W64 _ (by omega)]; omega
  rw [if_pos hsb]
  have hsb2 : 0 ≤ sint.Z (W64 ↑nn) ∧ sint.Z (W64 ↑nn) ≤ sint.Z (W64 ↑(nn + c)) ∧
      sint.Z (W64 ↑(nn + c)) ≤ sint.Z sl.len := by
    rw [wa_sintZ_W64 _ (by omega), wa_sintZ_W64 _ (by omega)]; omega
  icases (ownSlice_slice (W64 ↑nn) (W64 ↑(nn + c)) sl dqs data hsb2).1 $$ Hsl with
    ⟨Hsl1, Hsl2, Hsl3⟩
  wp_apply wp_bytes_to_string _ _ dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_slice (W64 ↑nn) (W64 ↑(nn + c)) sl dqs data hsb2).2 $$ [Hsl1 Hsl2 Hsl3]
  · iframe
  generalize hcd0 : subslice (sint.nat (W64 ↑nn)) (sint.nat (W64 ↑(nn + c))) data = cd
  have hcd : cd = (data.drop nn).take c := by
    rw [← hcd0, wa_sintNat_W64 _ (by omega), wa_sintNat_W64 _ (by omega)]
    simp only [subslice, List.drop_take]; congr 1; omega
  have hcdl : cd.length = c := by rw [hcd]; simp; omega
  have hcdne : cd ≠ [] := by intro h; rw [h] at hcdl; simp at hcdl; omega
  clear hcd0
  have hocN : (off + W64 ↑nn).toNat = off.toNat + nn := wa_toNat_add_W64 off nn (by omega)
  have hocI : 0 ≤ (off + W64 ↑nn).toInt := by
    have := BitVec.toInt_eq_toNat_cond (off + W64 ↑nn); split at this <;> omega
  generalize hoc : off + W64 ↑nn = oc at hocN hocI ⊢
  -- the bytes and cells the attempt takes
  have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) -
      min off.toNat m.size := by
    have := congrArg List.length hys; simp only [List.length_map, pwValsG_length] at this; exact this
  have hsz : m.size ≤ pwSize m.size off.toNat j := by unfold pwSize; split <;> omega
  icases osBytes_split3_range d.ino (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
      (min (oc.toNat + c) (pwSize m.size off.toNat j)) (DFrac.own 1) ys
      (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min off.toNat m.size)
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))
      (by omega) (by omega) (by omega) (by omega) (by omega) $$ Hbs with ⟨Hbs1, Hbs2, Hbs3⟩
  icases mcellsAny_split m.maps (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
    (off.toNat + data.length) (by omega) (by omega) $$ Hc with ⟨Hc1, Hc23⟩
  icases mcellsAny_split m.maps (min oc.toNat (pwSize m.size off.toNat j)) (oc.toNat + cd.length)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc23 with ⟨Hc2, Hc3⟩
  ihave Hbs2 := (show osBytes (GF := GF) d.ino (min oc.toNat (pwSize m.size off.toNat j))
      (DFrac.own 1) ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))) ⊢
      osBytes d.ino (min oc.toNat mj.size) (DFrac.own 1)
        ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
          (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))) by
    rw [hmsz]) $$ Hbs2
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (min oc.toNat (pwSize m.size off.toNat j))
      (oc.toNat + cd.length) ⊢ mcellsAny mj.maps (min oc.toNat mj.size) (oc.toNat + cd.length) by
    rw [hmsz, hmaps]) $$ Hc2
  try wp_auto
  wp_stub os.fsPWrite.impl
  wp_apply wp_osPWriteStartG fd oc cd dq d mj
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
    CoPset.subseteq_top hwr hocI hcdne (by
      simp only [List.length_take, List.length_drop, hcdl, hmsz]
      omega)
    $$ Hinv Hosfd Hm Hbs2 Hc2 as %t %nst %hst Hosfd Ht
  have hmlo : mj.lo ≤ mj.size := hst.2.2.2
  wp_apply hfin t d.ino oc.toNat cd mj
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
    nst _ (by omega) $$ Hinv Ht as %k %e %zs %hke %hpc %hPe Hm Hbs2 Hc2
  obtain ⟨hk, hke, -, -⟩ := hke
  rw [hcdl] at hk
  rw [hcdl, hocN] at hpc
  -- the file as a write of the first `max j (nn + k)` bytes left it, announced up to `nn + c`
  have hml : m.lo ≤ m.size := by
    rcases hinv with ⟨-, -, rfl, -⟩ | ⟨-, -, -, h, -⟩
    · exact hmlo
    · exact h
  have hE' : (if k = c then nn + c else E) ≤ max j (nn + k) ∧
      (max j (nn + k) = nn + c → (if k = c then nn + c else E) = nn + c) := by
    have hEj : E ≤ j ∧ (j = a → E = a) ∧ (j = 0 ∨ (j ≤ a ∧ a ≤ nn + c)) := by
      rcases hinv with ⟨hj0', -, -, hE0'⟩ | ⟨-, hEj, hja', -, hja, hal, -, ha, -⟩
      · omega
      · exact ⟨hEj, hja', Or.inr ⟨hja, by omega⟩⟩
    split <;> omega
  have hjc : j ≤ nn + c := by
    rcases hinv with ⟨hj0', -⟩ | ⟨-, -, -, -, hja, hal, -, ha, -⟩ <;> omega
  have hmeta : pwPost mj oc.toNat cd.length k =
      os.pwPostE m off.toNat (nn + c) (max j (nn + k)) (if k = c then nn + c else E) := by
    rw [hcdl, hocN]
    rcases hinv with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hEj', -, -, hja, hal, -, ha, ha0⟩
    · rw [Nat.add_zero, Nat.zero_add, Nat.zero_add, show max 0 k = k by omega]
      exact pwPostE_base _ _ _ _ hk
    · exact pwPostE_chunk m off.toNat a nn j E c k hml hnj hja (by omega) ha0 hk hc0 hEj'
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) (pwPost mj oc.toNat cd.length k) ⊢
    osMeta d.ino (DFrac.own 1)
      (os.pwPostE m off.toNat (nn + c) (max j (nn + k)) (if k = c then nn + c else E)) by
      rw [hmeta]) $$ Hm
  -- the last whole chunk's end, as a variable (its `if` slows `omega` on the context down)
  generalize hE'd : (if k = c then nn + c else E) = E' at hE' ⊢
  clear hE'd hmeta hinv
  have hL2 := pwBytesG_length mj.size oc.toNat cd k nst
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))) zs
  rw [hcdl] at hL2
  have hend := pwChunk_end (pwSize m.size off.toNat j) off.toNat data.length nn c k
    (min off.toNat m.size) ys hk hcn' hyl
  rw [← hocN] at hend
  ihave Hbs := osBytes_app3 d.ino (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
    (min (oc.toNat + c) (pwSize m.size off.toNat j)) (DFrac.own 1)
    (ys.take (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))
    (pwBytesG mj.size oc.toNat cd k nst
      ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
      zs)
    (ys.drop (min (oc.toNat + c) (pwSize m.size off.toNat j) - min off.toNat m.size))
    (by simp only [List.length_take]; exact wa_take_split _ _ _ _ _ _ _ hocN hnl hsz hyl)
    (by rw [hL2, hmsz]; rcases hend with h1 | h1
        · left; omega
        · right; exact h1) $$ [Hbs1 Hbs2 Hbs3]
  · rw [hmsz]; iframe
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc23 := mcellsAny_merge m.maps (min oc.toNat (pwSize m.size off.toNat j))
    (oc.toNat + cd.length) (off.toNat + data.length) (by omega) (by omega) $$ [Hc2 Hc3]
  · rw [hmsz, hmaps]; iframe
  ihave Hc := mcellsAny_merge m.maps (min off.toNat m.size)
    (min oc.toNat (pwSize m.size off.toNat j)) (off.toNat + data.length) (by omega) (by omega)
    $$ [Hc1 Hc23]
  · iframe
  have hys' := pwValsG_chunk m.size off.toNat data cd j nn c k xs ys
    (pwBytesG mj.size oc.toNat cd k nst
      ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
      zs) hnj hj hcn' hk hcd hxl hys
    (by rw [pwBytesG_map_fst, hmsz, hocN])
  rw [← hocN] at hys'
  have hJ : max j (nn + k) ≤ data.length := by omega
  have hnJ : nn ≤ max j (nn + k) := by omega
  have hcj' : os.WaCut off.toNat data.length (max j (nn + k)) :=
    waCut_step _ _ _ _ _ _ hcj hcn hcdef hk hnl hnj hpc
  have hA := wa_chunk_bounds j nn k c data.length hjc hk hcn' hcdef hc0
  have hinv' : ∀ nn', nn ≤ nn' → (max j (nn + k) = 0 ∧ nn' = 0 ∧
      os.pwPostE m off.toNat (nn + c) (max j (nn + k)) E' = m ∧
      E' = 0) ∨
      (os.pwPostE m off.toNat (nn + c) (max j (nn + k)) E' =
          os.pwPostE m off.toNat (nn + c) (max j (nn + k)) E' ∧
        E' ≤ max j (nn + k) ∧
        (max j (nn + k) = nn + c → E' = nn + c) ∧
        m.lo ≤ m.size ∧ max j (nn + k) ≤ nn + c ∧ nn + c ≤ data.length ∧
        min data.length 0x40000000 ≤ nn + c ∧ nn + c ≤ nn' + 0x40000000 ∧ 0 < nn + c) :=
    fun nn' h => .inr ⟨rfl, hE'.1, hE'.2, hml, hA.1, hA.2.1, hA.2.2.1,
      hcdef ▸ Nat.add_le_add h (Nat.min_le_right _ _), hA.2.2.2⟩
  clear hend hL2 hyl hsz hlZ hsb hsb2 hys hcd hslz Hlen Hwf hmsz hmaps
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    try wp_auto
    wp_for_post
    inext
    iapply IH $$ %(W64 ↑nn) %nn %(max j (nn + k)) %(nn + c) %E' %_ %_ %rfl %hJ %hnJ %hnl %hys'
      %(hinv' nn (Nat.le_refl _)) %hcj' %hcn Hm Hbs Hc Hosfd Hsl Hfd HΦ [$] [$] [$] [$] [$] [$] [$] [$]
  · rw [decide_eq_false he4]
    try wp_auto
    rcases hke with ⟨hkc', rfl⟩ | he0
    · by_cases hfull : nn + k = data.length
      · rw [decide_eq_true (show W64 ↑nn + W64 ↑k = sl.len by
          rw [wa_W64_add, hsln]; congr 2)]
        try wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        wp_for_post
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨hA.1, hA.2.1, hA.2.2.1, hE'.1, hE'.2, hys', hcj', .inl ⟨by omega, hsln, rfl⟩⟩
      · rw [decide_eq_false (show ¬ W64 ↑nn + W64 ↑k = sl.len by
          rw [wa_W64_add, hsln, wa_W64_inj _ _ (by omega) (by omega)]; omega)]
        try wp_auto
        try wp_auto
        try wp_auto
        try wp_auto
        try wp_auto
        try wp_auto
        try wp_auto
        have hk0 : 0 < k := by
          rcases hkc' with h | h
          · omega
          · exact h
        have hnw2 : W64 ↑nn + W64 ↑k = W64 ↑(nn + k) := wa_W64_add nn k
        have hnJ2 : nn + k ≤ max j (nn + k) := by omega
        have hnl2 : nn + k < data.length := by omega
        have hcn2 := waCut_short _ _ _ _ _ hcn hcdef hk0 hfull hk hnl hpc
        wp_for_post
        inext
        iapply IH $$ %(W64 ↑nn + W64 ↑k) %(nn + k) %(max j (nn + k)) %(nn + c) %E' %_ %_
          %hnw2 %hJ %hnJ2 %hnl2 %hys' %(hinv' (nn + k) (by omega)) %hcj' %hcn2
          Hm Hbs Hc Hosfd Hsl Hfd HΦ [$] [$] [$] [$] [$] [$] [$] [$]
    · have he0' : ¬ e = W64 0 := he0
      by_cases hkl : W64 ↑nn + W64 ↑k = sl.len
      · rw [decide_eq_true hkl]
        try wp_auto
        rw [decide_eq_false he0']
        try wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        try wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn Hsys as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        wp_for_post
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨hA.1, hA.2.1, hA.2.2.1, hE'.1, hE'.2, hys', hcj',
            .inr ⟨rfl, (by intro h; cases h), oc.toNat, e, by omega, hPe, he0'⟩⟩
      · rw [decide_eq_false hkl]
        try wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        try wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn Hsys as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        wp_for_post
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨hA.1, hA.2.1, hA.2.2.1, hE'.1, hE'.2, hys', hcj',
            .inr ⟨rfl, (by intro h; cases h), oc.toNat, e, by omega, hPe, he0'⟩⟩

theorem os.File.WriteAt.wp_proofExt : os.File.WriteAt.specExt (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hwr hoff hbig hn hxl
  iintro %Φ Hpre HΦ
  -- a failed `pwrite` started at or past `maxBytes`, or the premises do not hold (`NoIoErr`: below
  -- `maxBytes` an error-free step exists, `wp_pwFinish_postNE`)
  iapply os.File.WriteAt.wp_proofExtQ (2 ^ 63) (fun o e => e = 0 ∨ ¬ FsNoErr ∨ maxBytes ≤ o)
    (fun t p o dt m xs n Φ _ => by
      by_cases hne : FsNoErr ∧ o < maxBytes
      · obtain ⟨⟨Sio, hSio, hs1, -, -⟩, ho⟩ := hne
        haveI := hs1
        iintro Ht H
        iapply wp_pwFinish_postNE hSio t o dt ho _ (pwTokG_inflight t p o dt m xs n) Φ $$ Ht
        iintro Ht
        iapply wp_wand $$ [Ht H]
        · iapply H $$ Ht
        iintro %r H %hr
        iapply H; ipureintro; intro r0 e he; exact Or.inl (hr r0 e he)
      · iintro Ht H
        iapply wp_wand $$ [Ht H]
        · iapply H $$ Ht
        iintro %r H; iapply H; ipureintro; intro r0 e _
        right
        by_cases h : FsNoErr
        · right; exact Nat.le_of_not_lt (fun h' => hne ⟨h, h'⟩)
        · left; exact h)
    f fd name dqf sl data dqs off dq d m xs hwr hoff hbig hn hxl (by omega) $$ Hpre
  inext
  iintro %n %err ⟨Hfo, Hsl, Hfd, %j, %a, %E, %ys, %h, Hm, Hbs, Hc, Hok⟩
  iapply HΦ
  iframe Hfo Hsl Hfd Hok
  iexists j, a, E, ys
  iframe Hm Hbs Hc
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8.imp id (fun h => ⟨h.1, h.2.1, ?_⟩)⟩
  obtain ⟨o, e, ho, hP, he⟩ := h.2.2
  rcases hP with hP | hP | hP
  · exact absurd hP he
  · exact Or.inl hP
  · exact Or.inr (by omega)

end proof

end EtcdGrove
end Perennial
