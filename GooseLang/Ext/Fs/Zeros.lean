/-
**Zero runs** (plan I4, `notes/wal-fsext-plan.md`): a symbolic resource for a run of bytes of a file
that are all zero with the same crash candidates, for the WAL's 64 MB preallocated segments, whose
per-byte resources (`osBytes`, one `gElem` per byte) a proof context cannot hold one by one
(CLAUDE.md, "Large contexts").

`osZeros i lo n dq cs` is `osBytes i lo dq (List.replicate n (0, cs))`, sealed (`@[irreducible]`):
a proof never sees the big separating conjunction, only the laws below, all over a symbolic length
(`n` never needs to be a literal, nor `List.replicate n _` to be computed):

* `osZeros_add` (split/merge at an offset), `osZeros_zero`, `osZeros_frac` (fractions);
* `osZeros_take`: the first `k` bytes as per-byte resources (`osBytes`, for a write over a prefix
  of the run), the rest still a run; `osZeros_bytes` the definition, for a run
  short enough to unfold (a write over the run's start takes them, its `osBytes`);
* `zrun_synced`: a sync (`wp_osFsync`'s post maps `durB` over the bytes) turns a run into the run of
  durable zeros;
* `rsDone_zeros`: the bytes a resize (`ftruncate`, `fallocate`'s growth) grew a file over, when the
  file's zeros are known from its size on (`m.zf = some z`, `z ≤ m.size`: a file created in this
  generation, or synced), are a zero run with the candidates `zcs n`;
* `osZerosA`: a run of zeros each with candidates of its own (a resize of a file whose zeros are not
  known, `rsDone_zerosA`: `fileutil.ZeroToEnd`'s truncate and regrowth), with the same laws, made
  durable zeros by a sync (`zcands_synced`);
* `zcs_crash`, `zrun_crash`: a run whose candidates are all zero crashes to zeros (a crash leaves
  a byte one of its state candidates' values, `MachineCrash`, which are among the resource's,
  `CandRel.mem`).
Untrusted.
-/
module

public import GooseLang.Ext.Fs.Falloc

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ### Pure facts -/

/-- `n` zero bytes, each with the candidates `cs`. -/
abbrev zrun (n : Nat) (cs : Cands) : List ByteG := List.replicate n ((0 : w8), cs)

/-- The candidates of a byte a resize numbered `n` grew a file over, the file's zeros known: the
durable zero, then the zero the change announced. -/
abbrev zcs (n : Nat) : Cands := [((0 : w8), 0), ((0 : w8), n)]

/-- A sync makes a run durable zeros. -/
theorem zrun_synced (n : Nat) (cs : Cands) :
    (zrun n cs).map (fun x => durB x.1) = zrun n [((0 : w8), 0)] := by
  simp [zrun, List.map_replicate]

theorem zrun_add (a b : Nat) (cs : Cands) : zrun (a + b) cs = zrun a cs ++ zrun b cs := by
  simp [zrun, List.replicate_append_replicate]

@[simp] theorem zrun_length (n : Nat) (cs : Cands) : (zrun n cs).length = n := by simp [zrun]

/-- Every candidate of `zcs n` is zero. -/
theorem zcs_zero (n : Nat) : ∀ p ∈ zcs n, p.1 = 0 := by
  intro p hp; simp [zcs] at hp; rcases hp with rfl | rfl <;> rfl

/-- **The crash of a zero byte**: a byte whose resource's candidates are all zero holds zero after a
crash (the state's candidates relate to the resource's by `CandRel`, whatever the file's cut). -/
theorem zcs_crash {o : Option Nat} {cs sc : Cands} (hz : ∀ p ∈ cs, p.1 = 0) (hr : CandRel o cs sc)
    {v : w8} {s : Nat} (hv : (v, s) ∈ sc) : v = 0 := by
  obtain ⟨s', hs'⟩ := hr.mem hv
  exact hz _ hs'

/-- **The crash of a zero run**: every byte of a run whose candidates are all zero has only zero
candidates (with `zcs_crash`, a crash leaves it zero), and its value is zero. -/
theorem zrun_crash {n : Nat} {cs : Cands} (hz : ∀ p ∈ cs, p.1 = 0) :
    ∀ y ∈ zrun n cs, y.1 = 0 ∧ ∀ p ∈ y.2, p.1 = 0 := by
  intro y hy
  rw [zrun, List.mem_replicate] at hy
  obtain ⟨-, rfl⟩ := hy
  exact ⟨rfl, hz⟩

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **A zero run**: the `n` bytes of the file `i` from `lo` are zero, each with the crash candidates
`cs`. Sealed: use its laws, never its body (`osZeros_bytes` only for a short run). -/
@[irreducible] def osZeros (i : Ino) (lo n : Nat) (dq : DFrac) (cs : Cands) : IProp GF :=
  osBytes (L := L) i lo dq (zrun n cs)

/-- The definition, for a run short enough to hold byte by byte. -/
theorem osZeros_bytes (i : Ino) (lo n : Nat) (dq : DFrac) (cs : Cands) :
    osZeros (L := L) i lo n dq cs ⊣⊢ osBytes (L := L) i lo dq (zrun n cs) := by
  unfold osZeros; exact .rfl

instance osZeros_timeless (i : Ino) (lo n : Nat) (dq : DFrac) (cs : Cands) :
    Timeless (osZeros (L := L) i lo n dq cs) := by
  unfold osZeros osBytes; infer_instance

theorem osZeros_zero (i : Ino) (lo : Nat) (dq : DFrac) (cs : Cands) :
    osZeros (L := L) i lo 0 dq cs ⊣⊢ emp := by
  refine (osZeros_bytes i lo 0 dq cs).trans ?_
  unfold osBytes; exact bytesG_nil _ _ _ _

/-- **Split and merge** a run at an offset. -/
theorem osZeros_add (i : Ino) (lo a b : Nat) (dq : DFrac) (cs : Cands) :
    osZeros (L := L) i lo (a + b) dq cs ⊣⊢
      osZeros (L := L) i lo a dq cs ∗ osZeros (L := L) i (lo + a) b dq cs := by
  refine (osZeros_bytes i lo (a + b) dq cs).trans ?_
  rw [zrun_add]
  unfold osBytes
  refine (bytesG_append _ i dq lo (zrun a cs) (zrun b cs)).trans ?_
  rw [zrun_length]
  exact sep_congr (osZeros_bytes i lo a dq cs).symm (osZeros_bytes i (lo + a) b dq cs).symm

/-- A run split at `k ≤ n`: its first `k` bytes as per-byte resources, the rest a run. -/
theorem osZeros_take (i : Ino) (lo n k : Nat) (hk : k ≤ n) (dq : DFrac) (cs : Cands) :
    osZeros (L := L) i lo n dq cs ⊣⊢
      osBytes (L := L) i lo dq (zrun k cs) ∗ osZeros (L := L) i (lo + k) (n - k) dq cs := by
  have hn : n = k + (n - k) := by omega
  conv => lhs; rw [hn]
  exact (osZeros_add i lo k (n - k) dq cs).trans (sep_congr (osZeros_bytes i lo k dq cs) .rfl)

/-- Bytes of a file as fractions (a law of `osBytes`, by induction on the list: no unfolding of a
concrete one). -/
theorem osBytes_frac (i : Ino) (off : Nat) (q1 q2 : Qp) (xs : List ByteG) :
    osBytes (L := L) i off (DFrac.own (q1 + q2)) xs ⊣⊢
      osBytes (L := L) i off (DFrac.own q1) xs ∗ osBytes (L := L) i off (DFrac.own q2) xs := by
  unfold osBytes bytesG
  refine BIBase.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ _} => (gElem_split _ _ _ _ _ _).1),
    BigSepL.bigSepL_mono_of_forall (fun {_ _} => (gElem_split _ _ _ _ _ _).2)⟩

/-- A run as fractions. -/
theorem osZeros_frac (i : Ino) (lo n : Nat) (q1 q2 : Qp) (cs : Cands) :
    osZeros (L := L) i lo n (DFrac.own (q1 + q2)) cs ⊣⊢
      osZeros (L := L) i lo n (DFrac.own q1) cs ∗ osZeros (L := L) i lo n (DFrac.own q2) cs :=
  (osZeros_bytes _ _ _ _ _).trans <| (osBytes_frac i lo q1 q2 _).trans <|
    sep_congr (osZeros_bytes _ _ _ _ _).symm (osZeros_bytes _ _ _ _ _).symm

/-- The byte resources of a run hold zero with its candidates, in the ghost map. -/
theorem osZeros_lookup (i : Ino) (lo n : Nat) (dq : DFrac) (cs : Cands)
    (Γb : GMap (Ino × Nat) ByteG) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗ osZeros (L := L) i lo n dq cs -∗
      ⌜∀ k, k < n → Γb !! (i, lo + k) = some ((0 : w8), cs)⌝ := by
  iintro HA Hz
  icases (osZeros_bytes i lo n dq cs).1 $$ Hz with Hz
  unfold osBytes
  icases bytesG_lookup _ i lo dq (zrun n cs) Γb $$ HA Hz with %h
  ipureintro
  intro k hk
  rw [h k (by simp; exact hk)]
  simp [zrun]

/-- **The growth of a resize as a zero run**: when the file's zeros are known from its size on
(`m.zf = some z`, `z ≤ m.size`), the bytes `rsDone` gives (from the old size to the new one `sz'`)
are a zero run with the candidates `zcs n`. -/
theorem rsDone_zeros (tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (n z : Nat) (hzf : m.zf = some z)
    (hz : z ≤ m.size) :
    rsDone (L := L) tr p tg sz' m n ⊢
      osMeta (L := L) p (DFrac.own 1) (rsPost tr m tg sz') ∗
      osZeros (L := L) p m.size (sz' - m.size) (DFrac.own 1) (zcs n) ∗
      mcells (L := L) m.maps (min m.size tg) (rsHi tr m.size tg) (rsCell sz') := by
  unfold rsDone
  iintro ⟨%zs, %hzs, Hm, Hb, Hc⟩
  have hzr : zs = List.replicate (sz' - m.size) [((0 : w8), 0)] := by
    obtain ⟨hl, hzz⟩ := hzs
    apply List.ext_getElem?; intro j
    by_cases hj : j < sz' - m.size
    · rw [hzz j z hzf (by omega) (by rw [hl]; exact hj), List.getElem?_replicate, ite_eq_left_iff.mpr (fun h => absurd hj h)]
    · rw [List.getElem?_eq_none (by rw [hl]; omega),
        List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
  subst hzr
  rw [List.map_replicate, show List.replicate (sz' - m.size) ((0 : w8), [((0 : w8), 0)] ++ [((0 : w8), n)])
    = zrun (sz' - m.size) (zcs n) from rfl]
  iframe Hm Hc
  iapply (osZeros_bytes p m.size _ _ _).2
  iexact Hb

/-! ### Zero runs of unknown candidates

A resize grows a file over zeros whose candidates are known only when the file's zeros are
(`rsDone_zeros`); otherwise (a file truncated then grown before a sync: `fileutil.ZeroToEnd`) each
byte is zero with candidates of its own. `osZerosA` is such a run; a sync makes it a run of durable
zeros (`zcands_synced`). -/

/-- `n` zero bytes from `lo` of the file `i`, each with some candidates. Sealed as `osZeros`. -/
@[irreducible] def osZerosA (i : Ino) (lo n : Nat) (dq : DFrac) : IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = n⌝ ∗
    osBytes (L := L) i lo dq (zs.map (fun c => ((0 : w8), c))))

theorem osZerosA_unfold (i : Ino) (lo n : Nat) (dq : DFrac) :
    osZerosA (L := L) i lo n dq ⊣⊢ ∃ zs : List Cands, ⌜zs.length = n⌝ ∗
      osBytes (L := L) i lo dq (zs.map (fun c => ((0 : w8), c))) := by
  unfold osZerosA; exact .rfl

instance osZerosA_timeless (i : Ino) (lo n : Nat) (dq : DFrac) :
    Timeless (osZerosA (L := L) i lo n dq) := by
  unfold osZerosA osBytes; infer_instance

/-- A run of known candidates is one of unknown candidates. -/
theorem osZeros_zerosA (i : Ino) (lo n : Nat) (dq : DFrac) (cs : Cands) :
    osZeros (L := L) i lo n dq cs ⊢ osZerosA (L := L) i lo n dq := by
  iintro Hz
  icases (osZeros_bytes i lo n dq cs).1 $$ Hz with Hz
  iapply (osZerosA_unfold i lo n dq).2
  iexists List.replicate n cs
  rw [List.map_replicate]
  iframe Hz
  ipureintro; simp

/-- **Split and merge** a run of unknown candidates at an offset. -/
theorem osZerosA_add (i : Ino) (lo a b : Nat) (dq : DFrac) :
    osZerosA (L := L) i lo (a + b) dq ⊣⊢
      osZerosA (L := L) i lo a dq ∗ osZerosA (L := L) i (lo + a) b dq := by
  refine (osZerosA_unfold i lo (a + b) dq).trans ?_
  refine BIBase.BiEntails.trans ?_
    (sep_congr (osZerosA_unfold i lo a dq).symm (osZerosA_unfold i (lo + a) b dq).symm)
  unfold osBytes
  constructor
  · iintro ⟨%zs, %hl, Hb⟩
    rw [← List.take_append_drop a zs, List.map_append]
    icases (bytesG_append _ i dq lo _ _).1 $$ Hb with ⟨H1, H2⟩
    rw [List.length_map, List.length_take, show min a zs.length = a by omega]
    isplitl [H1]
    · iexists zs.take a; iframe H1; ipureintro; simp; omega
    · iexists zs.drop a; iframe H2; ipureintro; simp; omega
  · iintro ⟨⟨%z1, %h1, H1⟩, ⟨%z2, %h2, H2⟩⟩
    iexists z1 ++ z2
    rw [List.map_append]
    isplitr
    · ipureintro; simp; omega
    iapply (bytesG_append _ i dq lo _ _).2
    rw [List.length_map, h1]
    iframe

/-- The definition of a short run of unknown candidates, its first `k` bytes as per-byte resources,
the rest a run. -/
theorem osZerosA_take (i : Ino) (lo n k : Nat) (hk : k ≤ n) (dq : DFrac) :
    osZerosA (L := L) i lo n dq ⊣⊢
      osZerosA (L := L) i lo k dq ∗ osZerosA (L := L) i (lo + k) (n - k) dq := by
  have hn : n = k + (n - k) := by omega
  conv => lhs; rw [hn]
  exact osZerosA_add i lo k (n - k) dq

/-- A sync makes a zero run of unknown candidates durable zeros. -/
theorem zcands_synced (zs : List Cands) :
    (zs.map (fun c => ((0 : w8), c))).map (fun x => durB x.1) = zrun zs.length [((0 : w8), 0)] := by
  simp only [List.map_map, zrun]
  exact List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb; rfl⟩

/-- **The growth of any resize as a zero run** (of unknown candidates). -/
theorem rsDone_zerosA (tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (n : Nat) :
    rsDone (L := L) tr p tg sz' m n ⊢
      osMeta (L := L) p (DFrac.own 1) (rsPost tr m tg sz') ∗
      osZerosA (L := L) p m.size (sz' - m.size) (DFrac.own 1) ∗
      mcells (L := L) m.maps (min m.size tg) (rsHi tr m.size tg) (rsCell sz') := by
  unfold rsDone
  iintro ⟨%zs, %hzs, Hm, Hb, Hc⟩
  iframe Hm Hc
  iapply (osZerosA_unfold p m.size _ _).2
  iexists zs.map (fun c0 => c0 ++ [(0, n)])
  rw [show (zs.map (fun c0 => c0 ++ [((0 : w8), n)])).map (fun c => ((0 : w8), c)) =
    zs.map (fun c0 => ((0 : w8), c0 ++ [((0 : w8), n)])) by simp [Function.comp_def]]
  iframe Hb
  ipureintro; rw [List.length_map, hzs.1]

/-- `rsDone_zerosA` of `rsDoneK`. -/
theorem rsDoneK_zerosA (keep tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (xs : List ByteG)
    (n : Nat) :
    rsDoneK (L := L) keep tr p tg sz' m xs n ⊢
      osMeta (L := L) p (DFrac.own 1) (rsPostK keep tr m tg sz' n xs) ∗
      osZerosA (L := L) p m.size (sz' - m.size) (DFrac.own 1) ∗
      mcells (L := L) m.maps (min m.size tg) (rsHi tr m.size tg) (rsCell sz') := by
  unfold rsDoneK
  iintro ⟨%zs, %hzs, Hm, Hb, Hc⟩
  iframe Hm Hc
  iapply (osZerosA_unfold p m.size _ _).2
  iexists zs.map (fun c0 => c0 ++ [(0, n)])
  rw [show (zs.map (fun c0 => c0 ++ [((0 : w8), n)])).map (fun c => ((0 : w8), c)) =
    zs.map (fun c0 => ((0 : w8), c0 ++ [((0 : w8), n)])) by simp [Function.comp_def]]
  iframe Hb
  ipureintro; rw [List.length_map, hzs.1]

/-- `rsDone_zeros` of `rsDoneK`. -/
theorem rsDoneK_zeros (keep tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (xs : List ByteG)
    (n z : Nat) (hzf : m.zf = some z) (hz : z ≤ m.size) :
    rsDoneK (L := L) keep tr p tg sz' m xs n ⊢
      osMeta (L := L) p (DFrac.own 1) (rsPostK keep tr m tg sz' n xs) ∗
      osZeros (L := L) p m.size (sz' - m.size) (DFrac.own 1) (zcs n) ∗
      mcells (L := L) m.maps (min m.size tg) (rsHi tr m.size tg) (rsCell sz') := by
  unfold rsDoneK
  iintro ⟨%zs, %hzs, Hm, Hb, Hc⟩
  have hzr : zs = List.replicate (sz' - m.size) [((0 : w8), 0)] := by
    obtain ⟨hl, hzz⟩ := hzs
    apply List.ext_getElem?; intro j
    by_cases hj : j < sz' - m.size
    · rw [hzz j z hzf (by omega) (by rw [hl]; exact hj), List.getElem?_replicate, ite_eq_left_iff.mpr (fun h => absurd hj h)]
    · rw [List.getElem?_eq_none (by rw [hl]; omega),
        List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
  subst hzr
  rw [List.map_replicate, show List.replicate (sz' - m.size) ((0 : w8), [((0 : w8), 0)] ++ [((0 : w8), n)])
    = zrun (sz' - m.size) (zcs n) from rfl]
  iframe Hm Hc
  iapply (osZeros_bytes p m.size _ _ _).2
  iexact Hb

/-- A 64 MB segment's run, its first 8 bytes taken for a write: nothing is materialized. -/
example (i : Ino) (cs : Cands) :
    osZeros (L := L) i 0 (64 * 1024 * 1024) (DFrac.own 1) cs ⊢
      osBytes (L := L) i 0 (DFrac.own 1) (zrun 8 cs) ∗
        osZeros (L := L) i 8 (64 * 1024 * 1024 - 8) (DFrac.own 1) cs := by
  iintro H
  icases (osZeros_take i 0 _ 8 (by omega) _ cs).1 $$ H with ⟨H1, H2⟩
  iframe H1
  iexact H2

end resources

end Fs
end Perennial

end
