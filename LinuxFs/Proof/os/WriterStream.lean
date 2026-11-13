/-
**An `*os.File` is an `io.Writer` stream** (`io.writerStream`, `Proof/io/WriterStream.lean`): the
bridge from `(*os.File).Write` (`os.File.Write.wp_long`/`wp_empty`, `OffLong.lean`) to the stream
writer `ioutil.PageWriter` and the WAL's encoder write through. WAL W6 (2026-11-13, `wal-bridge`).

The file of inode `d.ino`, open at `fd` (writable), is written from the offset `o0`, where its
`OsMeta` was `m0` and its bytes from `o0` to its end `xs0` (whole: `osMeta … 1`, `osBytes … 1`;
not mapped, `m0.maps = ∅`). The stream's state after accepting `out` (`os.fileW`):

* the handle (`ownFile`, `osFd`) and the offset past `out` (`ownOff f (o0 + len out)`);
* the file's `OsMeta` `m` and its bytes `ys` from `o0` to its end, whole, with `os.StreamOk`:
  `m` is `m0` after one full write per accepted `Write` (`os.MetaChain`: the writes' chunking is
  the client's, and the `OsMeta` keeps it: each write moves the crash bounds by its own range);
  the bytes below `len out` hold `out`'s, each with its old candidates (below the old end) then one
  or more holding its value (each attempt of its write announced it); the bytes past it are
  `xs0`'s.

After a failed `Write` of `xs` (`os.fileB`): the state before it, the offset unknown, and the
file as the failed write left it (`os.File.Write.wp_long`'s error post: `pwPost`/`PwOutA`; for an
empty `xs`, unchanged). The stream accepts at most `lim` bytes, `o0 + lim < 2^62` (the model's
bound).

**Not crash-aware**: the bridge takes the file's resources whole, as `WriteAt`'s plain spec does.
A WAL segment's halves are in the WAL invariant (`segRes`, `wal/Inv.lean`), whose writes need a
crash-aware `Write` (as `File.WriteAt.specCrash`, `Spec/os/Crash.lean`); that bridge has the same
shape with `cfOwn`-like resources in place of `osMeta`/`osBytes`. Lean-first.
-/
module

public import LinuxFs.Proof.os.OffLong
public import Proof.io.WriterStream

@[expose] public section

noncomputable section

namespace Perennial

namespace os

open Fs

/-- `m` is `m0` after full writes at `o0` of `a` bytes in all, one after the other, each of
`k > 0` bytes at the end of the last (`pwPost` of a write that wrote all it announced). -/
inductive MetaChain (o0 : Nat) (m0 : OsMeta) : Nat → OsMeta → Prop
  | nil : MetaChain o0 m0 0 m0
  | step {a k : Nat} {m : OsMeta} : MetaChain o0 m0 a m → 0 < k →
      MetaChain o0 m0 (a + k) (pwPost m (o0 + a) k k)

/-- The file's state after a stream of writes of `out` at `o0` (the file header). -/
def StreamOk (m0 : OsMeta) (o0 : Nat) (xs0 : List ByteG) (out : List w8) (m : OsMeta)
    (ys : List ByteG) : Prop :=
  xs0.length = m0.size - o0 ∧
  MetaChain o0 m0 out.length m ∧ m.lo ≤ m.size ∧ m.maps = m0.maps ∧ m0.size ≤ m.size ∧
  o0 + out.length ≤ m.size ∧ ys.length = m.size - o0 ∧
  (∀ i, i < out.length → (ys.getD i (0, [])).1 = out.getD i 0 ∧
    ∃ c0 extra, (ys.getD i (0, [])).2 = c0 ++ extra ∧ extra ≠ [] ∧
      (∀ q ∈ extra, q.1 = out.getD i 0) ∧ (i < xs0.length → c0 = (xs0.getD i (0, [])).2)) ∧
  (∀ i, out.length ≤ i → ys.getD i (0, []) = xs0.getD i (0, []))

theorem StreamOk.start {m0 : OsMeta} {o0 : Nat} {xs0 : List ByteG} (hlo : m0.lo ≤ m0.size)
    (ho : o0 ≤ m0.size) (hxs : xs0.length = m0.size - o0) : StreamOk m0 o0 xs0 [] m0 xs0 :=
  ⟨hxs, .nil, hlo, rfl, Nat.le_refl _, by simpa using ho, hxs, fun i hi => absurd hi (by simp),
    fun _ _ => rfl⟩

theorem pwPost_size' (m : OsMeta) (off n k : Nat) : (pwPost m off n k).size = pwSize m.size off k := rfl
theorem pwPost_lo' (m : OsMeta) (off n k : Nat) :
    (pwPost m off n k).lo = min m.lo (max m.size (off + n)) := by simp [pwPost]
theorem pwPost_maps' (m : OsMeta) (off n k : Nat) : (pwPost m off n k).maps = m.maps := by
  simp [pwPost]

theorem getD_eq_getElem {α} (l : List α) (d : α) (i : Nat) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A full write of `xs` at the end of the stream. -/
theorem StreamOk.step {m0 : OsMeta} {o0 : Nat} {xs0 : List ByteG} {out xs : List w8} {m : OsMeta}
    {ys ys2 : List ByteG} (h : StreamOk m0 o0 xs0 out m ys) (hn : 0 < xs.length)
    (hp : PwOut m (o0 + out.length) xs xs.length ((ys.drop out.length).take xs.length) ys2) :
    StreamOk m0 o0 xs0 (out ++ xs) (pwPost m (o0 + out.length) xs.length xs.length)
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length) := by
  obtain ⟨hx0, hch, hlo, hmaps, hsz0, hosz, hyl, hin, hpast⟩ := h
  obtain ⟨hl2, hb2⟩ := hp
  have hS : pwSize m.size (o0 + out.length) xs.length = max m.size (o0 + out.length + xs.length) := by
    unfold pwSize; rw [if_neg (by omega)]
  rw [hS] at hl2
  have hl2' : ys2.length = xs.length := by rw [hl2]; omega
  have hout : out.length ≤ ys.length := by omega
  have hxs0 : xs0.length ≤ ys.length := by omega
  have hT : (ys.take out.length).length = out.length := by rw [List.length_take]; omega
  have hxw : ((ys.drop out.length).take xs.length).length = min xs.length (ys.length - out.length) := by
    simp only [List.length_take, List.length_drop]
  -- the bytes, by position
  have gT : ∀ i, i < out.length →
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length).getD i (0, []) =
        ys.getD i (0, []) := by
    intro i hi
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]
  have g2 : ∀ i (hi : out.length ≤ i) (hi2 : i < out.length + xs.length),
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length).getD i (0, []) =
        ys2[i - out.length]'(by omega) := by
    intro i hi hi2
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hT,
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some]
  have gR : ∀ i, out.length + xs.length ≤ i →
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length).getD i (0, []) =
        ys.getD i (0, []) := by
    intro i hi
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hT,
      List.getElem?_append_right (by omega), hl2', List.getElem?_drop, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
    congr 1; omega
  refine ⟨hx0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]; exact .step hch hn
  · rw [pwPost_lo', pwPost_size', hS]; omega
  · rw [pwPost_maps']; exact hmaps
  · rw [pwPost_size', hS]; omega
  · rw [pwPost_size', hS, List.length_append]; omega
  · rw [pwPost_size', hS]; simp only [List.length_append, hT, hl2', List.length_drop]; omega
  · intro i hi
    rw [List.length_append] at hi
    by_cases hiL : i < out.length
    · rw [gT i hiL, show (out ++ xs).getD i 0 = out.getD i 0 by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hiL, ← List.getD_eq_getElem?_getD]]
      exact hin i hiL
    · have hiL' : out.length ≤ i := by omega
      rw [g2 i hiL' hi]
      have hgx : (out ++ xs).getD i 0 = xs.getD (i - out.length) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hiL', ← List.getD_eq_getElem?_getD]
      rw [hgx]
      obtain ⟨hv, c0, extra, hc, hne, hq, hc0⟩ := hb2 (i - out.length) (by omega)
      refine ⟨?_, c0, extra, hc, hne, hq, fun hix => ?_⟩
      · rw [hv]; unfold pwByte
        rw [if_pos (by omega), show o0 + out.length + (i - out.length) - (o0 + out.length) =
          i - out.length by omega]
      · have hlt : i - out.length < ((ys.drop out.length).take xs.length).length := by
          rw [hxw]; omega
        rw [hc0 hlt, ← hpast i hiL', List.getElem_take, List.getElem_drop,
          getD_eq_getElem ys _ i (by omega)]
        congr 2; omega
  · intro i hi
    rw [List.length_append] at hi
    rw [gR i hi]; exact hpast i (by omega)

end os

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- A `*os.File` as an `io.Writer` (`wal.fileWi`, `newFileEncoder`'s conversion). -/
abbrev os.fileWi [GooseExts] [GoGlobalContext] (f : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType os.File.ty) #f

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- The stream's state after accepting `out` (the file header). -/
def os.fileW (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (o0 : Nat) (xs0 : List ByteG) (out : List w8) : IProp GF :=
  iprop(∃ (m : OsMeta) (ys : List ByteG), ⌜os.StreamOk m0 o0 xs0 out m ys⌝ ∗
    os.ownFile f fd name dqf ∗ osFd fd dq d ∗ os.ownOff f (W64 ((o0 + out.length : Nat) : Int)) ∗
    osMeta d.ino (DFrac.own 1) m ∗ osBytes d.ino o0 (DFrac.own 1) ys)

/-- The stream after a failed `Write` of `xs` from the state of `out` (the file header): the
offset unknown; the file unchanged (an empty `xs`), or as the failed write left it, over the bytes
before it (`ys.take (len out)`), the write's range (`zs`, `PwOutA`) and the bytes after it. -/
def os.fileB (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta)
    (o0 : Nat) (xs0 : List ByteG) (out xs : List w8) : IProp GF :=
  iprop(∃ (o' : w64) (m : OsMeta) (ys : List ByteG), ⌜os.StreamOk m0 o0 xs0 out m ys⌝ ∗
    os.ownFile f fd name dqf ∗ osFd fd dq d ∗ os.ownOff f o' ∗
    ((⌜xs = []⌝ ∗ osMeta d.ino (DFrac.own 1) m ∗ osBytes d.ino o0 (DFrac.own 1) ys) ∨
     (∃ (j A : Nat) (zs : List ByteG), ⌜j ≤ A ∧ A ≤ xs.length ∧
          os.PwOutA m (o0 + out.length) xs A j ((ys.drop out.length).take xs.length) zs ∧
          PwCut (o0 + out.length) xs.length j⌝ ∗
        osMeta d.ino (DFrac.own 1) (pwPost m (o0 + out.length) A j) ∗
        osBytes d.ino o0 (DFrac.own 1) (ys.take out.length) ∗
        osBytes d.ino (o0 + out.length) (DFrac.own 1) zs ∗
        osBytes d.ino (o0 + out.length + ((ys.drop out.length).take xs.length).length) (DFrac.own 1)
          ((ys.drop out.length).drop xs.length))))

theorem os.osBytes_split3 (i : Ino) (o0 L n : Nat) (ys : List ByteG) (hL : L ≤ ys.length) :
    osBytes (GF := GF) i o0 (DFrac.own 1) ys ⊢
      osBytes i o0 (DFrac.own 1) (ys.take L) ∗
      osBytes i (o0 + L) (DFrac.own 1) ((ys.drop L).take n) ∗
      osBytes i (o0 + L + ((ys.drop L).take n).length) (DFrac.own 1) ((ys.drop L).drop n) := by
  conv => lhs; rw [← List.take_append_drop L ys, ← List.take_append_drop n (ys.drop L)]
  unfold osBytes
  iintro H
  ihave ⟨H1, H2⟩ := (bytesG_append _ _ _ _ _ _).1 $$ H
  rw [List.length_take, Nat.min_eq_left hL]
  ihave ⟨H2, H3⟩ := (bytesG_append _ _ _ _ _ _).1 $$ H2
  iframe

theorem os.osBytes_merge3 (i : Ino) (o0 L : Nat) (a b c xsw : List ByteG) (hL : a.length = L)
    (hc : c = [] ∨ xsw.length = b.length) :
    osBytes (GF := GF) i o0 (DFrac.own 1) a ∗ osBytes i (o0 + L) (DFrac.own 1) b ∗
      osBytes i (o0 + L + xsw.length) (DFrac.own 1) c ⊢
      osBytes i o0 (DFrac.own 1) (a ++ b ++ c) := by
  unfold osBytes
  iintro ⟨H1, H2, H3⟩
  rcases hc with rfl | hc
  · rw [List.append_nil]
    iapply (bytesG_append _ _ _ _ _ _).2
    rw [hL]
    iframe
  · rw [List.append_assoc]
    iapply (bytesG_append _ _ _ _ _ _).2
    rw [hL]
    iframe H1
    iapply (bytesG_append _ _ _ _ _ _).2
    rw [← hc]
    iframe

theorem os.mcellsAny_empty (M : GMap Loc Nat) (lo hi : Nat) (h : M = ∅) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  unfold mcellsAny; rw [h]; exact BigSepM.bigSepM_empty.2

theorem os.W64_nat_toNat (a : Nat) (h : a < 2 ^ 62) : (W64 (a : Int)).toNat = a := by
  simp only [W64]; rw [BitVec.toNat_ofInt]; omega

theorem os.W64_nat_toInt (a : Nat) (h : a < 2 ^ 62) : (W64 (a : Int)).toInt = a := by
  rw [BitVec.toInt_eq_toNat_cond, os.W64_nat_toNat a h]; split <;> omega

/-- **The bridge**: from the file's resources at `o0` (the file header), with the file not mapped,
its crash low bound at most its size, `o0` inside it and at most `lim` bytes to come below `2^62`,
`(*os.File).Write` through `os.fileWi f` is a stream writer: `os.fileW … []` is its state now
(`os.fileW_start`), `os.fileW … out` after accepting `out`, `os.fileB … out xs` after a failed
`Write` of `xs`. -/
theorem os.File.writerStream (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m0 : OsMeta) (o0 : Nat)
    (xs0 : List ByteG) (lim : Nat) (hfd : 0 ≤ fd.toInt) (hwr : d.writable = true)
    (hmaps : m0.maps = ∅) (hlim : o0 + lim < 2 ^ 62) :
    osInv (GF := GF) ⊢ io.writerStream (os.fileWi f) lim (os.fileW f fd name dqf dq d m0 o0 xs0)
      (os.fileB f fd name dqf dq d m0 o0 xs0) := by
  iintro #Hinv
  unfold io.writerStream
  iintro !> %out %p %xs %dqp %hb
  iintro !> %Φ ⟨HW, Hp⟩ HΦ
  iunfold os.fileW at HW
  icases HW with ⟨%m, %ys, %Hok, Hf, Hfd, Ho, Hm, Hbs⟩
  have Hok0 := Hok
  obtain ⟨hx0, -, hlo, hmm, hsz0, hosz, hyl, -, -⟩ := Hok
  have hmm' : m.maps = ∅ := hmm.trans hmaps
  by_cases hx : xs = []
  · subst hx
    wp_apply os.File.Write.wp_empty f fd name dqf p dqp _ hfd $$ [Hf Ho Hp] as %n %err ⟨%hn, Hf, Ho, Hp⟩
    · iframe
    iapply HΦ
    iframe Hp
    rcases err with ei | _
    · iright
      isplitr
      · ipureintro; intro h; cases h
      iunfold os.fileB
      iexists _, m, ys
      iframe Hf Hfd Ho
      isplitr
      · ipureintro; exact Hok0
      ileft
      iframe Hm Hbs
      ipureintro; rfl
    · ileft
      isplitr
      · ipureintro; exact ⟨rfl, by rw [hn]; rfl⟩
      iunfold os.fileW
      iexists m, ys
      rw [List.append_nil]
      iframe
      ipureintro; exact Hok0
  have hn : 0 < xs.length := List.length_pos_iff.2 hx
  have hL : out.length ≤ ys.length := by omega
  have hoN := os.W64_nat_toNat (o0 + out.length) (by omega)
  have hoI := os.W64_nat_toInt (o0 + out.length) (by omega)
  ihave ⟨Hb1, Hb2, Hb3⟩ := os.osBytes_split3 d.ino o0 out.length xs.length ys hL $$ Hbs
  ihave Hmc := os.mcellsAny_empty (GF := GF) m.maps (o0 + out.length) (o0 + out.length + xs.length)
    hmm'
  have hxw : ((ys.drop out.length).take xs.length).length =
      min (o0 + out.length + xs.length) m.size - (o0 + out.length) := by
    simp only [List.length_take, List.length_drop]; omega
  wp_apply (os.File.Write.wp_long wp_WriteAt f fd name dqf p xs dqp (W64 ((o0 + out.length : Nat) : Int))
      dq d m ((ys.drop out.length).take xs.length) hfd hwr (by rw [hoI]; omega) (by rw [hoN]; omega)
      hlo hn (by rw [hoN]; exact hxw) (by rw [hoI]; omega))
    $$ [Hinv Hf Ho Hp Hfd Hm Hb2 Hmc] as %n %err ⟨Hf, Hp, Hfd, -, Hres⟩
  · rw [hoN]; iframe Hinv Hmc; iframe
  rw [hoN]
  iapply HΦ
  iframe Hp
  icases Hres with (⟨%ys2, ⟨%herr, %hnn, %hpw⟩, Hm, Hb2, Ho⟩ |
    ⟨%j, %A, %zs, ⟨%herr, %hjA, %hAn, %hpa, %hcut⟩, Hm, Hb2, Ho⟩)
  · ileft
    isplitr
    · ipureintro
      refine ⟨herr, ?_⟩
      rw [hnn]; simp only [sint.Z]; rw [os.W64_nat_toInt xs.length (by omega)]
    iunfold os.fileW
    iexists _, _
    iframe Hf Hfd
    isplitr
    · ipureintro; exact os.StreamOk.step Hok0 hn hpw
    isplitl [Ho]
    · rw [show W64 ((o0 + out.length : Nat) : Int) + W64 (xs.length : Int) =
          W64 ((o0 + (out ++ xs).length : Nat) : Int) by
        rw [List.length_append]; simp only [W64]; push_cast; rw [← BitVec.ofInt_add]; congr 1; omega]
      iexact Ho
    iframe Hm
    have hc : (ys.drop out.length).drop xs.length = [] ∨
        ((ys.drop out.length).take xs.length).length = ys2.length := by
      by_cases hr : (ys.drop out.length).drop xs.length = []
      · exact .inl hr
      · right
        rw [hpw.1, show pwSize m.size (o0 + out.length) xs.length =
          max m.size (o0 + out.length + xs.length) by unfold pwSize; rw [if_neg (by omega)]]
        have : xs.length < (ys.drop out.length).length := by
          rcases Nat.lt_or_ge xs.length (ys.drop out.length).length with h | h
          · exact h
          · exact absurd (List.drop_eq_nil_of_le h) hr
        simp only [List.length_take, List.length_drop] at this ⊢; omega
    iapply os.osBytes_merge3 d.ino o0 out.length _ _ _ ((ys.drop out.length).take xs.length)
      (by rw [List.length_take]; omega) hc
    iframe
  · iright
    isplitr
    · ipureintro; exact herr
    iunfold os.fileB
    iexists _, m, ys
    iframe Hf Hfd Ho
    isplitr
    · ipureintro; exact Hok0
    iright
    iexists j, A, zs
    iframe
    ipureintro
    exact ⟨hjA, hAn, hpa, hcut⟩

/-- The stream's state at the start: the file's resources at `o0`, nothing accepted. -/
theorem os.fileW_start (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd)
    (m0 : OsMeta) (o0 : Nat) (xs0 : List ByteG) (hlo : m0.lo ≤ m0.size) (ho : o0 ≤ m0.size)
    (hxs : xs0.length = m0.size - o0) :
    os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      os.ownOff (GF := GF) f (W64 (o0 : Int)) ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m0 ∗
      osBytes (GF := GF) d.ino o0 (DFrac.own 1) xs0 ⊢
      os.fileW f fd name dqf dq d m0 o0 xs0 [] := by
  iintro ⟨Hf, Hfd, Ho, Hm, Hb⟩
  iunfold os.fileW
  iexists m0, xs0
  rw [List.length_nil, Nat.add_zero]
  iframe
  ipureintro
  exact os.StreamOk.start hlo ho hxs

end bridge

end EtcdGrove

end Perennial
