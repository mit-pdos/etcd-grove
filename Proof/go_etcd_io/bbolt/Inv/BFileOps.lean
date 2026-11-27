/-
bbolt's file operations over its shares of the file (`bMeta`, `bBytes`), in either mode (W1 stage
B of `plans/bbolt-crash-plan.md` §7; Lean-first, no Rocq counterpart): outside a crash invariant
(`p.cs = none`) each is the crash-free spec; inside one (`p.cs = some c`) it is the local crash
spec (`Spec/os/CrashStIL.lean`), the caller's part of the file being `bMeta`'s token and half of
the `OsMeta` (`csOwnIL`), and the obligation `bCsOk` of each state the call passes through is
discharged from H1's preservation lemmas (`Crash/Phases.lean`).

* `bMeta_own`/`bMeta_of_own`: `bMeta` in crash mode, as the local caller's part and its facts.
* `wp_bMunmap`, `wp_bMmap`: the mapping's changes (`bDur_maps`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFileCrash
public import Proof.go_etcd_io.bbolt.Crash.Phases
public import Spec.os.CrashStIL
public import Spec.os.CrashStILR
public import Spec.golang_org.x.sys.unix.Munmap
public import Spec.golang_org.x.sys.unix.Mmap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The facts `bMeta` keeps beside the token, in crash mode. -/
def bMetaF (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) (bs : List ByteG) (a : BAbs) :
    Prop :=
  a.phase = .idle ∧ a.cur = C ∧ DurOut L bs ∧ FsNoErr ∧ XsOne m

omit go_gctx in
/-- **`bMeta` in crash mode** as the local caller's part (`csOwnIL`), the exclusivity tokens'
authority and its facts. -/
theorem bMeta_own (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) :
    bMeta (GF := GF) p C L m ⊢ ∃ (bs : List ByteG) (a : BAbs),
      csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗ ⌜bMetaF C L m bs a⌝ := by
  unfold bMeta bMetaG; rw [hc]; dsimp only
  iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
  iexists bs, a
  iframe Ha
  isplitl [Ht Hm]
  · unfold csOwnIL csOwnL; iframe; ipureintro; exact ⟨Hf.1, rfl, rfl, rfl⟩
  ipureintro; exact ⟨Hf.2.1, Hf.2.2.1, Hf.2.2.2.1, Hf.2.2.2.2.1, Hf.2.2.2.2.2 rfl⟩

omit go_gctx in
theorem bMeta_of_own (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (bs : List ByteG) (a : BAbs) (hf : bMetaF C L m bs a) :
    csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ⊢ bMeta p C L m := by
  unfold bMeta bMetaG; rw [hc]; dsimp only
  unfold csOwnIL csOwnL
  iintro ⟨⟨Ht, Hm, %Hl⟩, Ha⟩
  iframe Hm Ha
  iexists bs, a
  iframe Ht
  ipureintro; exact ⟨Hl.1, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun _ => hf.2.2.2.2⟩

/-- `bMetaF` but the crash sizes (`bMetaG`'s facts at `lh`). -/
def bMetaFG (lh : Bool) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) (bs : List ByteG)
    (a : BAbs) : Prop :=
  a.phase = .idle ∧ a.cur = C ∧ DurOut L bs ∧ FsNoErr ∧ (lh = true → XsOne m)

omit go_gctx in
/-- **`bMetaG` in crash mode** as the local caller's part (`bMeta_own`, any `lh`). -/
theorem bMetaG_own (lh : Bool) (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) :
    bMetaG (GF := GF) lh p C L m ⊢ ∃ (bs : List ByteG) (a : BAbs),
      csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗ ⌜bMetaFG lh C L m bs a⌝ := by
  unfold bMetaG; rw [hc]; dsimp only
  iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
  iexists bs, a
  iframe Ha
  isplitl [Ht Hm]
  · unfold csOwnIL csOwnL; iframe; ipureintro; exact ⟨Hf.1, rfl, rfl, rfl⟩
  ipureintro; exact Hf.2

omit go_gctx in
theorem bMetaG_of_own (lh : Bool) (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (bs : List ByteG) (a : BAbs) (hf : bMetaFG lh C L m bs a) :
    csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ⊢ bMetaG lh p C L m := by
  unfold bMetaG; rw [hc]; dsimp only
  unfold csOwnIL csOwnL
  iintro ⟨⟨Ht, Hm, %Hl⟩, Ha⟩
  iframe Hm Ha
  iexists bs, a
  iframe Ht
  ipureintro; exact ⟨Hl.1, hf⟩

omit go_gctx in
theorem bMetaT_none {p : BFile} (h : p.cs = none) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    bMetaT (GF := GF) p C L m = osMeta p.ino (DFrac.own 1) m := by
  unfold bMetaT bMetaG; rw [h]

omit go_gctx in
/-- `bMetaT` after a failure is `bMeta` (crash mode records `FsNoErr`). -/
theorem bMetaT_err (p : BFile) (C : CommitSt) (L L' : List (Nat × Nat)) (m : OsMeta)
    (hne : ¬ FsNoErr) : bMetaT (GF := GF) p C L m ⊢ bMeta p C L' m := by
  unfold bMetaT bMeta bMetaG
  cases p.cs with
  | none => exact .rfl
  | some c =>
    dsimp only
    iintro ⟨-, -, %bs, %a, -, %Hf⟩
    iexfalso; ipureintro; exact hne Hf.2.2.2.2.1

omit go_gctx in
theorem bMeta_T (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    bMeta (GF := GF) p C L m ⊢ bMetaT p C L m := by
  unfold bMetaT bMeta bMetaG
  cases p.cs with
  | none => exact .rfl
  | some c =>
    dsimp only
    iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
    iframe Hm Ha
    iexists bs, a
    iframe Ht
    ipureintro
    exact ⟨Hf.1, Hf.2.1, Hf.2.2.1, Hf.2.2.2.1, Hf.2.2.2.2.1, fun h => nomatch h⟩

theorem bCsInv_some (p : BFile) (c : CsN) (hc : p.cs = some c) :
    bCsInv (GF := GF) p ⊢ csInvIR c.N p.ino c.g c.ga c.gc bCsOk (bR c.cg) := by
  unfold bCsInv; rw [hc]

theorem bCsOk_maps (a : BAbs) (m : OsMeta) (bs : List ByteG) (mp : GMap Loc Nat)
    (h : bCsOk a ⟨m, bs, 0, 0, .idle⟩) : bCsOk a ⟨{ m with maps := mp }, bs, 0, 0, .idle⟩ :=
  fun hf => bDur_maps a m bs 0 0 .idle mp (h hf)

variable [golang_org.x.sys.unix.Assumptions] in
/-- **`unix.Munmap` of a mapping of bbolt's file**, in either mode (as `Munmap.spec`). -/
theorem wp_bMunmap (hM : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG))
    (hMC : golang_org.x.sys.unix.Munmap.specCrashILR (GF := GF) (hG := hG))
    (base : Loc) (len : w64) (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta)
    (vf : Nat → val) (hlen : 0 < len.toInt) (hmap : m.maps !! base = some len.toNat)
    (hns : bNsOk p) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ bMeta p C L m ∗ cellsR base 0 len.toNat vf }}
      (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
    {{ (e : w64), RET #(errnoErr e);
        (⌜e = 0⌝ ∗ bMeta p C L { m with maps := GMap.delete base m.maps }) ∨
         (⌜e ≠ 0 ∧ ¬ FsNoErr⌝ ∗
           (bMeta p C L { m with maps := GMap.delete base m.maps } ∨
            (bMeta p C L m ∗ cellsR base 0 len.toNat vf))) }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hm, Hc⟩ HΦ
  cases hc : p.cs with
  | none =>
    simp only [bMeta_none hc]
    iapply (hM base len p.ino m vf hlen hmap) $$ [Hm Hc]
    · iframe; iframe #
    inext
    iintro %e Hr
    iapply HΦ $$ %e Hr
  | some c =>
    ihave #Hinv := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    imod csOwnILR_ok (bR c.cg) c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hinv Hown with ⟨Hown, %Hok⟩
    iapply (hMC base len p.ino c.N c.g c.ga c.gc bCsOk (bR c.cg) a m bs vf hlen hmap (hns c hc)
      (bCsOk_maps a m bs _ Hok.1)) $$ [Hown Hc]
    · iframe; iframe #
    inext
    iintro %e Hr
    iapply HΦ $$ %e
    icases Hr with (⟨%he, Hown⟩ | ⟨%he, (Hown | ⟨Hown, Hc⟩)⟩)
    · ileft; isplitr
      · ipureintro; exact he
      iapply bMeta_of_own p c hc C L { m with maps := GMap.delete base m.maps } bs a Hf $$ [Hown Ha]
      iframe
    · iright; isplitr
      · ipureintro; exact he
      ileft
      iapply bMeta_of_own p c hc C L { m with maps := GMap.delete base m.maps } bs a Hf $$ [Hown Ha]
      iframe
    · iright; isplitr
      · ipureintro; exact he
      iright; iframe Hc; iapply bMeta_of_own p c hc C L m bs a Hf $$ [Hown Ha]; iframe

variable [golang_org.x.sys.unix.Assumptions] in
/-- **`unix.Mmap` of bbolt's file**, in either mode (as `Mmap.spec`). -/
theorem wp_bMmap (hM : golang_org.x.sys.unix.Mmap.spec (GF := GF) (hG := hG))
    (hMC : golang_org.x.sys.unix.Mmap.specCrashILR (GF := GF) (hG := hG))
    (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (hd : d.ino = p.ino) (hr : d.readable = true)
    (hoff : off = 0) (hlen : 0 < len.toInt) (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) (hns : bNsOk p) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ osFd fd dq d ∗ bMeta p C L m }}
      (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
        (Val #len)) (Val #prot)) (Val #fl))
    {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
        ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
            bMeta p C L { m with maps := <[base := len.toNat]> m.maps } ∗
            ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) ∨
         (⌜e ≠ 0 ∧ sl = slice.nil ∧ ¬ FsNoErr⌝ ∗ bMeta p C L m)) }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hfd, Hm⟩ HΦ
  cases hc : p.cs with
  | none =>
    simp only [bMeta_none hc]
    rw [← hd]
    iapply (hM fd off len prot fl dq d m hr hoff hlen hprot hfl) $$ [Hfd Hm]
    · iframe; iframe #
    inext
    iintro %sl %e ⟨Hfd, Hr⟩
    iapply HΦ $$ %sl %e
    rw [hd]
    iframe
  | some c =>
    ihave #Hinv := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    imod csOwnILR_ok (bR c.cg) c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hinv Hown with ⟨Hown, %Hok⟩
    iapply (hMC fd off len prot fl dq d c.N p.ino c.g c.ga c.gc bCsOk (bR c.cg) a m bs hd hr hoff hlen
      hprot hfl (hns c hc) (fun _ => bCsOk_maps a m bs _ Hok.1)) $$ [Hfd Hown]
    · iframe; iframe #
    inext
    iintro %sl %e ⟨Hfd, Hr⟩
    iapply HΦ $$ %sl %e
    iframe Hfd
    icases Hr with (⟨%base, %he, Hown, Hcs⟩ | ⟨%he, Hown⟩)
    · ileft; iexists base; isplitr
      · ipureintro; exact he
      iframe Hcs
      iapply bMeta_of_own p c hc C L { m with maps := <[base := len.toNat]> m.maps } bs a Hf
        $$ [Hown Ha]
      iframe
    · iright; isplitr
      · ipureintro; exact he
      iapply bMeta_of_own p c hc C L m bs a Hf $$ [Hown Ha]; iframe

end res

end bbolt
end EtcdGrove
end Perennial
