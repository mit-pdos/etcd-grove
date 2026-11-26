/-
bbolt's `WriteAt` of its file over its shares (`bMeta`, `bBytes`), in either mode (W1 stage B of
`plans/bbolt-crash-plan.md` §7, step 3; Lean-first, no Rocq counterpart).

`wp_bWriteAt` has `os.File.WriteAt.specExt`'s shape (its `OsMeta` named only by its size and
mappings): outside a crash invariant it is `specExt`; inside one, the write lies inside the file and
its bytes are past the meta pages and no protected data of the committed state (`hcr`), and it is the
local crash spec for data of any length (`os.File.WriteAt.specCrashILLongR`, in chunks of at most
1 GiB), the obligation from `bDur_write_idleC`; every error
arm is refuted (crash mode records `FsNoErr`). The range written joins the ranges since the last
sync.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFileOps
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Spec.os.File__WriteAt
public import Spec.os.CrashStILLong
public import Proof.go_etcd_io.bbolt.Crash.PhasesC

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

/-- The values a complete write inside the file leaves in its range. -/
theorem wrote_vals (bs' : List ByteG) (off : Nat) (data : List w8) (h : off + data.length ≤ bs'.length)
    (hv : ∀ i < data.length, (bs'[off + i]?).map Prod.fst = data[i]?) :
    ((bs'.drop off).take data.length).map Prod.fst = data := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < data.length
  · rw [if_pos hi, hv i hi]
  · rw [if_neg hi, List.getElem?_eq_none (by omega)]; rfl

/-- **`bMeta` with the bytes the writer may write named** (`P`): in crash mode, also no byte of
`P` is protected data of the committed state for the crash invariant's reference image
(`protData a.xcur a.cur`). `Commit` gets it for the dirty pages' slots before `tx.write()`
(`Commit/CrashProt.lean`); writes keep it (they change neither `a` nor `C`). -/
def bMetaP (P : Nat → Prop) (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    IProp GF :=
  match p.cs with
  | none => osMeta p.ino (DFrac.own 1) m
  | some c => iprop(osMeta p.ino (DFrac.own (1 : Qp).half) m ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗
      ∃ (bs : List ByteG) (a : BAbs), csTokI c.g c.ga a (⟨m, bs, 0, 0, .idle⟩ : CSt) ∗
        ⌜(⟨m, bs, 0, 0, .idle⟩ : CSt).Wf ∧ bMetaF C L m bs a ∧
          ∀ k, protData a.xcur a.cur k → ¬ P k⌝)

omit go_gctx in
theorem bMetaP_none {p : BFile} (h : p.cs = none) (P : Nat → Prop) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) :
    bMetaP (GF := GF) P p C L m = osMeta p.ino (DFrac.own 1) m := by
  unfold bMetaP; rw [h]

omit go_gctx in
/-- **Forgetting the named bytes.** -/
theorem bMetaP_bMeta (P : Nat → Prop) (p : BFile) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) : bMetaP (GF := GF) P p C L m ⊢ bMeta p C L m := by
  unfold bMetaP bMeta bMetaG
  cases p.cs with
  | none => exact .rfl
  | some c =>
    dsimp only
    iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
    iframe Hm Ha
    iexists bs, a
    iframe Ht
    ipureintro
    obtain ⟨hw, ⟨h1, h2, h3, h4, h5⟩, -⟩ := Hf
    exact ⟨hw, h1, h2, h3, h4, fun _ => h5⟩

omit go_gctx in
/-- `bMetaP` in crash mode as the local caller's part. -/
theorem bMetaP_own (P : Nat → Prop) (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) :
    bMetaP (GF := GF) P p C L m ⊢ ∃ (bs : List ByteG) (a : BAbs),
      csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗
      ⌜bMetaF C L m bs a ∧ ∀ k, protData a.xcur a.cur k → ¬ P k⌝ := by
  unfold bMetaP; rw [hc]; dsimp only
  iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
  iexists bs, a
  iframe Ha
  isplitl [Ht Hm]
  · unfold csOwnIL csOwnL; iframe; ipureintro; exact ⟨Hf.1, rfl, rfl, rfl⟩
  ipureintro; exact Hf.2

omit go_gctx in
theorem bMetaP_of_own (P : Nat → Prop) (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (bs : List ByteG) (a : BAbs) (hf : bMetaF C L m bs a)
    (hp : ∀ k, protData a.xcur a.cur k → ¬ P k) :
    csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ⊢ bMetaP P p C L m := by
  unfold bMetaP; rw [hc]; dsimp only
  unfold csOwnIL csOwnL
  iintro ⟨⟨Ht, Hm, %Hl⟩, Ha⟩
  iframe Hm Ha
  iexists bs, a
  iframe Ht
  ipureintro; exact ⟨Hl.1, hf, hp⟩

omit go_gctx in
/-- **Naming the bytes** from `bMeta`'s parts, given that none of them is protected. -/
theorem bMeta_P (P : Nat → Prop) (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta)
    (hp : ∀ c, p.cs = some c → ∀ (bs : List ByteG) (a : BAbs), bMetaF C L m bs a →
      ∀ k, protData a.xcur a.cur k → ¬ P k) :
    bMeta (GF := GF) p C L m ⊢ bMetaP P p C L m := by
  cases hc : p.cs with
  | none => rw [bMeta_none hc, bMetaP_none hc]
  | some c =>
    iintro Hm
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    iapply bMetaP_of_own P p c hc C L m bs a Hf (hp c hc bs a Hf) $$ [Hown Ha]
    iframe

omit go_gctx in
/-- **Any ranges, outside crash mode or after a failure** (`bMeta_err`). -/
theorem bMeta_L (p : BFile) (C : CommitSt) (L L' : List (Nat × Nat)) (m : OsMeta)
    (h : p.cs = none ∨ ¬ FsNoErr) : bMeta (GF := GF) p C L m ⊢ bMeta p C L' m := by
  rcases h with h | h
  · rw [bMeta_none h, bMeta_none h]
  · exact bMeta_err p C C L L' m h

omit go_gctx in
/-- **The file system does not fail, in crash mode** (`bMeta` records it). -/
theorem bMeta_fsNoErr (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta)
    (h : p.cs ≠ none) : bMeta (GF := GF) p C L m ⊢ bMeta p C L m ∗ ⌜FsNoErr⌝ := by
  unfold bMeta bMetaG
  cases hc : p.cs with
  | none => exact absurd hc h
  | some c =>
    dsimp only
    iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
    isplitl
    · iframe Hm Ha; iexists bs, a; iframe Ht; ipureintro; exact Hf
    ipureintro; exact Hf.2.2.2.2.1

omit go_gctx in
/-- A fraction of `bMetaP`'s `OsMeta` (as `bMeta_osMeta`). -/
theorem bMetaP_osMeta (P : Nat → Prop) (p : BFile) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) :
    bMetaP (GF := GF) P p C L m ⊢ ∃ q : Qp, osMeta p.ino (DFrac.own q) m ∗
      (osMeta p.ino (DFrac.own q) m -∗ bMetaP P p C L m) := by
  unfold bMetaP
  cases p.cs with
  | none =>
    dsimp only
    iintro Hm
    iexists 1; iframe; iintro H; iexact H
  | some c =>
    dsimp only
    iintro ⟨Hm, Ha, Ht⟩
    iexists (1 : Qp).half; iframe Hm
    iintro Hm; iframe

variable [os.Assumptions] in
/-- **`File.WriteAt` of bbolt's file**, in either mode (see the file header). -/
theorem wp_bWriteAt (hW : os.File.WriteAt.specExt (GF := GF) (hG := hG))
    (hWC : os.File.WriteAt.specCrashILLongR (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (xs : List ByteG)
    (hd : d.ino = p.ino) (hwr : d.writable = true) (h0 : 0 ≤ off.toInt)
    (hlt : off.toNat + data.length < 2 ^ 63) (hpos : 0 < data.length)
    (hxl : xs.length = min (off.toNat + data.length) m.size - min off.toNat m.size) (hns : bNsOk p)
    (P : Nat → Prop)
    (hcr : p.cs ≠ none → off.toNat + data.length ≤ m.size ∧
      ∀ k, off.toNat ≤ k → k < off.toNat + data.length → 8192 ≤ k ∧ P k) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
        osFd (GF := GF) fd dq d ∗ bMetaP P p C L m ∗
        bBytes p (min off.toNat m.size) (DFrac.own 1) xs ∗
        mcellsAny (GF := GF) m.maps (min off.toNat m.size) (off.toNat + data.length) }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
        (Val #off))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
        (∃ (j a E : Nat) (m' : OsMeta) (ys : List ByteG),
          ⌜j ≤ a ∧ a ≤ data.length ∧ min data.length 0x40000000 ≤ a ∧ E ≤ j ∧ (j = a → E = a) ∧
            ys.map Prod.fst = pwValsG m.size off.toNat data j xs ∧
            os.WaCut off.toNat data.length j ∧
            ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
             (n = W64 0 ∧ err ≠ interface.nil ∧
               (¬ FsNoErr ∨ (p.cs = none ∧ maxBytes ≤ off.toNat + j)))) ∧
            m'.size = pwSize m.size off.toNat j ∧ m'.maps = m.maps⌝ ∗
          bMetaP P p C ((off.toNat, data.length) :: L) m' ∗
          bBytes p (min off.toNat m.size) (DFrac.own 1) ys ∗
          mcellsAny m.maps (min off.toNat m.size) (off.toNat + data.length)) ∗
        fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hf, Hsl, Hfd, Hm, Hxs, Hc⟩ HΦ
  cases hc : p.cs with
  | none =>
    simp only [bMetaP_none hc]
    ihave Hxs := (bBytes_none hc _ _ _).1 $$ Hxs
    rw [← hd]
    iapply (hW f fd name dqf sl data dqs off dq d m xs hwr h0 hlt hpos hxl) $$ [Hf Hsl Hfd Hm Hxs Hc]
    · iframe; iframe #
    inext
    iintro %n %err ⟨Hf, Hsl, Hfd, %j, %a, %E, %ys, %Hj, Hm, Hys, Hc, Herr⟩
    iapply HΦ $$ %n %err
    iframe Hf Hsl Hfd Herr
    iexists j, a, E, os.pwPostE m off.toNat a j E, ys
    rw [hd]
    ihave Hys := (bBytes_none hc _ _ _).2 $$ Hys
    iframe
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Hj
    refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, rfl, by simp only [os.pwPostE, pwPost, announce_maps]⟩
    rcases h8 with h8 | ⟨h8a, h8b, h8c | h8c⟩
    · exact Or.inl h8
    · exact Or.inr ⟨h8a, h8b, Or.inl h8c⟩
    · exact Or.inr ⟨h8a, h8b, Or.inr ⟨by first | trivial | rfl | exact hc, h8c⟩⟩
  | some c =>
    obtain ⟨hin, hun⟩ := hcr (by rw [hc]; exact fun h => nomatch h)
    have hmin : min off.toNat m.size = off.toNat := by omega
    have hxl' : xs.length = data.length := by rw [hxl]; omega
    rw [hmin]
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    icases bMetaP_own P p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨⟨hph, hcur, hdur, hfs, hlh⟩, hpr⟩ := Hf
    imod csOwnILR_ok (bR c.cg) c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hci Hown with ⟨Hown, %Hok⟩
    have hD : BDur a ⟨m, bs, 0, 0, .idle⟩ := Hok.1 hfs
    have hI : IdleOk a.cur a.xcur ⟨m, bs, 0, 0, .idle⟩ := ((bDur_idle_iff hph).1 hD).2
    have hW0 : BWf ⟨m, bs, 0, 0, .idle⟩ := hD.1
    have hbl : bs.length = m.size := hW0.1
    icases (bBytes_os p off.toNat (DFrac.own 1) xs).1 $$ Hxs with ⟨Hxs, Hg⟩
    have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by unfold BFile.dq; rw [hc]; rfl
    rw [hdq]
    -- the file is at most `maxBytes` (the model's bound)
    icases Hown with ⟨Htok, Hm1, %Hlo⟩
    iapply wp_osMeta_size _ _ rfl p.ino _ m $$ Hm1
    iintro %hmax Hm1
    ihave Hown : csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a $$ [Htok Hm1]
    · unfold csOwnIL csOwnL; iframe; ipureintro; exact Hlo
    have hunp : ∀ k, off.toNat ≤ k → k < off.toNat + data.length → 8192 ≤ k ∧ ¬ protData a.xcur a.cur k :=
      fun k h1 h2 => ⟨(hun k h1 h2).1, fun hk => hpr k hk (hun k h1 h2).2⟩
    have hobl := bDur_write_idleC a hph m bs 0 0 off.toNat data hD hin hunp hlh
    iapply (hWC f fd name dqf sl data dqs off dq d c.N p.ino c.g c.ga c.gc bCsOk (bR c.cg) a m bs xs hd hwr h0
      hin (by omega) hlt hpos hxl' (hns c hc)
      (fun nn m' bs' hR => ⟨fun _ => (hobl nn m' bs' hR).1,
        fun hl t n hfr _ => (hobl nn m' bs' hR).2 hl t n hfr⟩)) $$ [Hf Hsl Hfd Hown Hxs Hc]
    · iframe; iframe #
    inext
    iintro %n %err ⟨Hf, Hsl, Hfd, Hc, %nn, %m', %bs', %Hr, Hown, Hys⟩
    obtain ⟨hxs, hR, hres⟩ := Hr
    rcases hres with ⟨hn, herr, hnn, hsz, hmaps, hvals⟩ | ⟨-, -, hne⟩
    rotate_left
    · exact absurd hfs hne
    subst hn herr hnn
    iapply HΦ $$ %(W64 data.length) %interface.nil
    iframe Hf Hsl Hfd
    have hbl' : bs'.length = m'.size :=
      (wreachC_inside hR hin hbl hW0.2.2.1 hW0.2.2.2).2.2.2.1.trans hsz.symm
    obtain ⟨hs', -, -, -, -, hout, hxs'⟩ := wreachC_inside hR hin hbl hW0.2.2.1 hW0.2.2.2
    have hyl : ((bs'.drop off.toNat).take data.length).length = data.length := by
      simp only [List.length_take, List.length_drop]; omega
    have hdo : DurOut ((off.toNat, data.length) :: L) bs' := by
      intro k x hk hko
      have hk' := hko (off.toNat, data.length) List.mem_cons_self
      rw [hout k (by simpa using hk')] at hk
      exact hdur k x hk (fun r hr => hko r (List.mem_cons_of_mem _ hr))
    isplitl [Hown Ha Hys Hg Hc]
    · iexists data.length, data.length, data.length, m', (bs'.drop off.toNat).take data.length
      isplitr
      · ipureintro
        refine ⟨Nat.le_refl _, Nat.le_refl _, Nat.min_le_left _ _, Nat.le_refl _, fun _ => rfl, ?_,
          ⟨Or.inl (Or.inr (Or.inl rfl)), Or.inr (by omega)⟩, Or.inl ⟨rfl, rfl, rfl⟩,
          by rw [hsz, pwSize_inside m.size off.toNat data.length data.length (Nat.le_refl _) hin],
          hmaps⟩
        rw [pwValsG_inside m.size off.toNat data data.length xs hin hxl' (Or.inr rfl),
          if_neg (by omega)]
        exact wrote_vals bs' off.toNat data (by omega) hvals
      isplitl [Hown Ha]
      · iapply bMetaP_of_own P p c hc C ((off.toNat, data.length) :: L) m' bs' a
          ⟨hph, hcur, hdo, hfs, fun l hl x hx => by
            rw [hs']; rw [hxs'] at hl; exact hlh l hl x hx⟩ hpr $$ [Hown Ha]
        rw [hsz]; iframe
      isplitl [Hys Hg]
      · iapply (bBytes_os p off.toNat (DFrac.own 1) _).2
        rw [hdq, hyl, ← hxl']; iframe
      iexact Hc
    unfold fmtErrorOkOrNil; itrivial

end res

end bbolt
end EtcdGrove
end Perennial
