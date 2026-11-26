/-
bbolt's `WriteAt` of its file over its shares (`bMeta`, `bBytes`), in either mode (W1 stage B of
`plans/bbolt-crash-plan.md` §7, step 3; Lean-first, no Rocq counterpart).

`wp_bWriteAt` has `os.File.WriteAt.specExt`'s shape (its `OsMeta` named only by its size and
mappings): outside a crash invariant it is `specExt`; inside one, the write lies inside the file and
its bytes are past the meta pages and no protected data of the committed state (`hcr`), and it is the
local crash spec (`os.File.WriteAt.specCrashIL`), the obligation from `bDur_write_idle`; every error
arm is refuted (crash mode records `FsNoErr`). The range written joins the ranges since the last
sync.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFileOps
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Spec.os.File__WriteAt

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

variable [os.Assumptions] in
/-- **`File.WriteAt` of bbolt's file**, in either mode (see the file header). -/
theorem wp_bWriteAt (hW : os.File.WriteAt.specExt (GF := GF) (hG := hG))
    (hWC : os.File.WriteAt.specCrashIL (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (xs : List ByteG)
    (hd : d.ino = p.ino) (hwr : d.writable = true) (h0 : 0 ≤ off.toInt)
    (hlt : off.toNat + data.length < 2 ^ 63) (hpos : 0 < data.length)
    (hxl : xs.length = min (off.toNat + data.length) m.size - min off.toNat m.size) (hns : bNsOk p)
    (hcr : p.cs ≠ none → off.toNat + data.length ≤ m.size ∧
      -- interim: removed when CrashIL WriteAt covers long writes
      data.length ≤ 0x40000000 ∧
      ∀ k, off.toNat ≤ k → k < off.toNat + data.length → ∀ X, RefImg X C →
        8192 ≤ k ∧ ¬ protData X C k) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
        osFd (GF := GF) fd dq d ∗ bMeta p C L m ∗
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
             (n = W64 0 ∧ err ≠ interface.nil ∧ (¬ FsNoErr ∨ maxBytes ≤ off.toNat + j))) ∧
            m'.size = pwSize m.size off.toNat j ∧ m'.maps = m.maps⌝ ∗
          bMeta p C ((off.toNat, data.length) :: L) m' ∗
          bBytes p (min off.toNat m.size) (DFrac.own 1) ys ∗
          mcellsAny m.maps (min off.toNat m.size) (off.toNat + data.length)) ∗
        fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hf, Hsl, Hfd, Hm, Hxs, Hc⟩ HΦ
  cases hc : p.cs with
  | none =>
    simp only [bMeta_none hc]
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
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl, by simp only [os.pwPostE, pwPost, announce_maps]⟩
  | some c =>
    obtain ⟨hin, hlen, hun⟩ := hcr (by rw [hc]; exact fun h => nomatch h)
    have hmin : min off.toNat m.size = off.toNat := by omega
    have hxl' : xs.length = data.length := by rw [hxl]; omega
    rw [hmin]
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, hlh⟩ := Hf
    imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
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
      fun k h1 h2 => by rw [hcur]; exact hun k h1 h2 a.xcur (hcur ▸ hI.1)
    have hobl := bDur_write_idle a hph m bs 0 0 off.toNat data hD hin hunp hlh
    iapply (hWC f fd name dqf sl data dqs off dq d c.N p.ino c.g c.ga c.gc bCsOk a m bs xs hd hwr h0
      hin (by omega) hlt hpos hlen hxl' (hns c hc)
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
      (wreach_inside hR hin hbl hW0.2.2.1 hW0.2.2.2).2.2.2.1.trans hsz.symm
    obtain ⟨hs', -, -, -, -, hout, hxs'⟩ := wreach_inside hR hin hbl hW0.2.2.1 hW0.2.2.2
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
      · iapply bMeta_of_own p c hc C ((off.toNat, data.length) :: L) m' bs' a
          ⟨hph, hcur, hdo, hfs, fun l hl x hx => by
            rw [hs']; rw [hxs'] at hl; exact hlh l hl x hx⟩ $$ [Hown Ha]
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
