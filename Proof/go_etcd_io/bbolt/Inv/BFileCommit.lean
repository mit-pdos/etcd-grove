/-
bbolt's file while a commit is in flight (W1 stage B of `plans/bbolt-crash-plan.md` §7, the meta
write's crash branch; Lean-first, no Rocq counterpart).

* `bMetaCm p C' C L m`: the writer's whole share from the commit point to the commit's second
  `fdatasync`, the crash invariant's value committing from `C` to `C'` (`bMeta`'s, phase
  `committing`). Outside a crash invariant, `osMeta 1`.
* `bMeta_commit`: **the commit point** (`Tx.Commit`, under `metalock`, before the meta page's
  `pwrite`): from `bMeta p C [] m` (every byte durable: after the first `fdatasync`) and the new
  tree's slots, the value moves to committing (`bDur_commit_of`, `csOwnIL_setA`).
* `wp_bWriteMetaC`: the meta page's `WriteAt` in crash mode (`os.File.WriteAt.specCrashIL`, the
  obligation from `bDur_write_meta`); it lands whole (crash mode records `FsNoErr`).
* `wp_bFdatasyncC`: the commit's second `fdatasync` in crash mode
  (`syscall.Fdatasync.specCrashILA`: the value moves to idle at `C'` as the sync lands,
  `bDur_sync_commit`), back to `bMeta p C' [] m'`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFileSync
public import Proof.go_etcd_io.bbolt.Inv.BFileWrite
public import Proof.go_etcd_io.bbolt.Inv.Store
public import Proof.go_etcd_io.bbolt.Crash.Img
public import Spec.os.CrashStILA

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

/-! ## The share while committing -/

/-- **The writer's whole share while a commit is in flight** (see the file header). -/
def bMetaCm (p : BFile) (C' C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) : IProp GF :=
  match p.cs with
  | none => osMeta p.ino (DFrac.own 1) m
  | some c => iprop(osMeta p.ino (DFrac.own (1 : Qp).half) m ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗
      ∃ (bs : List ByteG) (a : BAbs), csTokI c.g c.ga a (⟨m, bs, 0, 0, .idle⟩ : CSt) ∗
        ⌜(⟨m, bs, 0, 0, .idle⟩ : CSt).Wf ∧ a.phase = .committing ∧ a.cur = C' ∧ a.prev = C ∧
          DurOut L bs ∧ FsNoErr⌝)

omit go_gctx sem in
instance bMetaCm_timeless (p : BFile) (C' C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    Timeless (bMetaCm (GF := GF) p C' C L m) := by
  unfold bMetaCm
  cases p.cs with
  | none => dsimp only; unfold osMeta; infer_instance
  | some c => dsimp only; unfold osMeta csTokI; infer_instance

omit go_gctx sem in
theorem bMetaCm_none {p : BFile} (h : p.cs = none) (C' C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) : bMetaCm (GF := GF) p C' C L m = osMeta p.ino (DFrac.own 1) m := by
  unfold bMetaCm; rw [h]

omit go_gctx sem in
theorem bMetaCm_to_os {p : BFile} (h : p.cs = none) (C' C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) : bMetaCm (GF := GF) p C' C L m ⊢ osMeta p.ino (DFrac.own 1) m := by
  rw [bMetaCm_none h]

omit go_gctx sem in
/-- A fraction of the extension's `OsMeta` (`bMeta_osMeta`'s, for the crash-free specs that take
any fraction). -/
theorem bMetaCm_osMeta (p : BFile) (C' C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    bMetaCm (GF := GF) p C' C L m ⊢ ∃ q : Qp, osMeta p.ino (DFrac.own q) m ∗
      (osMeta p.ino (DFrac.own q) m -∗ bMetaCm p C' C L m) := by
  unfold bMetaCm
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

/-- The facts `bMetaCm` keeps beside the token, in crash mode. -/
def bMetaCmF (C' C : CommitSt) (L : List (Nat × Nat)) (bs : List ByteG) (a : BAbs) : Prop :=
  a.phase = .committing ∧ a.cur = C' ∧ a.prev = C ∧ DurOut L bs ∧ FsNoErr

omit go_gctx sem in
/-- **`bMetaCm` in crash mode** as the local caller's part, the tokens' authority and its facts. -/
theorem bMetaCm_own (p : BFile) (c : CsN) (hc : p.cs = some c) (C' C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) :
    bMetaCm (GF := GF) p C' C L m ⊢ ∃ (bs : List ByteG) (a : BAbs),
      csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗ ⌜bMetaCmF C' C L bs a⌝ := by
  unfold bMetaCm; rw [hc]; dsimp only
  iintro ⟨Hm, Ha, %bs, %a, Ht, %Hf⟩
  iexists bs, a
  iframe Ha
  isplitl [Ht Hm]
  · unfold csOwnIL csOwnL; iframe; ipureintro; exact ⟨Hf.1, rfl, rfl, rfl⟩
  ipureintro; exact Hf.2

omit go_gctx sem in
theorem bMetaCm_of_own (p : BFile) (c : CsN) (hc : p.cs = some c) (C' C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (bs : List ByteG) (a : BAbs) (hf : bMetaCmF C' C L bs a) :
    csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ⊢ bMetaCm p C' C L m := by
  unfold bMetaCm; rw [hc]; dsimp only
  unfold csOwnIL csOwnL
  iintro ⟨⟨Ht, Hm, %Hl⟩, Ha⟩
  iframe Hm Ha
  iexists bs, a
  iframe Ht
  ipureintro; exact ⟨Hl.1, hf⟩

/-! ## The commit point -/

/-- **The store's slots `S` (`slotsOwn`) are the state's bytes** (`csOwnIL_agree`, slot by slot). -/
theorem slots_agree (p : BFile) (c : CsN) (hc : p.cs = some c) (s : CSt) (a : BAbs)
    (ms : MapSt) (g : Nat → List w8) :
    ∀ S : List Nat, (∀ x ∈ S, 4096 * (x + 1) ≤ s.bs.length ∧ (g x).length = 4096) →
    ⊢ csInvI (GF := GF) c.N p.ino c.g c.ga c.gc bCsOk -∗
      csOwnIL (GF := GF) p.ino c.g c.ga s a -∗ slotsOwn ms p S g ={⊤}=∗
      csOwnIL (GF := GF) p.ino c.g c.ga s a ∗ slotsOwn ms p S g ∗
        ⌜∀ x ∈ S, ∀ k < 4096, (s.bs[4096 * x + k]?).map Prod.fst = (g x)[k]?⌝
  | [], _ => by
    iintro #Hinv Hown HS
    imodintro; iframe
    ipureintro; intro x hx; cases hx
  | x :: S, h => by
    iintro #Hinv Hown HS
    unfold slotsOwn
    icases BigSepL.bigSepL_cons.1 $$ HS with ⟨⟨Hc, Hx⟩, HS⟩
    iunfold osSlot at Hx
    icases Hx with ⟨%xs, Hx, %hxs⟩
    have hxl : xs.length = 4096 := by
      have := congrArg List.length hxs; simp only [List.length_map] at this
      rw [this]; exact (h x List.mem_cons_self).2
    icases (bBytes_os p (4096 * x) (DFrac.own 1) xs).1 $$ Hx with ⟨Hx, Hg⟩
    imod csOwnIL_agree c.N p.ino c.g c.ga c.gc bCsOk s a ⊤ CoPset.subseteq_top (4096 * x) _ xs
      (by have := (h x List.mem_cons_self).1; omega) $$ Hinv Hown Hx with ⟨Hown, Hx, %he⟩
    imod slots_agree p c hc s a ms g S (fun y hy => h y (List.mem_cons_of_mem _ hy)) $$ Hinv Hown
      [HS] with ⟨Hown, HS, %hS⟩
    · unfold slotsOwn; iexact HS
    ihave Hx : osSlot (GF := GF) p x (g x) $$ [Hx Hg]
    · unfold osSlot
      iexists xs
      isplitl [Hx Hg]
      · iapply (bBytes_os p (4096 * x) (DFrac.own 1) xs).2; iframe
      ipureintro; exact hxs
    imodintro
    iframe Hown
    isplitl [Hc Hx HS]
    · unfold slotsOwn
      iapply BigSepL.bigSepL_cons.2
      iframe HS
      iframe Hc
      iexact Hx
    ipureintro
    intro y hy k hk
    rcases List.mem_cons.1 hy with rfl | hy
    · have hb : 4096 * y + k < s.bs.length := by have := (h y List.mem_cons_self).1; omega
      rw [← hxs, List.getElem?_map, he, List.getElem?_take, if_pos (by omega),
        List.getElem?_drop]
    · exact hS y hy k hk

/-- **The commit point** (see the file header): the premises are `bDur_commit_of`'s, the new
pages either `C`'s or in whole slots of `S` (held, `slotsOwn`), inside the file. -/
theorem bMeta_commit (p : BFile) (C C' : CommitSt) (m : OsMeta) (ms : MapSt)
    (S : List Nat) (g : Nat → List w8)
    (htx : C'.txid = C.txid + 1) (htx2 : C'.txid < 2 ^ 62)
    (hsl : ∀ i, i % 2 ≠ C'.txid % 2 → C'.slot i = C.slot i)
    (hmok : C'.metaOk) (htree : treeOK C') (hfl : C'.flpg = none)
    (htail : ∀ k, 80 ≤ k → k < 4096 → (C'.slot C'.txid)[k]? = some 0)
    (hpg : ∀ id pg, C'.pages !! id = some pg → C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap g))
    (hS : ∀ x ∈ S, (g x).length = 4096)
    (hin : p.cs ≠ none → C'.hwm * 4096 ≤ m.size ∧ ∀ x ∈ S, 4096 * (x + 1) ≤ m.size)
    -- the crash size bounds agree (the commit's first `fdatasync`, `m.synced`)
    (hlh : p.cs ≠ none → m.lo = m.hi) :
    ⊢ bCsInv (GF := GF) p -∗ bMeta p C [] m -∗ slotsOwn ms p S g ={⊤}=∗
      bMetaCm p C' C [] m ∗ slotsOwn ms p S g := by
  iintro #Hinv Hm HS
  cases hc : p.cs with
  | none =>
    rw [bMeta_none hc, bMetaCm_none hc]
    imodintro; iframe
  | some c =>
    obtain ⟨hhwm, hSin⟩ := hin (by rw [hc]; exact fun h => nomatch h)
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C [] m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, -⟩ := Hf
    have hlh := hlh (by rw [hc]; exact fun h => nomatch h)
    imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hci Hown with ⟨Hown, %Hok⟩
    ihave %hlo := csOwnL_locOk (csTokI c.g c.ga a) p.ino ⟨m, bs, 0, 0, .idle⟩ $$ Hown
    have hbl : bs.length = m.size := hlo.1.1
    imod slots_agree p c hc ⟨m, bs, 0, 0, .idle⟩ a ms g S
      (fun x hx => ⟨by show _ ≤ bs.length; rw [hbl]; exact hSin x hx, hS x hx⟩)
      $$ Hci Hown HS with ⟨Hown, HS, %hag⟩
    have hdur' : ∀ (k : Nat) (x : ByteG), bs[k]? = some x → x = durB x.1 :=
      fun k x h => hdur k x h (fun r hr => by cases hr)
    have hD := bDur_commit_of a ⟨m, bs, 0, 0, .idle⟩ rfl (Hok.1 hfs) hph hdur' hlh C' g
      (by rw [hcur]; exact htx) htx2 (fun i hi => by rw [hcur]; exact hsl i hi) hmok htree hfl
      hhwm htail (fun id pg hp => by
        rcases hpg id pg hp with h | ⟨hj, he⟩
        · left; rw [hcur]; exact h
        · right
          exact ⟨fun j hj' => ⟨hS _ (hj j hj'), hag _ (hj j hj')⟩, he⟩)
    imod csOwnIL_setA c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a
      (⟨C', a.cur, cpImg ⟨m, bs, 0, 0, .idle⟩ C', a.xcur, .committing⟩ : BAbs) ⊤ CoPset.subseteq_top (fun _ => hD) $$ Hci Hown with Hown
    imodintro
    iframe HS
    iapply bMetaCm_of_own p c hc C' C [] m bs
      (⟨C', a.cur, cpImg ⟨m, bs, 0, 0, .idle⟩ C', a.xcur, .committing⟩ : BAbs)
      ⟨rfl, rfl, hcur, fun k x h _ => hdur' k x h, hfs⟩ $$ [Hown Ha]
    iframe

/-! ## The meta write -/

variable [os.Assumptions] in
/-- **The meta page's `WriteAt` in crash mode** (see the file header): `C'`'s current meta at its
slot, inside the file; it lands whole, the range joining the ranges since the last sync. -/
theorem wp_bWriteMetaC (hWC : os.File.WriteAt.specCrashIL (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (p : BFile) (c : CsN) (hc : p.cs = some c)
    (C' C : CommitSt) (m : OsMeta) (xs : List ByteG)
    (hd : d.ino = p.ino) (hwr : d.writable = true) (h0 : 0 ≤ off.toInt) (hns : bNsOk p)
    (hoff : off.toNat = 4096 * (C'.txid % 2)) (hdata : data = C'.slot C'.txid)
    (hdl : data.length = 4096) (hxl : xs.length = 4096) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
        osFd (GF := GF) fd dq d ∗ bMetaCm p C' C [] m ∗ bBytes p off.toNat (DFrac.own 1) xs ∗
        mcellsAny (GF := GF) m.maps off.toNat (off.toNat + data.length) }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
        (Val #off))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜n = W64 4096 ∧ err = interface.nil⌝ ∗
        os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
        mcellsAny m.maps off.toNat (off.toNat + data.length) ∗
        ∃ (m' : OsMeta) (ys : List ByteG), ⌜m'.size = m.size ∧ m'.maps = m.maps ∧
            ys.map Prod.fst = data⌝ ∗
          bMetaCm p C' C [(off.toNat, 4096)] m' ∗ bBytes p off.toNat (DFrac.own 1) ys }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hf, Hsl, Hfd, Hm, Hxs, Hc⟩ HΦ
  ihave #Hci := bCsInv_some p c hc $$ Hinv
  icases bMetaCm_own p c hc C' C [] m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
  obtain ⟨hph, hcur, hprev, hdur, hfs⟩ := Hf
  imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
    $$ Hci Hown with ⟨Hown, %Hok⟩
  have hD : BDur a ⟨m, bs, 0, 0, .idle⟩ := Hok.1 hfs
  have hW0 : BWf ⟨m, bs, 0, 0, .idle⟩ := hD.1
  have hbl : bs.length = m.size := hW0.1
  have hCk := ((bDur_commit_iff hph).1 hD).2
  have h3 := refImg_hwm hCk.2.1
  have hsz : 12288 ≤ m.size := by
    have := Nat.mul_le_mul_right 4096 h3
    have : a.cur.hwm * 4096 ≤ m.lo := hCk.2.2.2.2.2.2.2.2.2.1
    have : m.lo ≤ m.size := hW0.2.2.1
    omega
  have hp2 : C'.txid % 2 < 2 := Nat.mod_lt _ (by omega)
  have hin : off.toNat + data.length ≤ m.size := by omega
  icases (bBytes_os p off.toNat (DFrac.own 1) xs).1 $$ Hxs with ⟨Hxs, Hg⟩
  have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by unfold BFile.dq; rw [hc]; rfl
  rw [hdq]
  have hR0 : ∀ nn m' bs', WReach m bs off.toNat data nn m' bs' →
      WReach m bs (4096 * (a.cur.txid % 2)) (a.cur.slot a.cur.txid) nn m' bs' := by
    intro nn m' bs' h; rw [hcur, ← hoff, ← hdata]; exact h
  have hobl : ∀ nn m' bs', WReach m bs off.toNat data nn m' bs' →
      bCsOk a ⟨m', bs', 0, 0, .idle⟩ ∧ (nn < data.length → ∀ t n,
        PwFresh m' bs' (off.toNat + nn) (data.drop nn) n →
        bCsOk a ⟨m', bs', 0, 0, .write t (off.toNat + nn) (data.drop nn) n⟩) := by
    intro nn m' bs' h
    have hw := bDur_write_meta a hph m bs 0 0 hD nn m' bs' (hR0 nn m' bs' h)
    refine ⟨fun _ => hw.1, fun hl t n hfr _ => ?_⟩
    have e1 : 4096 * (a.cur.txid % 2) = off.toNat := by rw [hcur, hoff]
    have e2 : a.cur.slot a.cur.txid = data := by rw [hcur, hdata]
    have := hw.2 (by rw [e2]; exact hl) t n (by rw [e1, e2]; exact hfr)
    rw [e1, e2] at this; exact this
  iapply (hWC f fd name dqf sl data dqs off dq d c.N p.ino c.g c.ga c.gc bCsOk a m bs xs hd hwr h0
      hin (by have : maxBytes = 0xffffffff000 := rfl; omega) (by omega) (by omega) (by omega)
      (by omega) (hns c hc) hobl) $$ [Hf Hsl Hfd Hown Hxs Hc]
  · iframe; iframe #
  inext
  iintro %n %err ⟨Hf, Hsl, Hfd, Hc, %nn, %m', %bs', %Hr, Hown, Hys⟩
  obtain ⟨hxs, hR, hres⟩ := Hr
  rcases hres with ⟨hn, herr, hnn, hsz', hmaps, hvals⟩ | ⟨-, -, hne⟩
  rotate_left
  · exact absurd hfs hne
  subst hn herr hnn
  iapply HΦ $$ %(W64 data.length) %interface.nil
  obtain ⟨-, -, -, hl', -, hout, -⟩ := wreach_inside hR hin hbl hW0.2.2.1 hW0.2.2.2
  have hyl : ((bs'.drop off.toNat).take data.length).length = data.length := by
    simp only [List.length_take, List.length_drop]; omega
  have hdo : DurOut [(off.toNat, 4096)] bs' := by
    intro k x hk hko
    have hk' := hko (off.toNat, 4096) List.mem_cons_self
    rw [hout k (by rw [hdl]; simpa using hk')] at hk
    exact hdur k x hk (fun r hr => by cases hr)
  isplitr
  · ipureintro; exact ⟨by rw [hdl]; rfl, rfl⟩
  iframe Hf Hsl Hfd Hc
  iexists m', (bs'.drop off.toNat).take data.length
  isplitr
  · ipureintro; exact ⟨hsz', hmaps, wrote_vals bs' off.toNat data (by omega) hvals⟩
  isplitl [Hown Ha]
  · iapply bMetaCm_of_own p c hc C' C [(off.toNat, 4096)] m' bs' a
      ⟨hph, hcur, hprev, hdo, hfs⟩ $$ [Hown Ha]
    rw [hsz']; iframe
  iapply (bBytes_os p off.toNat (DFrac.own 1) _).2
  rw [hdq, hyl]
  iframe Hys
  rw [show data.length = xs.length by omega]
  iexact Hg

/-! ## The commit's second sync -/

/-- **The commit's second `fdatasync` in crash mode** (see the file header): the meta page's bytes
(its slot, written whole) the only ones not durable; the value moves to idle at `C'`. -/
theorem wp_bFdatasyncC (hSA : syscall.Fdatasync.specCrashILA (GF := GF) (hG := hG))
    (fd : w64) (dq : DFrac) (d : OsFd) (p : BFile) (c : CsN) (hc : p.cs = some c)
    (C' C : CommitSt) (m : OsMeta) (o : Nat) (ys : List ByteG) (hd : d.ino = p.ino)
    (hns : bNsOk p) (ho : o = 4096 * (C'.txid % 2)) (hys : ys.map Prod.fst = C'.slot C'.txid) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ osFd (GF := GF) fd dq d ∗ bMetaCm p C' C [(o, 4096)] m ∗
        bBytes p o (DFrac.own 1) ys }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ ⌜e = 0⌝ ∗
        ∃ (m' : OsMeta) (ys' : List ByteG), bMeta p C' [] m' ∗ bBytes p o (DFrac.own 1) ys' ∗
          ⌜m'.size = m.size ∧ m'.maps = m.maps ∧ ys'.map Prod.fst = ys.map Prod.fst⌝ }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hfd, Hm, Hys⟩ HΦ
  ihave #Hci := bCsInv_some p c hc $$ Hinv
  icases bMetaCm_own p c hc C' C [(o, 4096)] m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
  obtain ⟨hph, hcur, hprev, hdur, hfs⟩ := Hf
  imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
    $$ Hci Hown with ⟨Hown, %Hok⟩
  have hD : BDur a ⟨m, bs, 0, 0, .idle⟩ := Hok.1 hfs
  have hbl : bs.length = m.size := hD.1.1
  have hCk := ((bDur_commit_iff hph).1 hD).2
  have hRc := hCk.2.1
  have h3 := refImg_hwm hRc
  have hsz : 12288 ≤ m.size := by
    have := Nat.mul_le_mul_right 4096 h3
    have : a.cur.hwm * 4096 ≤ m.lo := hCk.2.2.2.2.2.2.2.2.2.1
    have : m.lo ≤ m.size := hD.1.2.2.1
    omega
  have hp2 : C'.txid % 2 < 2 := Nat.mod_lt _ (by omega)
  have hyl : ys.length = 4096 := by
    have := congrArg List.length hys; simp only [List.length_map] at this
    rw [this]; have := slot_length hRc.mok C'.txid; rw [hcur] at this; exact this
  have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by unfold BFile.dq; rw [hc]; rfl
  let R : List (Nat × List ByteG) := [(o, ys)]
  have hin : ∀ r ∈ R, r.1 + r.2.length ≤ m.size := by
    intro r hr; simp only [R, List.mem_singleton] at hr; subst hr; show o + ys.length ≤ _; omega
  ihave HR : bRanges p R $$ [Hys]
  · unfold bRanges; simp only [R]; iapply BigSepL.bigSepL_singleton.2; iexact Hys
  icases (bRanges_os p R).1 $$ HR with ⟨HR, HG⟩
  rw [hdq]
  imod ranges_agree c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
    (DFrac.own (1 : Qp).half) R (fun r hr => by show _ ≤ bs.length; rw [hbl]; exact hin r hr)
    $$ Hci Hown HR with ⟨Hown, HR, %hag⟩
  have hdisj : RDisj R := List.pairwise_singleton _ _
  have hruns : ∀ r ∈ R, r.1 + r.2.length ≤ bs.length ∧ r.2 = (bs.drop r.1).take r.2.length :=
    fun r hr => ⟨by rw [hbl]; exact hin r hr, hag r hr⟩
  have hys' : ys = (bs.drop o).take 4096 := by
    have := hag (o, ys) List.mem_cons_self; rw [hyl] at this; exact this
  ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) bs R hruns hdisj).1 $$ HR
  have hw : ∀ k < 4096, (bs[4096 * (a.cur.txid % 2) + k]?).map Prod.fst =
      some (xb a.xcur (4096 * (a.cur.txid % 2) + k)) := by
    intro k hk
    have hb : o + k < bs.length := by omega
    have h1 : (bs[o + k]?).map Prod.fst = (C'.slot C'.txid)[k]? := by
      rw [← hys, List.getElem?_map, hys', List.getElem?_take, if_pos hk, List.getElem?_drop]
    have h2 : C'.slot C'.txid = bytesAt a.xcur o 4096 := by
      rw [← hcur, refImg_slot hRc, hcur, ← ho]
    have hxl := hRc.len
    have hxb : o + k < a.xcur.length := by
      have := Nat.mul_le_mul_right 4096 h3; omega
    rw [hcur, ← ho, h1, h2, bytesAt_getElem? _ _ _ _ hk]
    exact (xb_some _ _ hxb).symm
  let a' : BAbs := ⟨a.cur, a.prev, a.xcur, a.xprev, .idle⟩
  have hok : bCsOk a' (csSynced m [] [] bs 0 0) := fun _ =>
    bDur_sync_commit a hph m [] [] bs 0 0 (fun y hy => by cases hy) (by simpa using hD)
      (by simpa using hw)
  have hcov' : ∀ b, b < m.size → m.dlo ≤ b → b < m.dhi →
      rMask R b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1 := by
    intro b hb _ _
    by_cases hL : o ≤ b ∧ b < o + 4096
    · left; exact rMask_true.2 ⟨(o, ys), List.mem_cons_self, by show o ≤ b ∧ b < o + ys.length; omega⟩
    · right
      have hb' : b < bs.length := by omega
      refine ⟨bs[b], List.getElem?_eq_getElem hb', ?_⟩
      refine hdur b bs[b] (List.getElem?_eq_getElem hb') fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; omega
  iapply (hSA fd dq d c.N p.ino c.g c.ga c.gc bCsOk a a' m bs (rMask R) hd (hns c hc) hcov' hok)
    $$ [Hfd Hown HR]
  · iframe; iframe #
  inext
  iintro %e ⟨Hfd, Hr⟩
  iapply HΦ $$ %e
  iframe Hfd
  icases Hr with (⟨%he, Hown, HR⟩ | ⟨%he, -, -⟩)
  rotate_left
  · exact absurd hfs he.2
  isplitr
  · ipureintro; exact he
  iexists m.synced, ys.map (fun x => durB x.1)
  ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) (rDur R)
    (rDur_runs bs R hruns) (RDisj_rDur R hdisj)).2 $$ [HR]
  · have e : rMask (rDur R) = rMask R := by
      funext k
      simp [rMask, rDur, List.any_map, rIn, Function.comp_def]
    rw [e]; iexact HR
  isplitl [Hown Ha]
  · iapply bMeta_of_own p c hc C' [] m.synced (bs.map (fun x => durB x.1)) a'
      ⟨rfl, hcur, fun k x hk _ => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hk); rfl, hfs, xsOne_synced m⟩
      $$ [Hown Ha]
    iframe
  isplitl [HR HG]
  · simp only [R, rDur, List.map_cons, List.map_nil]
    iapply (bBytes_os p o (DFrac.own 1) _).2
    rw [hdq]
    simp only [List.length_map]
    icases BigSepL.bigSepL_singleton.1 $$ HR with HR
    icases BigSepL.bigSepL_singleton.1 $$ HG with HG
    iframe
  ipureintro
  refine ⟨rfl, rfl, ?_⟩
  simp only [List.map_map]; rfl

end res

end bbolt
end EtcdGrove
end Perennial
