/-
**The crash-mode `Open`'s commit point** (W6; `Open.specC`, the dual of `DB.Close.specC`'s; Lean-first, no
Rocq counterpart). Right after `os.OpenFile`, before `Open` uses the file, the atomic update over the
caller's settled durable file (`fileHoldsMDurC`) is opened and committed in one step at `⊤`
(`open_commit`): the file goes into bbolt's crash invariant (`bfile_alloc_sy`), idle at the file's
committed state `C` with its own bytes as the reference image (`open_bDurC`: every byte durable, no
sync cut, the crash sizes the size), all of the database's ghost names are allocated (`openNames`;
the update's post names the database, so its name is fixed here), and the update gets bbolt's crash
record at `(D, D)` (at the version `C.txid`, its evidence the synced mark of `C.txid`); `Open` keeps the
client's half of the committed data, the file's resources in crash mode and the core phase's names.

The reference image's zero meta tails come with the settled file's `boltImage` (its `fileOK`'s
`metaOk`, W7). If the commit point moves (C★: a repair before crash mode), only this lemma is
re-proved.
-/
module

public import Proof.go_etcd_io.bbolt.Open.Core
public import Proof.go_etcd_io.bbolt.Open.Facts
public import Proof.go_etcd_io.bbolt.Open.CloseTok
public import Proof.go_etcd_io.bbolt.Inv.BFileCrash
public import Proof.go_etcd_io.bbolt.Inv.AuMask
public import Spec.go_etcd_io.bbolt.ApiCrash
public import Spec.go_etcd_io.bbolt.DB__validMetaOverPages
public import Proof.go_etcd_io.bbolt.Crash.Good
public import Proof.go_etcd_io.bbolt.Spill.STree
import all Spec.go_etcd_io.bbolt.Api
import all Spec.go_etcd_io.bbolt.ApiCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- **A settled durable file is durable for its committed state** (`Open/Mode.open_bDur` with the
crash sizes known only to be the size, `fileHoldsMDurC`'s): its own bytes are a reference image of `C`,
every byte durable. -/
theorem open_bDurC (C : CommitSt) (D : Data) (m : OsMeta) (xs : List ByteG)
    (hok : openOK C D m xs) (hl : xs.length = m.size)
    (h8 : 8192 ≤ m.size) (hdur : ∀ y ∈ xs, y = durB y.1) (hlo : m.lo = m.size)
    (hhi : m.hi = m.size) (hxs : ∃ l, m.xs = some l ∧ ∀ x ∈ l, x = m.size)
    (hal : m.size % 4096 = 0) :
    BDur ⟨C, C, xs.map Prod.fst, xs.map Prod.fst, .idle⟩ ⟨m, xs, 0, 0, .idle⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hok
  have hR : RefImg (xs.map Prod.fst) C :=
    ⟨h1, h2, h3, h4, by rw [List.length_map, hl]; exact h5, h6, h7⟩
  have hps : ∀ b, b < m.size →
      PSync ⟨m, xs, 0, 0, .idle⟩ b (xb (xs.map Prod.fst) b) := by
    intro b hb
    refine ⟨?_, by intro t off data n h; cases h⟩
    have hb' : b < xs.length := by omega
    show xs[b]? = some (durB (xb (xs.map Prod.fst) b))
    rw [List.getElem?_eq_getElem hb']
    refine congrArg some ((hdur _ (List.getElem_mem hb')).trans ?_)
    unfold xb
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb']
    rfl
  have hbw : BWf ⟨m, xs, 0, 0, .idle⟩ :=
    ⟨hl, trivial, by show m.lo ≤ m.size; omega, by show m.size ≤ m.hi; omega⟩
  have hI1 : ∀ b < 8192, PSync ⟨m, xs, 0, 0, .idle⟩ b (xb (xs.map Prod.fst) b) :=
    fun b hb => hps b (by omega)
  have hI2 : ∀ b, protData (xs.map Prod.fst) C b →
      PSync ⟨m, xs, 0, 0, .idle⟩ b (xb (xs.map Prod.fst) b) := by
    intro b hb
    have h1 := (protData_range hR hb).2
    exact hps b (by omega)
  have hI3 : C.hwm * 4096 ≤ m.lo := by rw [hlo]; exact h5
  have hI4 : WrIn ⟨m, xs, 0, 0, .idle⟩ := by
    intro t off data n h; cases h
  have hI5 : XsAl ⟨m, xs, 0, 0, .idle⟩ := by
    obtain ⟨l, hl', hall⟩ := hxs
    refine ⟨l, hl', ?_, ?_, ?_⟩
    · intro x hx; rw [hall x hx]; exact hal
    · intro t sz n h; cases h
    · intro t off data n h; cases h
  exact ⟨hbw, hR, hI1, hI2, hI3, hal, hI4, hI5⟩

/-- A page's header read from any prefix of it at least a header long. -/
theorem pageHdr_bytesAt (X : List w8) (off L L' : Nat) (hL : 16 ≤ L) (hL' : 16 ≤ L') :
    pageHdr (bytesAt X off L) = pageHdr (bytesAt X off L') := by
  unfold pageHdr bytesAt
  simp only [List.drop_zero, List.take_take, Nat.min_eq_left hL, Nat.min_eq_left hL']

/-- **An opened file's current meta is a valid meta over the pages it names** (W6; what refutes
`needsInit`'s re-initialization of it, the fork's 2c660ee): the meta of slot `C.txid % 2` validates,
the freelist page it names is a freelist page of its own id inside the file (`flFileOK`), its root page
a leaf or branch page inside the file (`treeOK`). -/
theorem openOK_metaOverPages (C : CommitSt) (D : Data) (m : OsMeta) (xs : List ByteG)
    (hok : openOK C D m xs) (hl : xs.length = m.size) :
    metaOverPages (xs.map Prod.fst) (C.txid % 2) := by
  obtain ⟨hI, hM, hT, hF, hH, -, -, -⟩ := hok
  have hXl : (xs.map Prod.fst).length = m.size := by rw [List.length_map, hl]
  generalize hX : xs.map Prod.fst = X at hXl hI hF
  have h3 := treeOK_root' C hT
  have hn : C.hwm ≤ X.length / 4096 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
  have hslot : bytesAt X (4096 * (C.txid % 2)) 4096 = C.slot C.txid := by
    unfold CommitSt.slot
    rcases Nat.mod_two_eq_zero_or_one C.txid with h | h <;> simp only [h] <;> simp [hI.1, hI.2.1]
  obtain ⟨-, -, -, -, -, hval, hisM, -⟩ := hM
  have h2 := Nat.mod_lt C.txid (show 0 < 2 by decide)
  unfold metaOverPages
  rw [hslot]
  refine ⟨by omega, hval, ?_, by rw [hisM.2.1]; omega, ?_⟩
  · intro f hf
    rw [hisM.2.2.2] at hf
    obtain ⟨-, hext, hflag, -, -, -, -, -, hid⟩ := hF f hf
    refine ⟨by omega, ?_, ?_⟩
    · unfold pageFlags
      rw [pageHdr_bytesAt X (4096 * f) 4096
        ((1 + pageOverflow (bytesAt X (4096 * f) 4096)) * 4096) (by omega) (by omega)]
      exact hflag
    · unfold pageId
      rw [pageHdr_bytesAt X (4096 * f) 4096
        ((1 + pageOverflow (bytesAt X (4096 * f) 4096)) * 4096) (by omega) (by omega)]
      exact hid
  · rw [hisM.2.1]
    obtain ⟨⟨hwf, -⟩, -⟩ := hT
    cases hwf with
    | page _ pg h2r hlt hlk _ _ hptw =>
      have hlk' := Spill.treePages_le _ _ _ _ (hI.2.2 ▸ hlk)
      rw [filePages_lookup, if_pos hlt] at hlk'
      have hpg : pg = filePage X C.root := (Option.some.inj hlk').symm
      subst hpg
      unfold pageFlags
      rw [pageHdr_bytesAt X (4096 * C.root) 4096
        ((1 + pageOverflow (bytesAt X (4096 * C.root) 4096)) * 4096) (by omega) (by omega)]
      cases hptw with
      | leaf _ _ hfl _ _ => exact .inl hfl
      | branch _ _ hfl _ _ => exact .inr hfl

end pure

section commit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The crash-mode `Open`'s commit point** (see the file header): the atomic update over the
settled durable file `i` of `D`, opened and committed at `⊤`, gives the database's names `B`, the file
`p` (its path `path`, crash names `c`) in its crash invariant (`bCsInv`, the crash names registered
under `B.cn`) idle at its committed state `C` (`openOK`), the writer's share of its `OsMeta` `m` and
bbolt's share of its bytes `xs`, `C.txid`'s receipt, the core phase's names (`openNames`), the
client's half of the committed data and the update's `Q`. -/
theorem open_commit (N : Namespace) (path : GoString) (i : Ino) (D : Data)
    (Q : BoltName → IProp GF) (hfs : FsNoErr) :
    AU <{ fileHoldsMDurC (GF := GF) i D }> @ ⊤ \ ↑N, ∅
      <{ ∀∀ (γ : BoltName), ⌜γ.ns = N⌝ ∗ boltCrashRec γ i D D, COMM Q γ }> ⊢
    |={⊤}=> ∃ (B : BNs) (c : CsN) (C : CommitSt) (m : OsMeta) (xs : List ByteG),
      ⌜c.gc = B.bq ∧ c.N = crashN N ∧ openOK C D m xs ∧ m.maps = ∅ ∧ xs.length = m.size ∧
        8192 ≤ m.size ∧ m.size < 2 ^ 62 ∧ m.size % 4096 = 0 ∧ m.size ≤ 0xFFFFFFFFFFFF⌝ ∗
      bCsInv (GF := GF) { path := path, ino := i, cs := some c } ∗ cnReg B (some c.cg) ∗
      bMeta { path := path, ino := i, cs := some c } C [] m ∗
      bBytes { path := path, ino := i, cs := some c } 0 (DFrac.own 1) xs ∗
      ⧖ C.txid ∗ openNames B C ∗ boltStateDef B (1 : Qp).half (treeData C) ∗
      Q ⟨mkGs B, N⟩ := by
  iintro Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  ihave Hacc := fupd_open_closeMask N _ $$ Hacc
  imod Hacc with Hacc
  try isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨Hf, Hucl⟩
  -- the settled durable file: its facts, its committed state `C`
  unfold fileHoldsMDurC boltImageRcpt
  icases Hf with ⟨%m, %bs, Hm, Hb, %hm, #Hrc⟩
  obtain ⟨hmaps, hsz, hlo, hhi, hpos, hcut, hxs, himg, hlen⟩ := hm
  unfold boltImage at himg
  obtain ⟨⟨hlt, hal⟩, hfok⟩ := himg
  obtain ⟨C, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8⟩ :
      ∃ C, fileImage bs C ∧ C.metaOk ∧ treeOK C ∧ flFileOK bs C ∧ C.hwm * 4096 ≤ bs.length ∧
        1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧ treeData C = D := by
    rcases hfok with ⟨h0, -⟩ | h
    · omega
    · exact h
  have hxf : (bs.map durB).map Prod.fst = bs := by simp [List.map_map, Function.comp_def]
  have hxl : (bs.map durB).length = m.size := by rw [List.length_map, hsz]
  have hroot := treeOK_root' C hC3
  have h8 : 8192 ≤ m.size := by rw [hsz]; omega
  have hok : openOK C D m (bs.map durB) :=
    ⟨by rw [hxf]; exact hC1, hC2, hC3, by rw [hxf]; exact hC4, by rw [hsz]; exact hC5, hC6, hC7, hC8⟩
  have hdur : ∀ y ∈ bs.map durB, y = durB y.1 := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
    rfl
  have hxsm : ∃ l, m.xs = some l ∧ ∀ x ∈ l, x = m.size := by
    obtain ⟨l, hl, hall⟩ := hxs
    exact ⟨l, hl, fun x hx => (hall x hx).trans hsz.symm⟩
  have hone : XsOne m := by
    intro l hl x hx
    obtain ⟨l', hl', hall⟩ := hxsm
    rw [hl] at hl'
    cases hl'
    exact hall x hx
  have hD : BDur ⟨C, C, (bs.map durB).map Prod.fst, (bs.map durB).map Prod.fst, .idle⟩
      ⟨m, bs.map durB, 0, 0, .idle⟩ :=
    open_bDurC C D m (bs.map durB) hok hxl h8 hdur (by rw [hlo, hsz])
      (by rw [hhi, hsz]) hxsm (by rw [hsz]; exact hal)
  ihave #HrcC := fileRcpt_get bs C hC1 hC2 $$ Hrc
  -- the file into its crash invariant, with its synced mark
  imod ghostVar_alloc (GF := GF) () with ⟨%γbq, Hbq⟩
  imod bfile_alloc_sy path i γbq (crashN N) C m (bs.map durB)
    ⟨C, C, (bs.map durB).map Prod.fst, (bs.map durB).map Prod.fst, .idle⟩ (closeMask N) hxl hcut
    ⟨rfl, rfl, rfl⟩ (fun _ => hD) hdur hfs hone $$ Hm Hb HrcC
    with ⟨%c, %hc, #Hci, Hm, Hb, Hcv, #Hh, #Hsy⟩
  -- the crash names registered, the database's names
  imod dghostVar_alloc (GF := GF) (some c.cg) with ⟨%gcn, Hreg⟩
  imod dghostVar_persist gcn 1 (some c.cg) $$ Hreg with #Hreg
  imod openNames_alloc (GF := GF) γbq gcn C (closeMask N) with ⟨%B, %HB, Hnames, Hst⟩
  obtain ⟨hBbq, hBcn⟩ := HB
  rw [← hBbq, ← hBcn]
  have hcgc : c.gc = B.bq := hc.1.trans hBbq.symm
  -- the committed data's halves: the record's and the client's
  icases (ghostVar_split_half B.st _ _).1 $$ Hst with ⟨Hst1, Hst2⟩
  icases (ghostVar_split_half B.bq 1 ()).1 $$ Hbq with ⟨Hbq1, Hbq2⟩
  icases (ghostVar_split_half c.cg.cv _ _).1 $$ Hcv with ⟨Hcv1, Hcv2⟩
  ihave #Hinv := (show bCsInv (GF := GF) { path := path, ino := i, cs := some c } ⊢
      csInvIR c.N i c.g c.ga c.gc bCsOk (bR c.cg) from by unfold bCsInv; exact .rfl) $$ Hci
  -- the record at `(D, D)`, version `C.txid`, its evidence the synced mark
  ihave Hrec : boltCrashRec (GF := GF) ⟨mkGs B, N⟩ i D D $$ [Hst1 Hbq1 Hcv1]
  · unfold boltCrashRec boltStateV boltStateVDef cRecDef
    rw [bnsOf_mkGs]
    iexists C.txid, c
    rw [← hC8]
    iframe Hst1 Hbq1
    isplitl [Hcv1]
    · unfold crashPart
      iexists (some c.cg)
      unfold cnReg
      iframe Hreg
      iapply (cpart_some c.cg _ _ _).2
      iframe Hcv1; iframe Hh
    isplitr
    · ipureintro; exact ⟨hcgc, hc.2, hfs⟩
    isplitr
    · iexact Hinv
    isplitr
    · unfold cnReg; iexact Hreg
    ileft; iexact Hsy
  -- commit
  icases Hucl with ⟨-, Hcommit⟩
  try isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  ihave Hc := Hcommit $$ %(⟨mkGs B, N⟩ : BoltName) [Hrec]
  · isplitr
    · ipureintro; rfl
    · iexact Hrec
  imod (fupd_close_closeMask N _) $$ Hc with HQ
  imodintro
  iexists B, c, C, m, bs.map durB
  isplitr
  · ipureintro
    refine ⟨hcgc, hc.2, hok, hmaps, hxl, h8, by rw [hsz]; exact hlt, by rw [hsz]; exact hal, ?_⟩
    unfold boltMaxMapSize at hlen
    rw [hsz]; exact hlen
  iframe Hci Hm Hb HrcC Hnames HQ
  isplitr
  · unfold cnReg; iexact Hreg
  unfold boltStateDef boltStateVDef
  iexists C.txid
  iframe Hst2 Hbq2
  unfold crashPart
  iexists (some c.cg)
  unfold cnReg
  iframe Hreg
  iapply (cpart_some c.cg _ _ _).2
  iframe Hcv2; iframe Hh

end commit

end bbolt
end EtcdGrove
end Perennial
