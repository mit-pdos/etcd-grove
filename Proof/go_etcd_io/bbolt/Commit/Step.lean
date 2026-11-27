/-
**`Commit`'s commit point** (U10 of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 7, D22):
`writeMeta`'s `commitStep` for a commit. Under `metalock`, with the writer's ghost state and meta
bytes (whole) and cells (its quarter), the new tree's slots and the client's update: the meta slot's bytes and cells go to the
write; given back with `j` bytes written,
- `j = 4096` (the page whole, whatever `WriteAt` returned): the store publishes `C'`
  (`store_publish`), the update has fired (`au_commit_fire`), the meta cells and bytes are `C'`'s
  (`meta_put`), and `metalock`'s resource holds `C'` (`metaOk_parity_write`);
- `j = 0`: everything as it was, the update unfired.

**Where the update fires** (`cpFired`). When the file system does not fail (`FsNoErr`, which the
backend's `FsNoErrAll` gives), in the step's first half: right after `metalock.Lock()`, before the
meta page's `pwrite` starts (`tx.go:612`), which is what C-I1's laws ask of the crash proof
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashLaws.lean`); the write
then lands whole (`commitStep`'s `FsNoErr → j = 4096`), so `j = 0` does not arise. Otherwise on
landing (`j = 4096`), as before. Between the fire and the landing the data's ghost state is at
`(Dn, ν + 1)` while the page cache's meta is still `C`'s: no invariant sees the gap, since
`metalock`'s resource `metaR` (the data's other quarter and the committed state's half) is the
committer's while it holds `metalock`, and every reader takes `metalock` to read the meta
(`beginTx`, from the mapped cells). The meta slots' page-cache bytes are the writer side's whole
(`wdbCoreG`, W1), so the meta write needs nothing of `metaR`'s but the ghost state.
-/
module

public import Proof.go_etcd_io.bbolt.Tx__writeMeta
public import Proof.go_etcd_io.bbolt.Commit.MetaBytes
public import Proof.go_etcd_io.bbolt.Commit.Fire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

-- `metaSummed_txid` (the summed meta's txid is the meta's): `Inv/WriteToImage.lean`, which this
-- module now imports (W1: `Inv/Locks` imports `Inv/BFile`, over `Crash/`).

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The writer's resources the commit point works on, at the committed state `C` (`wdbCoreG`'s
ghost state, its `opened` half and meta shares; the data's writer quarter at `D`), its store
state `(v, w, pb, wl)`. -/
def cpRes (K : BC) (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (v : View) (w : Nat)
    (pb wl : Bool) (D : Data) : IProp GF :=
  iprop(ghostVar K.B.out (1 : Qp).half false ∗ ghostVar K.B.cur (1 : Qp).half.half C ∗
    ghostVar K.B.fl (1 : Qp).half fl ∗ ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) ∗
    ghostVar K.B.wv (1 : Qp).half ((some v, some w, pb, wl) : WSt) ∗
    K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true ∗
    metaCellsQ (1 : Qp).half.half (some (b, l)) C ∗ metaOsBytes K.p (DFrac.own 1) C ∗
    ghostVar K.B.st (1 : Qp).half.half (D, C.txid))

/-- The client's update of a commit from `Db` to `Dn` (versioned: the version moves by one). -/
def commitAU (K : BC) (N' : Namespace) (Db Dn : Data) (Q : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (D' : Data) (ν : Nat), boltStateVDef K.B 1 D' ν }> @ ⊤ \ ↑N', ∅
    <{ ⌜D' = Db⌝ ∗ boltStateVDef K.B 1 Dn (ν + 1), COMM Q }>)

/-- **After the commit point**: published at `C'` with the update fired (`j = 4096`), or unchanged
with the update's carrier `A` (U11i: the caller's resource that gives the update, `Commit_err`'s
`P`) and the new slots back (`j = 0`). -/
def cpPost (K : BC) (C C' : CommitSt) (fl : FLPg) (b : Loc) (l : Nat)
    (v : View) (wl : Bool) (S : List Nat) (bs : Nat → List w8) (Fb : GMap Nat (List w8))
    (Dn : Data) (Q A : IProp GF) (j : Nat) : IProp GF :=
  iprop((⌜j = 4096⌝ ∗ cpRes K C' fl b l v (C.txid + 1) true wl Dn ∗ receipt 1 ∗ Q) ∨
    (⌜j = 0⌝ ∗ cpRes K C fl b l v (C.txid + 1) false wl (treeData C) ∗
      slotsOwn (some (b, l)) K.p S bs ∗
      fbTok K.B C fl ((some v, some (C.txid + 1), false, wl) : WSt) Fb ∗ A))

/-- **The commit point, from `writeMeta`'s first half to the write's landing** (see the file
header): under `FsNoErr` the update has fired (the data's two quarters at `(Dn, ν + 1)`, the
client's `Q`); otherwise not yet (at `(D, ν)`, with the update's carrier `A`). -/
def cpFired (K : BC) (D Dn : Data) (ν : Nat) (Q A : IProp GF) : IProp GF :=
  iprop((⌜FsNoErr⌝ ∗ ghostVar K.B.st (1 : Qp).half.half (Dn, ν + 1) ∗
      ghostVar K.B.st (1 : Qp).half.half (Dn, ν + 1) ∗ Q) ∨
    (⌜¬ FsNoErr⌝ ∗ ghostVar K.B.st (1 : Qp).half.half (D, ν) ∗
      ghostVar K.B.st (1 : Qp).half.half (D, ν) ∗ A))

omit package_sem in
/-- **The early commit point** (`writeMeta`'s first half, under `metalock`, before the meta
page's `pwrite`), outside crash mode (no crash part to move, `cnReg K.B none`): under `FsNoErr` the
update fires now. -/
theorem cpFired_intro (K : BC) (N' : Namespace) (D Dn : Data) (ν : Nat) (Q A : IProp GF)
    (hA : A ⊢ commitAU K N' D Dn Q) :
    cnReg K.B none ∗ ghostVar K.B.st (1 : Qp).half.half (D, ν) ∗
      ghostVar K.B.st (1 : Qp).half.half (D, ν) ∗ A ⊢
      |={⊤}=> cpFired K D Dn ν Q A := by
  iintro ⟨#Hn, H1, H2, Hau⟩
  unfold cpFired
  by_cases hne : FsNoErr
  · ihave Hau := hA $$ Hau
    iunfold commitAU at Hau
    imod au_commit_fire K.B N' D Dn ν Q iprop(emp) ⊤ CoPset.subseteq_top
      $$ [H1 H2 Hau] with ⟨H1, H2, HQ, -⟩
    · iframe; iapply cpart_none_upd K.B D Dn ν $$ Hn
    imodintro
    ileft
    isplitr
    · ipureintro; exact hne
    iframe
  · imodintro
    iright
    isplitr
    · ipureintro; exact hne
    iframe

omit package_sem in
/-- **The commit point at the landing** (the meta page written whole): the update has fired, in
the first half (`FsNoErr`) or now (then outside crash mode, which records `FsNoErr`: `Hn`). -/
theorem cpFired_land (K : BC) (N' : Namespace) (D Dn : Data) (ν : Nat) (Q A : IProp GF)
    (hA : A ⊢ commitAU K N' D Dn Q) :
    (⌜FsNoErr⌝ ∨ cnReg K.B none) ∗ cpFired K D Dn ν Q A ⊢
      |={⊤}=> ghostVar K.B.st (1 : Qp).half.half (Dn, ν + 1) ∗
        ghostVar K.B.st (1 : Qp).half.half (Dn, ν + 1) ∗ Q := by
  unfold cpFired
  iintro ⟨Hn, Hf⟩
  icases Hf with (⟨-, H1, H2, HQ⟩ | ⟨%hne, H1, H2, Hau⟩)
  · imodintro; iframe
  · icases Hn with (%hfs | #Hn)
    · exact absurd hfs hne
    ihave Hau := hA $$ Hau
    iunfold commitAU at Hau
    imod au_commit_fire K.B N' D Dn ν Q iprop(emp) ⊤ CoPset.subseteq_top
      $$ [H1 H2 Hau] with ⟨H1, H2, HQ, -⟩
    · iframe; iapply cpart_none_upd K.B D Dn ν $$ Hn
    imodintro
    iframe

omit package_sem in
/-- **The early commit point in crash mode** (W3): inside the crash invariant's opening
(`bMeta_commit`'s `U`), its client resource moves from the committed state `C` (data `D`, txid `ν`)
to the new one `C'` (data `Dn`, txid `ν + 1`, previous `C`) as the update fires: the version variable's
two halves (the invariant's and the committed data's crash part) move together, the history gains
`ν + 1 ↦ Dn` (a fresh key: the history stops at `ν`), and `C'`'s receipt is `ν + 1`'s. -/
theorem cp_fire_crash (K : BC) (N' : Namespace) (c : CsN) (hcN : (↑c.N : CoPset) ⊆ ↑N')
    (D Dn : Data) (ν : Nat) (Q A : IProp GF) (hA : A ⊢ commitAU K N' D Dn Q) (hfs : FsNoErr)
    (C C' : CommitSt) (hC : treeData C = D ∧ C.txid = ν) (hC' : treeData C' = Dn ∧ C'.txid = ν + 1) :
    ⊢ cnReg K.B (some c.cg) -∗ ghostVar K.B.st (1 : Qp).half.half (D, ν) -∗
      ghostVar K.B.st (1 : Qp).half.half (D, ν) -∗ A -∗ ⧖ (ν + 1) -∗
      iprop(∀ a, ∀ a', ⌜a.cur = C ∧ a.phase = .idle ∧ a'.cur = C' ∧ a'.prev = C ∧
          a'.phase = .committing⌝ -∗ bR c.cg a ={⊤ \ ↑c.N}=∗ bR c.cg a' ∗ cpFired K D Dn ν Q A) := by
  iintro #Hreg H1 H2 Hau #Hrc1 %a %a' %Hf HR
  obtain ⟨hcur, -, hcur', hprev', hph'⟩ := Hf
  obtain ⟨hCD, hCt⟩ := hC
  obtain ⟨hCD', hCt'⟩ := hC'
  unfold bR
  icases HR with ⟨Hcv, ⟨%H, %y, Hh, Hy, %Hfacts⟩, -⟩
  obtain ⟨hHc, hHp, hHle, hy, hpc, -⟩ := Hfacts
  rw [hcur, hCD, hCt] at hHc
  have hfresh : H !! (ν + 1) = none := by
    rcases hk : H !! (ν + 1) with _ | d
    · rfl
    · have := hHle (ν + 1) d hk; rw [hcur, hCt] at this; omega
  imod ghost_map_insert_persist (ν + 1) Dn hfresh $$ Hh with ⟨Hh, #Hnew⟩
  ihave Hau := hA $$ Hau
  iunfold commitAU at Hau
  ihave Hcv : ghostVar c.cg.cv (1 : Qp).half (D, ν) $$ [Hcv]
  · rw [← hCD, ← hCt, ← hcur]; iexact Hcv
  imod au_commit_fire K.B N' D Dn ν Q (ghostVar c.cg.cv (1 : Qp).half (Dn, ν + 1)) (⊤ \ ↑c.N)
    (fun x hx => CoPset.in_diff.2 ⟨CoPset.subseteq_top x (CoPset.in_diff.1 hx).1,
      fun h => (CoPset.in_diff.1 hx).2 (hcN x h)⟩) $$ [H1 H2 Hcv Hau] with ⟨H1, H2, HQ, Hcv⟩
  · iframe H1 H2 Hau
    iintro %o #Hr Hc
    ihave %ho := cnReg_agree K.B (some c.cg) o $$ [Hreg Hr]
    · iframe #
    subst ho
    icases (cpart_some c.cg 1 D ν).1 $$ Hc with ⟨Hcv', -⟩
    imod ghostVar_update_halves (Dn, ν + 1) c.cg.cv _ _ $$ Hcv Hcv' with ⟨Hcv, Hcv'⟩
    imodintro
    iframe Hcv'
    iapply (cpart_some c.cg 1 Dn (ν + 1)).2
    iframe Hcv
    unfold histE; iexact Hnew
  imodintro
  isplitr [H1 H2 HQ]
  · rw [hcur', hCD', hCt']
    iframe Hcv
    isplitl
    · iexists (H.insert (ν + 1) Dn), y
      iframe Hh Hy
      ipureintro
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcur', hCt', GMap.lookup_insert, hCD']
      · rw [hprev', hCt, GMap.lookup_insert_ne _ _ (by omega)]
        rw [hCD]; exact hHc
      · intro k d hk
        rw [hcur', hCt']
        by_cases hkν : k = ν + 1
        · omega
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkν)] at hk
          have := hHle k d hk; rw [hcur, hCt] at this; omega
      · rw [hprev', hCt]
        rcases hpc with h | h
        · have : a.cur.txid = ν := by rw [hcur, hCt]
          omega
        · have : a.prev.txid = ν := by rw [h, hcur, hCt]
          omega
      · left; rw [hprev', hcur', hCt, hCt']
      · rw [hph']; intro h; cases h
    · iexact Hrc1
  unfold cpFired
  ileft
  isplitr
  · ipureintro; exact hfs
  iframe

omit package_sem in
/-- **`writeMeta`'s commit step for a commit** (see the file header). The premises are
`store_publish`'s for `C' = C.publish (metaBuf mv) (metaSummed mv) pages` (spill's and
`commitFreelist`'s posts), the meta's validity, and the new data `Dn = treeData C'`. -/
theorem commitStep_commit (K : BC) (N' : Namespace) (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat)
    (v : View) (wl : Bool) (S : List Nat) (bs : Nat → List w8) (Fb : GMap Nat (List w8))
    (mv : Meta) (pages : Pages) (Dn : Data) (Q A : IProp GF)
    (hA : A ⊢ commitAU K N' (treeData C) Dn Q)
    (htx : mv.txid'.toNat = C.txid + 1) (hval : metaValid (metaSummed mv))
    (hps : (metaSummed mv).pageSize'.toNat = 4096)
    (hDn : treeData (C.publish (metaBuf mv) (metaSummed mv) pages) = Dn)
    (htree : treeOK (C.publish (metaBuf mv) (metaSummed mv) pages))
    (hhwm : (C.publish (metaBuf mv) (metaSummed mv) pages).hwm ≤ 2 ^ 62)
    (hdrop : ∀ s ∈ treeSlots C, s ∉ treeSlots (C.publish (metaBuf mv) (metaSummed mv) pages) →
      s ∈ pendSlots fl)
    (hS : ∀ s, s ∈ S ↔ s ∈ treeSlots (C.publish (metaBuf mv) (metaSummed mv) pages) ∧
      s ∉ slotsOf C fl)
    (hbytes : ∀ id pg, (C.publish (metaBuf mv) (metaSummed mv) pages).pages !! id = some pg →
      C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap bs))
    (hfl : flBelow fl (C.publish (metaBuf mv) (metaSummed mv) pages) (some (C.txid + 1)))
    (hnp : ∀ s ∈ treeSlots (C.publish (metaBuf mv) (metaSummed mv) pages), s ∉ pendSlots fl)
    (hSb : ∀ s ∈ S, (bs s).length = 4096 ∧ W64 (s : Int) ∉ fl.free ∧
      (∀ b' l', (some (b, l) : MapSt) = some (b', l') → s < l' / 4096) ∧ 2 ≤ s)
    (hC'fl : (C.publish (metaBuf mv) (metaSummed mv) pages).flpg = none)
    (hfreed : ∀ f, C.flpg = some f → f ∈ pendSlots fl)
    (hhwmb : (C.publish (metaBuf mv) (metaSummed mv) pages).hwm * 4096 ≤ 0xFFFFFFFFFFFF)
    (om : OsMeta)
    -- W1, crash mode: the new tree inside the file (`DB.grow`), the crash size bounds agreeing
    -- (`Tx.write`'s sync, `m.synced`)
    (hin : K.p.cs ≠ none → (C.publish (metaBuf mv) (metaSummed mv) pages).hwm * 4096 ≤ om.size ∧
      ∀ x ∈ S, 4096 * (x + 1) ≤ om.size)
    (hlh : K.p.cs ≠ none → om.lo = om.hi)
    -- W3: the crash invariant's namespace is inside the update's (it opens around the fire)
    (hN' : (↑(K.N .@ "crash") : CoPset) ⊆ ↑N') :
    K.core (GF := GF) ∗ cpRes K C fl b l v (C.txid + 1) false wl (treeData C) ∗
      slotsOwn (some (b, l)) K.p S bs ∗
      fbTok K.B C fl ((some v, some (C.txid + 1), false, wl) : WSt) Fb ∗
      A ⊢
    commitStep K (mv.txid'.toNat % 2) b (metaBuf mv) C
      (C.publish (metaBuf mv) (metaSummed mv) pages) om
      (cpPost K C (C.publish (metaBuf mv) (metaSummed mv) pages) fl b l v wl S bs Fb Dn Q A) := by
  have hs2 : mv.txid'.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  have hsl : ∀ i, (C.publish (metaBuf mv) (metaSummed mv) pages).slot i =
      if i % 2 = mv.txid'.toNat % 2 then metaBuf mv else C.slot i := by
    intro i; rw [publish_slot, metaSummed_txid]
  have hother : (mv.txid'.toNat % 2 + 1) % 2 ≠ mv.txid'.toNat % 2 := by omega
  have hself : mv.txid'.toNat % 2 % 2 = mv.txid'.toNat % 2 := Nat.mod_mod _ _
  have hmtx : (C.publish (metaBuf mv) (metaSummed mv) pages).txid = mv.txid'.toNat := by
    simp only [CommitSt.publish, metaSummed_txid]
  have htx' : (C.publish (metaBuf mv) (metaSummed mv) pages).txid = C.txid + 1 := hmtx.trans htx
  iintro ⟨#Hcore, Hres, HS, Hfb, Hau⟩
  icases BC.core_bfile K $$ Hcore with ⟨#Hci, -⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  ihave %Hrcpt := isBoltCoreP_receipts K.B K.N K.db K.p K.sp K.t0 $$ Hcore'
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
  iunfold cpRes at Hres
  icases Hres with ⟨Hout, Hcurq, Hfl, Hmap, Hwv, Hopw, Hmcw, Hobw, Hstw⟩
  unfold commitStep
  iintro HR
  iunfold metaR at HR
  icases HR with ⟨%C0, %F, %cl, %fli, %wa, Hcur, Hst, Hcls, Hop, Hfli, Hwa, Hmlk, Hfa, Hro, #Hrcm,
    %Hok, %HF⟩
  icombine Hcur Hcurq gives % ⟨_, hC0⟩
  subst C0
  icombine Hop Hopw gives %hop
  have hcl : cl = false := by
    cases cl
    · rfl
    · simp only [Bool.not_true] at hop; exact absurd hop (by simp)
  subst hcl
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  obtain ⟨hmok, htok, htx1, hhwm0⟩ := Hok rfl
  imod meta_take K.B K.N K.p ⊤ CoPset.subseteq_top C (some (b, l)) $$ [Hpi Hout Hmlk Hcurq Hmap]
    with ⟨Hmcl, Hout, Hcurq, Hmap⟩
  · iframe; iframe #
  icases metaCells_take C b l _ hs2 $$ [Hmcw Hmcl] with ⟨Hold, Hoth⟩
  · iframe
  icases metaOsBytes_take K.p C _ hs2 hmok.1 hmok.2.1 $$ Hobw with ⟨%xa, %xb, Hxa, Hxb, %hxab⟩
  have hslotlen : ∀ i, (C.slot i).length = 4096 := by
    intro i; unfold CommitSt.slot; split
    · exact hmok.1
    · exact hmok.2.1
  have hmeta : (C.publish (metaBuf mv) (metaSummed mv) pages).metaOk :=
    metaOk_parity_write C (metaBuf mv) (metaSummed mv) pages hmok (metaBuf_length mv)
      (metaOf_metaBuf mv) hval (by rw [metaSummed_txid]; exact htx) hps (metaBuf_tail mv)
  have hcur' : (C.publish (metaBuf mv) (metaSummed mv) pages).slot
      (C.publish (metaBuf mv) (metaSummed mv) pages).txid = metaBuf mv := by
    rw [hsl, hmtx, if_pos rfl]
  imodintro
  iexists C.txid
  iframe Hrcm
  iintro #Hrc1 Hm
  -- the early commit point, before the `pwrite` (after the step that raised the receipt): in crash
  -- mode the file's value moves to committing (W1); under `FsNoErr` the update fires
  ihave %hrb := preceipt_lt _ $$ Hrc1
  ihave #Hmd := BC.core_mode K $$ Hcore
  ihave #Hn : (⌜FsNoErr⌝ ∨ cnReg K.B none) $$ []
  · cases hc : K.p.cs with
    | none => iright; iapply bMode_none K.B K.N K.db K.p hc $$ Hmd
    | some c =>
      ileft
      icases bMode_some K.B K.N K.db K.p c hc $$ Hmd with ⟨%hcm, -⟩
      ipureintro; exact hcm.2.2
  ihave Hstep : (|={⊤}=> bMetaCm K.p (C.publish (metaBuf mv) (metaSummed mv) pages) C [] om ∗
      slotsOwn (some (b, l)) K.p S bs ∗ cpFired K (treeData C) Dn C.txid Q A) $$ [Hm HS Hst Hstw Hau]
  · cases hc : K.p.cs with
    | none =>
      rw [bMeta_none hc, bMetaCm_none hc]
      ihave #Hreg := bMode_none K.B K.N K.db K.p hc $$ Hmd
      imod cpFired_intro K N' (treeData C) Dn C.txid Q A hA $$ [Hst Hstw Hau] with Hpt
      · iframe; iframe #
      imodintro; iframe
    | some c =>
      icases bMode_some K.B K.N K.db K.p c hc $$ Hmd with ⟨%hcm, #Hreg⟩
      have hcN : (↑c.N : CoPset) ⊆ ↑N' := by rw [hcm.2.1]; exact hN'
      imod bMeta_commit K.p c hc C (C.publish (metaBuf mv) (metaSummed mv) pages) om (some (b, l)) S
        bs htx' (by have := Hrcpt.2; omega)
        (fun i hi => by rw [hsl, if_neg (by rw [← hmtx]; exact hi)]) hmeta htree hC'fl
        hbytes
        (fun x hx => (hSb x hx).1) hin hlh (cpFired K (treeData C) Dn C.txid Q A)
        $$ Hci Hm HS [Hst Hstw Hau] with ⟨Hm, HS, Hpt⟩
      · iapply cp_fire_crash K N' c hcN (treeData C) Dn C.txid Q A hA hcm.2.2 C
          (C.publish (metaBuf mv) (metaSummed mv) pages) ⟨rfl, rfl⟩ ⟨hDn, htx'⟩ $$ Hreg Hst Hstw Hau Hrc1
      imodintro; iframe
  imod Hstep with ⟨Hm, HS, Hpt⟩
  imodintro
  iexists xa, C.slot (mv.txid'.toNat % 2)
  iframe Hxa Hold Hm
  isplitr
  · ipureintro
    have := congrArg List.length hxab.1
    simp only [List.length_map] at this
    exact ⟨this.trans (hslotlen _), hslotlen _, fun _ => ⟨by rw [hmtx], hcur'⟩⟩
  iintro %j %ys %hj Hnew Hrc
  obtain ⟨hj01, hne, hys⟩ := hj
  rcases hj01 with rfl | rfl
  · -- nothing written (so the file system can fail): everything back, the update unfired
    iunfold cpFired at Hpt
    icases Hpt with (⟨%hfs, -, -, -⟩ | ⟨-, Hst, Hstw, Hau⟩)
    · exact absurd (hne hfs) (by decide)
    simp only [↓reduceIte] at hys
    ihave Hnew : bytesPointsto (b +ₗ ((4096 * (mv.txid'.toNat % 2) : Nat) : Int))
        (DFrac.own (1 : Qp).half) (C.slot (mv.txid'.toNat % 2)) $$ [Hnew]
    · rw [hys, hxab.1]; iexact Hnew
    icases metaCells_put C b l _ hs2 $$ [Hnew Hoth] with ⟨Hmcw, Hmcl⟩
    · iframe
    imod meta_put K.B K.N K.p ⊤ CoPset.subseteq_top C (some (b, l)) $$ [Hpi Hout Hmcl Hcurq Hmap]
      with ⟨Hout, Hmlk, Hcurq, Hmap⟩
    · iframe; iframe #
    imodintro
    isplitl [Hcur Hst Hcls Hop Hfli Hwa Hmlk Hfa Hro]
    · iunfold metaR
      iexists C, F, false, fli, wa
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      iframe Hrcm
      iframe
      ipureintro; exact ⟨fun _ => ⟨hmok, htok, htx1, hhwm0⟩, HF⟩
    iintro %ys' %hys' Hys
    icases metaOsBytes_put K.p C _ hs2 hmok.1 hmok.2.1 ys' xb (hys'.trans (hys.trans hxab.1)) hxab.2
      $$ [Hys Hxb] with Hobw
    · iframe
    unfold cpPost
    iright
    isplitr
    · ipureintro; rfl
    iunfold cpRes
    iframe
  · -- the page written whole: the commit point
    simp only [show (4096 : Nat) ≠ 0 from by decide, ↓reduceIte] at hys
    imod store_publish K.B K.N K.p ⊤ CoPset.subseteq_top C _ fl (some (b, l)) v (C.txid + 1) wl S bs
      Fb htx' hmeta htree hhwm hdrop hS hbytes hfl hnp hSb (by simp) hC'fl hfreed
      $$ [Hpi Hcur Hcurq Hfl Hmap Hwv HS Hout Hfb] with ⟨Hcur, Hcurq, Hfl, Hmap, Hwv, Hout⟩
    · iframe; iframe #
      iapply (ghostVar_split_half K.B.cur (1 : Qp).half C).1 $$ Hcur
    imod cpFired_land K N' (treeData C) Dn C.txid Q A hA $$ [Hpt] with ⟨Hst, Hstw, HQ⟩
    · iframe; iframe #
    have hlen' : ∀ i, ((C.publish (metaBuf mv) (metaSummed mv) pages).slot i).length = 4096 := by
      intro i; rw [hsl]; split
      · exact metaBuf_length mv
      · exact hslotlen i
    ihave Hnew : bytesPointsto (b +ₗ ((4096 * (mv.txid'.toNat % 2) : Nat) : Int))
        (DFrac.own (1 : Qp).half)
        ((C.publish (metaBuf mv) (metaSummed mv) pages).slot (mv.txid'.toNat % 2)) $$ [Hnew]
    · rw [hsl, ite_eq_left hself, ← hys]; iexact Hnew
    ihave Hoth : bytesPointsto (b +ₗ ((4096 * (1 - mv.txid'.toNat % 2) : Nat) : Int))
        (DFrac.own (1 : Qp).half)
        ((C.publish (metaBuf mv) (metaSummed mv) pages).slot (mv.txid'.toNat % 2 + 1)) $$ [Hoth]
    · rw [hsl, ite_eq_right hother]; iexact Hoth
    have hm0' : (C.publish (metaBuf mv) (metaSummed mv) pages).m0.length = 4096 := hmeta.1
    have hm1' : (C.publish (metaBuf mv) (metaSummed mv) pages).m1.length = 4096 := hmeta.2.1
    icases metaCells_put _ b l _ hs2 $$ [Hnew Hoth] with ⟨Hmcw, Hmcl⟩
    · iframe
    imod meta_put K.B K.N K.p ⊤ CoPset.subseteq_top _ (some (b, l)) $$ [Hpi Hout Hmcl Hcurq Hmap]
      with ⟨Hout, Hmlk, Hcurq, Hmap⟩
    · iframe; iframe #
    imodintro
    isplitl [Hcur Hst Hcls Hop Hfli Hwa Hmlk Hfa Hro]
    · iunfold metaR
      iexists (C.publish (metaBuf mv) (metaSummed mv) pages), F, false, fli, wa
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [hDn, htx']
      iframe Hrc1
      iframe
      ipureintro
      refine ⟨fun _ => ⟨hmeta, htree, by omega, hhwmb⟩, fun k t h => ?_⟩
      have := HF k t h
      omega
    iintro %ys' %hys' Hys
    icases metaOsBytes_put K.p _ _ hs2 hm0' hm1' ys' xb
      (by rw [hsl, ite_eq_left hself, hys']; exact hys)
      (by rw [hsl, ite_eq_right hother]; exact hxab.2)
      $$ [Hys Hxb] with Hobw
    · iframe
    unfold cpPost
    ileft
    isplitr
    · ipureintro; rfl
    iunfold cpRes
    rw [htx']
    iframe


end step

end bbolt
end EtcdGrove
end Perennial
