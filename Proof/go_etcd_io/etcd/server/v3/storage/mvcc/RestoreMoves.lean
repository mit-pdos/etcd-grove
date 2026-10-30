/-
**`store.Restore`'s ghost moves** (the restore plan's R5e, `notes/restore-plan.md`): the takeover
of the store's logical state under `s.mu` and `s.revMu` (the writer's state out of its invariant,
`s.revMu`'s body, the committed log and the index's history moved from `L` to the restored log
`L'`), and the switch, at `restore`'s last unlock of `s.revMu`, of the store's current objects and
physical names to the new backend, index and scheduler (`cur`'s eight parts gathered, the readers'
pool refilled, `s.revMu`'s body at the new names). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ### The history of a longer log -/

theorem histOfFrom_append_log (i : Nat) : ∀ (A B : Log),
    histOfFrom i (A ++ B) = histOfFrom i A ++ histOfFrom (i + A.length) B
  | [], B => by simp [histOfFrom]
  | cs :: A, B => by
    rw [List.cons_append, histOfFrom, histOfFrom, histOfFrom_append_log (i + 1) A B]
    simp only [List.length_cons, List.append_assoc]
    rw [show i + 1 + A.length = i + (A.length + 1) by omega]

/-- **The history is prefix-monotone in the log.** -/
theorem histOf_mono {L L' : Log} (h : L <+: L') : histOf L <+: histOf L' := by
  obtain ⟨B, rfl⟩ := h
  unfold histOf
  rw [histOfFrom_append_log]
  exact List.prefix_append _ _

theorem histShape_nil (L : Log) : histShape L [] = histOf L := by
  simp [histShape, evsOfRev]

section moves
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The committed log's authority, gathered: the writer's half, `s.revMu`'s part (`revQ`) and, for a
watchable store's, the outer quarter (`logQ`). -/
theorem logAuth_gather (γ : StoreNames) (l : Log) :
    idxLogAuth (GF := GF) γ.idx (1 : Qp).half l ∗ idxLogAuth γ.idx (revQ γ 1) l ∗
      (if γ.watchQ then logQ γ l else iprop(True)) ⊢ idxLogAuth γ.idx 1 l := by
  have h1 := (monoListAuthOwn_fractional (GF := GF) γ.idx.log l).fractional (1 : Qp).half
    (1 : Qp).half
  have h2 := (monoListAuthOwn_fractional (GF := GF) γ.idx.log l).fractional (1 : Qp).half.half
    (1 : Qp).half.half
  rw [Qp.half_add_half] at h1 h2
  unfold revQ logQ
  cases γ.watchQ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H1, H2, -⟩
    iapply h1.2; iframe H1 H2
  · simp only [↓reduceIte]
    iintro ⟨H1, H2, H3⟩
    ihave H23 : idxLogAuth (GF := GF) γ.idx (1 : Qp).half l $$ [H2 H3]
    · iapply h2.2; iframe H2 H3
    iapply h1.2; iframe H1 H23

/-- The committed log's authority, split back (`logAuth_gather`). -/
theorem logAuth_split (γ : StoreNames) (l : Log) :
    idxLogAuth (GF := GF) γ.idx 1 l ⊢ idxLogAuth γ.idx (1 : Qp).half l ∗
      idxLogAuth γ.idx (revQ γ 1) l ∗ (if γ.watchQ then logQ γ l else iprop(True)) := by
  have h1 := (monoListAuthOwn_fractional (GF := GF) γ.idx.log l).fractional (1 : Qp).half
    (1 : Qp).half
  have h2 := (monoListAuthOwn_fractional (GF := GF) γ.idx.log l).fractional (1 : Qp).half.half
    (1 : Qp).half.half
  rw [Qp.half_add_half] at h1 h2
  unfold revQ logQ
  cases γ.watchQ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro H
    icases h1.1 $$ H with ⟨H1, H2⟩
    iframe H1 H2
  · simp only [↓reduceIte]
    iintro H
    icases h1.1 $$ H with ⟨H1, H2⟩
    icases h2.1 $$ H2 with ⟨H2, H3⟩
    iframe H1 H2 H3

/-- **What `store.Restore` holds of the store's logical state** from its takeover of the writer's
state and `s.revMu`'s body to `restore`'s last unlock of `s.revMu` (the restore plan's R5e), at the
restored log `L'`: the committed log's ghost variable and its authority, whole; the revision
budget's authority, no token out (the tokens of the old log deleted: the restored log's are made at
the unlock, when its length is known to be small); `s.revMu`'s quarter of the compaction
revision's authority, at `-1`; the writer's reader slot of the lessor; the lower bounds of the
history and the committed log at `L'`. -/
def restoreHeld (γ : StoreNames) (L' : Log) : IProp GF :=
  iprop("Hclog" ∷ ghostVar γ.clog 1 L' ∗
    "Hlog" ∷ idxLogAuth γ.idx 1 L' ∗
    "Htoks" ∷ ownTokAuth γ.revs 0 ∗
    "Hcrev" ∷ crevUB γ.idx (1 : Qp).half.half (-1) ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "Hhist" ∷ monoListAuthOwn γ.idx.hist (1 : Qp).half (histOf L') ∗
    "#Hhlb" ∷ monoListLbOwn γ.idx.hist (histOf L') ∗
    "#Hllb" ∷ monoListLbOwn γ.idx.log L')

/-- **The takeover** (one later credit; `store.Restore` holds `s.mu` exclusively, `s.revMu` locked):
`s.revMu`'s body (not restoring: `s.mu`'s share of the fields holds the flag down) and the writer's
state (in its invariant: `s.mu`'s deposit ghost, whole, excludes a writer's deposit and the
restoring state) taken out; the committed log is the caller's certified `L` (the revision tokens of
`L` it holds are all the budget leaves); the committed log, its authority and the index's history
moved to `L'`; the writer's invariant left in its restoring state, with the deposit ghost and the
history's authority. Returned: `currentRev` and `compactMainRev` whole (the latter at `-1`, the
store never compacted), the restoring flag whole and down, `s.revMu`'s and the writer's eighths of
the current objects and names, and `restoreHeld`. -/
theorem restore_takeover (s : Loc) (γ : StoreNames) (o : StoreObjs) (L L' : Log)
    (hLL : L <+: L') :
    ⊢ £ 1 -∗ writerInv (GF := GF) s γ -∗ revMuInv s γ 1 -∗
      dghostVar γ.rst (DFrac.own (1 : Qp).half) false -∗ curAt γ (DFrac.own (1 : Qp).half) o -∗
      ghostVar γ.wr 1 () -∗ idxCert γ.idx L -∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) -∗
      (if γ.watchQ then logQ γ L else iprop(True)) -∗
      crevUB γ.idx (1 : Qp).half.half (-1) -∗
      (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) ={⊤}=∗
      (∃ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own 1} v : IProp GF)) ∗
      (s.[store, go!"compactMainRev"] ↦{DFrac.own 1} (W64 (-1) : w64) : IProp GF) ∗
      dghostVar γ.rst (DFrac.own 1) false ∗ curAt γ (DFrac.own (1 : Qp).half) o ∗
      curAt γ (DFrac.own (1 : Qp).half.half.half) o ∗ curAt γ (DFrac.own (1 : Qp).half.half.half) o ∗
      crevUB γ.idx (1 : Qp).half.half (-1) ∗ restoreHeld γ L' ∗
      monoListLbOwn γ.idx.hist (histShape L' []) := by
  iintro Hlc #Hwi HR Hrst Hcur Hwr #HcL Hrv HlogQ Hcrev Hcmp
  -- `s.revMu`'s body, at the current names
  icases revMuInv_open_cur s γ 1 _ _ o $$ [HR Hrst Hcur] with ⟨HB, HT, Hrst, Hcur⟩
  · iframe HR Hrst Hcur
  iunfold revMuTok at HT
  icases HT with ⟨Hrst2, ⟨%o2, Hcur2⟩, -⟩
  ihave %Ho2 := curAt_agree_o γ _ _ o o2 $$ [Hcur Hcur2]
  · iframe Hcur Hcur2
  subst Ho2
  iunfold revMuBody at HB
  icases HB with ⟨%log, %ntb, %cb, HB⟩
  iNamedSuffix HB "B"
  obtain ⟨HcB1, HcB2⟩ := HcB
  -- the writer's state
  iunfold writerInv at Hwi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hwi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨Hwr2, -⟩)
  rotate_left 1
  · ihave %Hv := ghostVar_valid_2 γ.wr () 1 () 1 $$ Hwr Hwr2
    exact absurd Hv.1 (Qp_one_add_not_le 1)
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hcur Hc]
  · iframe Hcur Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨HL, -⟩ | ⟨-, Hd, -⟩)
  rotate_left 1
  · iunfold wDep at Hd
    ihave %Hv := ghostVar_valid_2 γ.wr () 1 () _ $$ Hwr Hd
    exact absurd Hv.1 (Qp_one_add_not_le _)
  iunfold writerL at HL
  icases HL with ⟨%ilog, %ntw, HL⟩
  iNamed HL
  iunfold idxWriter at Hw
  icases Hw with ⟨Hhist, -, %Hwf, Hlw, -⟩
  -- the committed log is the writer's, and the caller's certified log
  icases ghostVar_join_halves γ.clog log ilog $$ [HclogB Hclog] with ⟨Hclog, %Hlog⟩
  · iframe HclogB Hclog
  subst Hlog
  ihave %HpL := idxLogAuth_cert_prefix γ.idx _ log L $$ [Hlw HcL]
  · iframe Hlw; iexact HcL
  icombine HtoksB Htoks gives %Hn
  obtain ⟨-, Hn⟩ := Hn
  subst Hn
  ihave Htoks : ownTokAuth γ.revs ntb $$ [HtoksB Htoks]
  · iapply (ownTokAuth_halves γ.revs ntb).2; iframe HtoksB Htoks
  icombine Htoks Hrv gives %Hge
  have hlen : log.length ≤ L.length := by
    have := HpL.length_le; omega
  have hLeq : L = log := HpL.eq_of_length (by have := HpL.length_le; omega)
  subst hLeq
  -- the committed log's authority, whole, at `L'`
  ihave HlogQ : (if γ.watchQ then logQ γ L else iprop(True)) $$ [HlogQ]
  · iexact HlogQ
  ihave Hla := logAuth_gather γ L $$ [Hlw HlogB HlogQ]
  · iframe Hlw HlogB HlogQ
  imod monoListAuthOwn_update L' hLL $$ Hla with ⟨Hla, #Hllb⟩
  imod ghostVar_update L' γ.clog L $$ Hclog with Hclog
  -- the index's history at `L'`
  rw [histShape_nil]
  imod monoListAuthOwn_update (histOf L') (histOf_mono hLL) $$ Hhist with ⟨Hhist, #Hhlb⟩
  -- the revision budget: the caller's tokens are all of it
  imod ownTokAuth_sub (2 ^ 63 - 3 - L.length) γ.revs ntb $$ Htoks Hrv with Htoks
  rw [show ntb - (2 ^ 63 - 3 - L.length) = 0 by omega]
  -- the compaction revision: `-1`
  ihave %Hcb := crevUB_agree γ.idx _ _ cb (-1) HcB1 (by decide) $$ HcrevB Hcrev
  subst Hcb
  -- `currentRev` and `compactMainRev`, whole
  ihave Hcm : (s.[store, go!"compactMainRev"] ↦{DFrac.own 1} (W64 (-1) : w64) : IProp GF)
      $$ [HcmpB Hcmp]
  · iapply (typedPointsto_parts (GF := GF) _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).2
    iframe HcmpB Hcmp
  ihave Hcr : (s.[store, go!"currentRev"] ↦{DFrac.own 1} (W64 ((L.length : Int) - 1) : w64) :
      IProp GF) $$ [HrevB Hcur]
  · iapply (typedPointsto_parts (GF := GF) _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).2
    iframe HrevB Hcur
  -- the restoring flag, whole
  ihave Hrst : dghostVar (GF := GF) γ.rst (DFrac.own 1) false $$ [Hrst Hrst2]
  · have h := (dghostVar_fractional (GF := GF) γ.rst false).fractional (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at h
    iapply h.2
    iframe Hrst Hrst2
  -- the writer's invariant, restoring, with half the history's authority
  have hh := (monoListAuthOwn_fractional (GF := GF) γ.idx.hist (histOf L')).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hh
  icases hh.1 $$ Hhist with ⟨Hhist, HhistI⟩
  imod Hclose $$ [Hwr HhistI] with -
  · inext; iunfold writerInvBody; iright; iframe Hwr; iexists _; iexact HhistI
  imodintro
  iframe Hcm Hrst Hcur Hcur2 Hc HcrevB
  isplitl [Hcr]
  · iexists _; iexact Hcr
  isplitl [Hclog Hla Htoks Hcrev Hlrd Hhist]
  · iunfold restoreHeld
    simp only [named]
    iframe Hclog Hla Htoks Hcrev Hlrd Hhist
    iframe #
  rw [histShape_nil]
  iexact Hhlb

/-- `a + b` copies of `P`, in two parts. -/
theorem rep_split (P : IProp GF) (a b : Nat) :
    ([∗list] _x ∈ List.replicate (a + b) (), P) ⊣⊢
      ([∗list] _x ∈ List.replicate a (), P) ∗ ([∗list] _x ∈ List.replicate b (), P) := by
  rw [← List.replicate_append_replicate]
  exact BigSepL.bigSepL_append

/-- The readers' pool's slots, apart: the index's reader slots and the backend's tokens. -/
theorem idxSlots_out (γ : StoreNames) (o : StoreObjs) : ∀ (n : Nat),
    ([∗list] _x ∈ List.replicate n (), idxSlot (GF := GF) γ o) ⊢
      ([∗list] _x ∈ List.replicate n (), idxReader o.ti γ.idx) ∗
        ([∗list] _x ∈ List.replicate n (), storeRT γ)
  | 0 => by
    rw [List.replicate_zero]; iintro _
    isplitl [] <;> (iapply BigSepL.bigSepL_nil_intro; iempintro)
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
    iunfold idxSlot at H1
    icases H1 with ⟨Hi1, Ht1⟩
    icases idxSlots_out γ o n $$ Hs with ⟨Hi, Ht⟩
    isplitl [Hi1 Hi]
    · iapply BigSepL.bigSepL_cons.2; iframe Hi1 Hi
    · iapply BigSepL.bigSepL_cons.2; iframe Ht1 Ht

/-- **The writer's state at the restored log `L'`, but its index handle** (what `store.Restore` keeps
from `restore`'s last unlock of `s.revMu` to its return, which gives the receipts and `currentRev`'s
other half): half the committed log's ghost variable and of its authority, half the revision
budget's authority with its bound, the lessor's reader slot, the certificate of `L'`. -/
def restoreWriter (γ : StoreNames) (L' : Log) : IProp GF :=
  iprop(∃ ntok : Nat,
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half L' ∗
    "Hlw" ∷ idxLogAuth γ.idx (1 : Qp).half L' ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜L'.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "Hhist" ∷ monoListAuthOwn γ.idx.hist (1 : Qp).half (histOf L') ∗
    "#Hcert" ∷ idxCert γ.idx L')

/-- The restored log's view, as `s.revMu`'s body holds it. -/
theorem restoreViewOut_bucketView (γ : StoreNames) (q : Qp) (R : Log) :
    restoreViewOut (GF := GF) γ q R ⊢ bucketView γ q (bucketMap ([[], []] ++ R)) := by
  unfold restoreViewOut
  by_cases hR : R = []
  · subst hR
    simp only [↓reduceIte, List.append_nil, bucketMap_init]
    iintro H
    iexact H
  · simp only [hR, ↓reduceIte]
    iintro H
    iapply bucketViewC_bucketView $$ H

/-- **The switch** (one later credit; inside `restore`'s last unlock of `s.revMu`, `store.Restore`
holding `s.mu` exclusively): `cur`'s eight parts gathered (the shares' half, the writer's fragment,
`s.revMu`'s and the writer's invariant's eighths from the takeover, the readers' pool's) and moved to
the new objects `o'` and names `p'`; the readers' pool refilled with `k` slots of the new index and
backend (the old ones' backend tokens returned; D22 receiver epochs, S8d, W7, 2026-10-25: exactly
`nReaders - 2`, the pool's retired count being `2`, `retiredAt`, and no slot out: none under the
watchable store's lock, whose deposit the caller holds, none under `s.mu`, whose deposit ghost the
writer's invariant holds whole in its restoring state, a second later credit); the restoring flag
down; `s.revMu`'s resource at the new names, with the restored log's
bucket view (`restoreViewOut`), its certificate (its changes below the receipts' bound, which the
rebuild's receipts give) and the revision budget's tokens of `L'` made. -/
theorem restore_switch (s : Loc) (γ : StoreNames) (o o' : StoreObjs) (p' : PhysNames) (R : Log)
    (hR : restoreLogOk R) :
    ⊢ £ 1 -∗ £ 1 -∗ writerInv (GF := GF) s γ -∗ wsDep γ -∗ readerPool (GF := GF) γ -∗
      curAt γ (DFrac.own (1 : Qp).half) o -∗ writerFrag γ -∗
      curAt γ (DFrac.own (1 : Qp).half.half.half) o -∗ curAt γ (DFrac.own (1 : Qp).half.half.half) o -∗
      retiredAt γ 2 -∗
      dghostVar γ.rst (DFrac.own (1 : Qp).half) true -∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) true -∗
      restoreHeld γ ([[], []] ++ R) -∗
      (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
        (W64 ((([[], []] ++ R).length : Int) - 1) : w64) : IProp GF) -∗
      (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) -∗
      monoNatLbOwn p'.nev (evsOf (([[], []] ++ R) ++ [[]])).length -∗ certOk γ ([[], []] ++ R) -∗
      restoreViewOut (γ.withPhys p') (1 : Qp).half R -∗
      ([∗list] _x ∈ List.replicate nReaders (), idxReader o'.ti (γ.withPhys p').idx) -∗
      ⌜logCh ([[], []] ++ R) < receiptBound GF⌝ -∗ ⌜receiptBound GF ≤ 2 ^ 48⌝ -∗
      ([∗list] _x ∈ List.replicate (nReaders - 1) (), storeRT (γ.withPhys p')) ={⊤}=∗
      revMuInv s γ 1 ∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) false ∗
      curAt (γ.withPhys p') (DFrac.own (1 : Qp).half) o' ∗ writerFrag (γ.withPhys p') ∗
      curAt (γ.withPhys p') (DFrac.own (1 : Qp).half.half.half) o' ∗ retiredAt γ 2 ∗ wsDep γ ∗
      restoreWriter γ ([[], []] ++ R) ∗ ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then logQ γ ([[], []] ++ R) else iprop(True)) ∗
      ([∗list] _x ∈ List.replicate (nReaders - 2) (), storeRT γ) ∗ storeRT (γ.withPhys p') := by
  iintro Hlc Hlc' #Hwi Hwsd #Hpool Hc1 Hfrag Hc2 Hc3 Htkr Hr1 Hr2 Hheld Hrev Hcmp #Hnv #Hok Hview
    Hrds %Hrc %Hrb Hrts
  have hlen := restoreLogOk_len hR
  obtain ⟨-, hwf, -⟩ := hR
  have hwfL : LogWf' ([[], []] ++ R) := hwf.1.prefix
  iunfold restoreHeld at Hheld
  iNamed Hheld
  -- the readers' pool, at the current names
  iunfold readerPool at Hpool
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hpool with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%pp, %op, Hc4, HP⟩
  ihave %Hv := curAt_pin γ pp _ _ o op $$ [Hc1 Hc4]
  · iframe Hc1 Hc4
  obtain ⟨Hop, rfl⟩ := Hv
  subst op
  rw [StoreNames.withPhys_self]
  iunfold writerFrag at Hfrag
  icases Hfrag with ⟨%of, Hc5⟩
  ihave %Hof := curAt_agree_o γ _ _ o of $$ [Hc1 Hc5]
  · iframe Hc1 Hc5
  subst Hof
  -- `cur` whole, moved to the new objects and names
  ihave Hcur : curAt (GF := GF) γ (DFrac.own 1) o $$ [Hc1 Hc2 Hc3 Hc4 Hc5]
  · iapply (curAt_halves γ 1 o).2
    iframe Hc1
    iapply (curAt_halves γ _ o).2
    isplitl [Hc2 Hc3]
    · iapply (curAt_halves γ _ o).2; iframe Hc2 Hc3
    · iapply (curAt_halves γ _ o).2; iframe Hc4 Hc5
  -- (W7) the writer's invariant: restoring (all of `cur` is here), with `s.mu`'s deposit ghost
  ihave #Hwi' := Hwi
  iunfold writerInv at Hwi'
  imod inv_acc (E := ⊤ \ ↑poolN) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by solve_ndisj) $$ Hwi' with ⟨HW, Hclose2⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc' HW with HW
  iunfold writerInvBody at HW
  icases HW with (⟨%pw, %ow, Hcw, -⟩ | ⟨Hwr, Hwh⟩)
  · iunfold curAt at Hcur Hcw
    simp only [StoreNames.withPhys_cur]
    ihave %Hv := dghostVar_valid_2 (GF := GF) γ.cur _ _ _ _ $$ Hcur Hcw
    exfalso
    have := DFrac.valid_own_op Hv.1
    have h1 : (1 : Qp).val = 1 := rfl
    have h2 : 0 < (1 : Qp).half.half.half.val := Subtype.property _
    grind
  iunfold curAt at Hcur
  imod dghostVar_update ((o', p') : StoreObjs × PhysNames) γ.cur _ $$ Hcur with Hcur
  ihave Hcur : curAt (GF := GF) (γ.withPhys p') (DFrac.own 1) o' $$ [Hcur]
  · iunfold curAt; simp only [StoreNames.withPhys_cur, StoreNames.withPhys_phys]; iexact Hcur
  icases (curAt_halves _ 1 o').1 $$ Hcur with ⟨Hn1, Hcur⟩
  icases (curAt_halves _ _ o').1 $$ Hcur with ⟨Hq1, Hq2⟩
  icases (curAt_halves _ _ o').1 $$ Hq1 with ⟨Hn2, Hn3⟩
  icases (curAt_halves _ _ o').1 $$ Hq2 with ⟨Hn4, Hn5⟩
  -- the readers' pool refilled: `k` slots of the new index and backend
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  -- (W7) the retired count is the caller's `2`
  iunfold retiredAt at Htkr
  ihave %Hr := ghostVar_agree (GF := GF) γ.tkr r _ 2 _ $$ Har Htkr
  subst Hr
  -- no slot out under the watchable store's lock: its deposit is the caller's
  obtain ⟨w', rfl⟩ | rfl : (∃ w', w = w' + 1) ∨ w = 0 := by cases w <;> simp
  · rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hws with ⟨Hw1, -⟩
    iunfold wsDep at Hw1 Hwsd
    ihave %Hv := ghostVar_valid_2 (GF := GF) γ.wsd () 1 () 1 $$ Hw1 Hwsd
    exact absurd Hv.1 (Qp_one_add_not_le 1)
  -- none under `s.mu`: its deposit ghost is whole in the writer's invariant
  obtain ⟨j', rfl⟩ | rfl : (∃ j', j = j' + 1) ∨ j = 0 := by cases j <;> simp
  · rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hds with ⟨Hd1, -⟩
    iunfold wDep at Hd1
    ihave %Hv := ghostVar_valid_2 (GF := GF) γ.wr () 1 () _ $$ Hwr Hd1
    exact absurd Hv.1 (Qp_one_add_not_le _)
  imod Hclose2 $$ [Hwr Hwh] with -
  · inext; iunfold writerInvBody; iright; iframe Hwr Hwh
  have hk1 : k + 1 ≤ nReaders := by omega
  icases idxSlots_out γ o k $$ Hs with ⟨-, Hold⟩
  obtain ⟨m, hm⟩ : ∃ m, nReaders = k + 1 + m := ⟨nReaders - (k + 1), by omega⟩
  rw [hm, show k + 1 + m - 1 = k + m by omega, show k + 1 + m = k + (1 + m) by omega]
  icases (rep_split _ k (1 + m)).1 $$ Hrds with ⟨Hrk, -⟩
  icases (rep_split _ k m).1 $$ Hrts with ⟨Htk, Hrts⟩
  ihave Hnew := idxSlots_of (γ.withPhys p') o' k $$ [Hrk Htk]
  · iframe Hrk Htk
  imod Hclose $$ [Hn5 Ha Hao Haw Har Hnew Hds Hws] with -
  · inext
    iexists p', o'
    iframe Hn5
    iunfold poolBody
    iexists k, 0, 0, 2
    withPhys_simp
    iframe Ha Hao Haw Har Hnew Hds Hws
    ipureintro; omega
  -- the restoring flag down
  imod dghostVar_update_halves false γ.rst true true $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
  -- the revision budget's tokens of `L'`
  imod ownTokAuth_add (2 ^ 63 - 3 - ([[], []] ++ R).length) γ.revs 0 $$ Htoks with ⟨Htoks, Hrv⟩
  rw [Nat.zero_add]
  icases (ownTokAuth_halves γ.revs _).1 $$ Htoks with ⟨HtoksW, HtoksB⟩
  -- the committed log's ghost variable and authority, split
  icases ghostVar_halves γ.clog _ $$ Hclog with ⟨HclogW, HclogB⟩
  icases logAuth_split γ _ $$ Hlog with ⟨Hlw, HlogB, HlogQ⟩
  have hsmall : ([[], []] ++ R).length + 3 ≤ 2 ^ 63 := by omega
  ihave #Hcert : idxCert (GF := GF) γ.idx ([[], []] ++ R) $$ []
  · iunfold idxCert
    iframe Hhlb Hllb
    ipureintro
    refine ⟨⟨hwfL, by omega, fun cs hcs => hwf.2.2.2 cs hcs⟩, Hrc⟩
  have hevs : (evsOf (([[], []] ++ R) ++ [[]])).length = (evsOf ([[], []] ++ R)).length := by
    rw [evsOf_append ([[], []] ++ R) []]; simp [evsOfRev]
  rw [hevs]
  ihave Hbv := restoreViewOut_bucketView (γ.withPhys p') _ R $$ Hview
  imodintro
  isplitl [Hr1 Hn2 Hrev HclogB Hbv HtoksB HlogB Hcmp Hcrev]
  · iapply revMuInv_close s γ (γ.withPhys p') 1
    isplitl [Hrev HclogB Hbv HtoksB HlogB Hcmp Hcrev]
    · iunfold revMuBody
      iexists ([[], []] ++ R), (2 ^ 63 - 3 - ([[], []] ++ R).length), (-1)
      simp only [named]
      iframe Hrev HclogB Hbv HtoksB HlogB Hcmp Hcrev
      iframe #
      isplitl []
      · iunfold idxNevLb; simp only [StoreNames.withPhys_idx_nev]; iexact Hnv
      ipureintro
      refine ⟨by simp, by omega, by decide, by simp; omega⟩
    · iunfold revMuTok
      iframe Hr1
      isplitl [Hn2]
      · iexists o'; iexact Hn2
      ipureintro; rfl
  ihave Htkr : retiredAt (GF := GF) γ 2 $$ [Htkr]
  · iunfold retiredAt; iexact Htkr
  iframe Hr2 Hn1 Hn4 Hrv HlogQ Hwsd Htkr
  isplitl [Hn3]
  · iunfold writerFrag; iexists o'; iexact Hn3
  isplitl [HclogW Hlw HtoksW Hlrd Hhist]
  · iunfold restoreWriter
    iexists (2 ^ 63 - 3 - ([[], []] ++ R).length)
    simp only [named]
    iframe HclogW Hlw HtoksW Hlrd Hhist Hcert
    ipureintro; omega
  have hm1 : m = 1 := by omega
  subst hm1
  rw [show k + (1 + 1) - 2 = k by omega]
  iframe Hold
  simp only [List.replicate]
  icases BigSepL.bigSepL_cons.1 $$ Hrts with ⟨H, -⟩
  iexact H

/-- **The writer's state checked in at the restored log** (one later credit; after `restore`, which
gives `currentRev`'s other half and the rebuild's receipts): the writer's invariant is in its
restoring state (a writer's state at the new names would have half the new view log's ghost, a
writer's deposit the new batch lock's key: `store.Restore` holds both whole), whose half of the
history's authority is at `L'`; the writer's state at `L'` and the new names goes in, with the new
backend's registration pending (`writerReg`: the right to register, the batch lock's resource:
the new key, half the new view log, half the new bucket's view, the certificate, the compaction's
fresh record). `s.mu`'s deposit ghost back. -/
theorem restore_finish (s : Loc) (γ : StoreNames) (o' : StoreObjs) (p' : PhysNames) (L' : Log)
    (hwf : IdxWf L' []) (hne : L' ≠ []) :
    ⊢ £ 1 -∗ writerInv (GF := GF) s γ -∗
      curAt (γ.withPhys p') (DFrac.own (1 : Qp).half.half.half) o' -∗ restoreWriter γ L' -∗
      (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 ((L'.length : Int) - 1) : w64) :
        IProp GF) -∗ ⧗ (logCh L') -∗ monoNatLbOwn p'.nev (evsOf (L' ++ [[]])).length -∗
      ghostVar p'.wk 1 () -∗ ghostVar p'.wv 1 L' -∗
      bucketView (γ.withPhys p') (1 : Qp).half (bucketMap L') -∗ compactRes (γ.withPhys p') -∗
      kbRegRight p'.kb ={⊤}=∗ ghostVar γ.wr 1 () ∗ idxCert γ.idx L' := by
  iintro Hlc #Hwi Hc Hw Hcur Hrc #Hnv Hwk Hwv Hbv Hcres Hrr
  iunfold restoreWriter at Hw
  icases Hw with ⟨%ntok, Hw⟩
  iNamed Hw
  iunfold writerInv at Hwi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hwi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o, Hc2, HP⟩ | ⟨Hwr, %h, Hh⟩)
  · -- a writer's state, or a writer's deposit, at the new names: excluded
    ihave %Hv := curAt_withPhys_agree γ p p' _ _ o o' $$ [Hc2 Hc]
    · iframe Hc2 Hc
    obtain ⟨rfl, rfl⟩ := Hv
    icases HP with (⟨HL, -⟩ | ⟨Hk, -, -⟩)
    · iunfold writerL at HL
      icases HL with ⟨%l, %n, HL⟩
      iNamedSuffix HL "2"
      simp only [StoreNames.withPhys_wv]
      ihave %Hv := ghostVar_valid_2 p.wv L' 1 l (1 : Qp).half $$ Hwv Hwv2
      exact absurd Hv.1 (Qp_one_add_not_le _)
    · iunfold writerKey at Hk
      simp only [StoreNames.withPhys_wk]
      ihave %Hv := ghostVar_valid_2 p.wk () 1 () 1 $$ Hwk Hk
      exact absurd Hv.1 (Qp_one_add_not_le _)
  -- the restoring state: the history's authority is at `L'`
  ihave %Hh := monoListAuthOwn_agree γ.idx.hist _ _ _ _ $$ Hh Hhist
  obtain ⟨-, rfl⟩ := Hh
  have hh := (monoListAuthOwn_fractional (GF := GF) γ.idx.hist (histOf L')).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hh
  ihave Hhist := hh.2 $$ [Hh Hhist]
  · iframe Hh Hhist
  icases ghostVar_halves p'.wv L' $$ Hwv with ⟨Hwv, HwvR⟩
  imod Hclose $$ [Hc Htoks Hhist Hlw Hrc Hclog Hwv Hcur Hlrd Hwk HwvR Hbv Hcres Hrr] with -
  · inext
    iunfold writerInvBody
    ileft
    iexists p', o'
    iframe Hc
    ileft
    isplitl [Htoks Hhist Hlw Hrc Hclog Hwv Hcur Hlrd]
    · iunfold writerL
      iexists L', ntok
      simp only [named]
      withPhys_simp
      simp only [StoreNames.withPhys_wv]
      iframe Htoks Hclog Hwv Hcur Hlrd
      iframe #
      isplitr
      · ipureintro; exact Hbudget
      isplitl [Hhist Hlw Hrc]
      · iunfold idxWriter
        simp only [StoreNames.withPhys_idx_hist, StoreNames.withPhys_idx_nev,
          StoreNames.withPhys_idx_log, idxLogAuth_withPhys, histShape_nil, List.length_nil,
          Nat.add_zero]
        iframe Hhist Hlw Hrc Hnv
        ipureintro; exact hwf
      ipureintro; exact hne
    · iunfold writerReg
      iright
      isplitl [Hrr]
      · simp only [StoreNames.withPhys_kb]; iexact Hrr
      iunfold writerRes
      iexists L'
      simp only [named, idxCert_withPhys]
      iframe Hbv Hcres
      iframe #
      isplitl [Hwk]
      · iunfold writerKey; simp only [StoreNames.withPhys_wk]; iexact Hwk
      isplitl [HwvR]
      · simp only [StoreNames.withPhys_wv]; iexact HwvR
      ipureintro; exact hne
  imodintro
  iframe Hwr Hcert

/-- The clean view of a bucket, in two halves (`restore`'s and the new batch lock's). -/
theorem kbViewC_halves (kb : Option KBReal) (γb : GName) (m : Bucket) :
    kbViewC (GF := GF) kb γb 1 m ⊢ kbViewC kb γb (1 : Qp).half m ∗ kbViewC kb γb (1 : Qp).half m := by
  cases kb with
  | none =>
    unfold kbViewC
    have h := (ghostMapAuth_fractional (GF := GF) γb m).fractional (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at h
    exact h.1
  | some d =>
    unfold kbViewC bkViewC backend.bViewC
    have hv := fun vd : backend.VData =>
      (ghostVar_fractional (GF := GF) d.γB.view vd).fractional (1 : Qp).half.half (1 : Qp).half.half
    have hc := (ghostVar_fractional (GF := GF) d.γB.cvw ()).fractional (1 : Qp).half.half
      (1 : Qp).half.half
    have hl := fun c : Bool =>
      (ghostVar_fractional (GF := GF) d.γB.cln c).fractional (1 : Qp).half.half (1 : Qp).half.half
    simp only [Qp.half_add_half] at hv hc hl
    iintro ⟨%vd, ⟨Hv, Hc, Hl⟩, %Hk⟩
    icases (hv vd).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
    icases (hl true).1 $$ Hl with ⟨Hl1, Hl2⟩
    isplitl [Hv1 Hc1 Hl1]
    · iexists vd; iframe Hv1 Hc1 Hl1; ipureintro; exact Hk
    · iexists vd; iframe Hv2 Hc2 Hl2; ipureintro; exact Hk

/-- **The view `restore` reads**, from a clean view of the restored log's bucket and the backend's
clean-view `ReadTx` (the empty bucket's, for `NewStore`'s log). -/
theorem restoreView_of (b : GoInterface) (γ : StoreNames) (RT : IProp GF) (q : Qp) (R : Log) :
    bucketViewC (GF := GF) γ q (bucketMap ([[], []] ++ R)) ∗
      keyCleanRead b (bucketViewC γ) RT (kbNoCmp γ.kb γ.bucket) ⊢
      restoreView b γ RT q R := by
  unfold restoreView restoreViewOut
  by_cases hR : R = []
  · subst hR
    simp only [↓reduceIte, List.append_nil, bucketMap_init]
    iintro ⟨H, -⟩
    isplitl [H]
    · iapply bucketViewC_bucketView $$ H
    · itrivial
  · simp only [hR, ↓reduceIte]
    iintro ⟨H, #Hc⟩
    iframe H Hc

/-- One of `nReaders` copies, and the rest. -/
theorem rep_take1 (P : IProp GF) :
    ([∗list] _x ∈ List.replicate nReaders (), P) ⊢
      P ∗ ([∗list] _x ∈ List.replicate (nReaders - 1) (), P) := by
  have hpos : 0 < nReaders := Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  rw [show nReaders = (nReaders - 1) + 1 by omega, List.replicate_succ, Nat.add_sub_cancel]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
  iframe H1 Hs

/-- A points-to, in two halves. -/
theorem typedPointsto_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (q : Qp) :
    typedPointsto (GF := GF) l v (DFrac.own q) ⊣⊢
      (l ↦{DFrac.own q.half} v ∗ l ↦{DFrac.own q.half} v) := by
  have h : (DFrac.own q : DFrac) = DFrac.own q.half • DFrac.own q.half := by
    rw [DFrac.op_own, Qp.half_add_half]
  rw [h]
  exact (typedPointsto_dfractional (GF := GF) l v).dfractional _ _

end moves

end mvcc

end EtcdGrove
end Perennial
