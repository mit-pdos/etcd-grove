/-
**The store's lock and writer invariants with a slot** (the API proof's parallel internals, stage 1,
2026-11-03; `notes/mvcc-api-invariants.md` §1, §2, round 16; `notes/decisions.md`, "parallel
internals, today's untouched"). Lean-first (no Rocq counterpart).

Today's `s.revMu` body (`revMuBodyL`, `revMuBody`) and writer's state (`writerL`) hold every
fraction of the ghost state they tie together (the committed log's `γ.clog`, the bucket's view, the
revision counter), so the API's new ghost state (`Api/Ghost.lean`: the client's view `γ.abs`, the
pending revision `γ.pnd`, the compaction revision's authority `γ.crevLb`, the share token) can only
be tied to the committed log *inside* them. These are today's definitions with a **slot**:

* `revMuBodyLX s γ γp X q`: `revMuBodyL` ∗ `X q log c`, at the body's own log and compaction
  revision (`X` fractional in `q`);
* `writerLX s γ Y`: `writerL` ∗ `Y ilog`, at the writer's log;
* `writerInvBodyX s γ Y F Fr`: `writerInvBody` over `writerLX`, with a **frozen** state `F` (the
  whole backend share's holder deposits `F` and takes the writer's state, or the open writer's
  key, out: round 16's F2, for `mvccImage_snapshot.law`), and `Fr` deposited in the restoring state
  (so that the freezer and `store.Restore`, each holding the whole share, exclude each other);
* `revMuCurX`, `revMuInvX`, `writerInvX`, `isStoreX`, over them.

The lemmas over today's definitions are restated for any slot (their proofs today's, carrying the
slot). The API's instance (`isStoreA`) fills the slots with the API's ghost state: `X q L c` the
lock's quarter of the view and of the compaction authority (scaled by `q`), `Y L` the writer's
quarter of the view and its part of the pending revision at `none`, `F` and `Fr` the whole share
token. Today's modules are untouched; a proof over today's `isStore` does not apply to `isStoreA`
(the locks' invariants are fixed at their creation), so every proof that opens `s.revMu` or the
writer's invariant is redone over these (the hand-off, `notes/mvcc-api-invariants.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Ghost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## `s.revMu`'s resource with a slot -/

/-- **`s.revMu`'s resource, lagging, with a slot `X`** at the body's log and compaction revision
(`revMuBodyL` ∗ `X q log c`). -/
def revMuBodyLX (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    IProp GF :=
  iprop(∃ (log : Log) (ntok : Nat) (c cp : Int),
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "#Hnev" ∷ idxNevLb γp.idx log ∗
    "#Hok" ∷ certOk γ log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketViewL γp q.half log ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own q.half) ntok ∗
    "%Hbudget" ∷ ⌜log.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlog" ∷ idxLogAuth γ.idx (revQ γ q) log ∗
    "Hcmp" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 cp : w64) : IProp GF) ∗
    "Hcrev" ∷ crevUB γ.idx q.half.half c ∗
    "#Hperm" ∷ crevPermAt γ c ∗
    "Hlag" ∷ revLag γ q c cp ∗
    "%Hc" ∷ ⌜-1 ≤ c ∧ c < log.length⌝ ∗
    "HX" ∷ X q log c)

/-- **`s.revMu`'s resource, with a slot** (no lag: `revMuBody` ∗ `X q log c`). -/
def revMuBodyX (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    IProp GF :=
  iprop(∃ (log : Log) (ntok : Nat) (c : Int),
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "#Hnev" ∷ idxNevLb γp.idx log ∗
    "#Hok" ∷ certOk γ log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketViewL γp q.half log ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own q.half) ntok ∗
    "%Hbudget" ∷ ⌜log.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlog" ∷ idxLogAuth γ.idx (revQ γ q) log ∗
    "Hcmp" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 c : w64) : IProp GF) ∗
    "Hcrev" ∷ crevUB γ.idx q.half.half c ∗
    "#Hperm" ∷ crevPermAt γ c ∗
    "%Hc" ∷ ⌜-1 ≤ c ∧ c < log.length⌝ ∗
    "HX" ∷ X q log c)

/-- The lagging body is fractional when its slot is (two parts agree on the log, through the
committed-log ghost, and on the compaction revision, through its authority). -/
theorem revMuBodyLX_fractional (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF)
    (hX : ∀ log c, Fractional (fun q => X q log c)) :
    Fractional (revMuBodyLX (GF := GF) s γ γp X) where
  fractional q1 q2 := by
    have hcur : ∀ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"currentRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"currentRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hclog := fun (log : Log) =>
      (ghostVar_fractional (GF := GF) γ.clog log).fractional q1.half q2.half
    have hbv := fun (L : Log) => bucketViewL_split (GF := GF) γp q1.half q2.half L
    have htk : ∀ n : Nat, ownTokAuthDfrac (GF := GF) γ.revs (DFrac.own (q1.half + q2.half)) n ⊣⊢
        ownTokAuthDfrac γ.revs (DFrac.own q1.half) n ∗ ownTokAuthDfrac γ.revs (DFrac.own q2.half) n :=
      fun n => ownTokAuthDfrac_split (GF := GF) γ.revs (DFrac.own q1.half) (DFrac.own q2.half) n
    have hlg := fun (log : Log) =>
      (monoListAuthOwn_fractional (GF := GF) γ.idx.log log).fractional (revQ γ q1) (revQ γ q2)
    have hcmp : ∀ v : w64, (s.[store, go!"compactMainRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"compactMainRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"compactMainRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hcrev := fun (c : Int) => crevUB_split (GF := GF) γ.idx q1.half.half q2.half.half c
    have hlag := fun (c cp : Int) => revLag_split (GF := GF) γ q1 q2 c cp
    have hx := fun (log : Log) (c : Int) => (hX log c).fractional q1 q2
    unfold revMuBodyLX
    rw [revQ_add, Qp_half_add, Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro H
      icases H with ⟨%log, %ntok, %c, %cp, H⟩
      iNamed H
      icases (hcur _).1 $$ Hrev with ⟨Hr1, Hr2⟩
      icases (hclog log).1 $$ Hclog with ⟨Hc1, Hc2⟩
      icases (hbv _).1 $$ Hbucket with ⟨Hb1, Hb2⟩
      icases (htk ntok).1 $$ Htoks with ⟨Ht1, Ht2⟩
      icases (hlg log).1 $$ Hlog with ⟨Hl1, Hl2⟩
      icases (hcmp _).1 $$ Hcmp with ⟨Hm1, Hm2⟩
      icases (hcrev c).1 $$ Hcrev with ⟨Hv1, Hv2⟩
      icases (hlag c cp).1 $$ Hlag with ⟨Hg1, Hg2⟩
      icases (hx log c).1 $$ HX with ⟨Hx1, Hx2⟩
      isplitl [Hr1 Hc1 Hb1 Ht1 Hl1 Hm1 Hv1 Hg1 Hx1]
      · iexists log, ntok, c, cp; simp only [named]; iframe Hr1 Hc1 Hb1 Ht1 Hl1 Hm1 Hv1 Hg1 Hx1
        iframe #
        ipureintro
        exact ⟨Hne, Hbudget, Hc⟩
      · iexists log, ntok, c, cp; simp only [named]; iframe Hr2 Hc2 Hb2 Ht2 Hl2 Hm2 Hv2 Hg2 Hx2
        iframe #
        ipureintro
        exact ⟨Hne, Hbudget, Hc⟩
    · iintro ⟨H1, H2⟩
      icases H1 with ⟨%log, %ntok, %c, %cp, H1⟩
      icases H2 with ⟨%log2, %ntok2, %c2, %cp2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      ihave %Hlog := ghostVar_agree γ.clog _ _ _ _ $$ Hclog1 Hclog2
      subst Hlog
      icombine Htoks1 Htoks2 gives %Hn
      obtain ⟨-, Hn⟩ := Hn
      subst Hn
      ihave %Hcc := crevUB_agree γ.idx _ _ c c2 Hc1.1 Hc2.1 $$ Hcrev1 Hcrev2
      subst Hcc
      icombine Hcmp1 Hcmp2 gives %Hv
      have Hv : (W64 cp : w64) = W64 cp2 := by first | exact Hv.2 | exact Hv
      iunfold revLag at Hlag1 Hlag2
      icases Hlag1 with ⟨%Hp1, Hlag1⟩
      icases Hlag2 with ⟨%Hp2, Hlag2⟩
      have Hpp : cp = cp2 := by
        obtain ⟨-, Hc'⟩ := Hc1
        word
      subst Hpp
      iexists log, ntok, c, cp
      simp only [named]
      isplitl [Hrev1 Hrev2]
      · iapply (hcur _).2; iframe Hrev1 Hrev2
      isplitl [Hclog1 Hclog2]
      · iapply (hclog log).2; iframe Hclog1 Hclog2
      isplitr
      · iexact Hcert1
      isplitr
      · iexact Hnev1
      isplitr
      · iexact Hok1
      isplitr
      · ipureintro; exact Hne1
      isplitl [Hbucket1 Hbucket2]
      · iapply (hbv _).2; iframe Hbucket1 Hbucket2
      isplitl [Htoks1 Htoks2]
      · iapply (htk ntok).2; iframe Htoks1 Htoks2
      isplitl []
      · ipureintro; exact Hbudget1
      isplitl [Hlog1 Hlog2]
      · iapply (hlg log).2; iframe Hlog1 Hlog2
      isplitl [Hcmp1 Hcmp2]
      · iapply (hcmp _).2; iframe Hcmp1 Hcmp2
      isplitl [Hcrev1 Hcrev2]
      · iapply (hcrev c).2; iframe Hcrev1 Hcrev2
      isplitr
      · iexact Hperm1
      isplitl [Hlag1 Hlag2]
      · iapply (hlag c cp).2
        iunfold revLag
        isplitl [Hlag1]
        · iframe Hlag1; ipureintro; exact Hp1
        · iframe Hlag2; ipureintro; exact Hp1
      isplitl []
      · ipureintro; exact Hc1
      iapply (hx log c).2; iframe HX1 HX2

/-- The body without a lag is a lagging body. -/
theorem revMuBodyLX_of (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    revMuBodyX (GF := GF) s γ γp X q ⊢ revMuBodyLX s γ γp X q := by
  iintro H
  iunfold revMuBodyX at H
  icases H with ⟨%log, %ntok, %c, H⟩
  iNamed H
  iunfold revMuBodyLX
  iexists log, ntok, c, c
  simp only [named]
  iunfold revLag
  simp only [↓reduceIte]
  iframe Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX
  iframe #
  ipureintro; exact ⟨Hne, Hbudget, ⟨⟨Hc.1, Int.le_refl c⟩, trivial⟩, Hc⟩

/-- The lagging body is a body, or it lags with the lag's token. -/
theorem revMuBodyLX_noLag (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    revMuBodyLX (GF := GF) s γ γp X q ⊢ ghostVar γ.wsd q.half.half () ∨ revMuBodyX s γ γp X q := by
  iintro H
  iunfold revMuBodyLX at H
  icases H with ⟨%log, %ntok, %c, %cp, H⟩
  iNamed H
  iunfold revLag at Hlag
  icases Hlag with ⟨%Hp, Hlag⟩
  by_cases h : cp = c
  · subst h
    iright
    iunfold revMuBodyX
    iexists log, ntok, cp
    simp only [named]
    iframe Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX
    iframe #
    ipureintro; exact ⟨Hne, Hbudget, Hc⟩
  · simp only [h, ↓reduceIte]
    ileft
    iexact Hlag

/-- **A holder of `s.mu` finds no lag** (`revMuBodyL_mu`, with the slot). -/
theorem revMuBodyLX_mu (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q q' : Qp)
    (dq : DFrac) (cm : Int) (hcm : -1 ≤ cm) :
    revMuBodyLX (GF := GF) s γ γp X q ∗
      (s.[store, go!"compactMainRev"] ↦{dq} (W64 cm : w64) : IProp GF) ∗ crevUB γ.idx q' cm ⊢
      revMuBodyX s γ γp X q ∗
        (s.[store, go!"compactMainRev"] ↦{dq} (W64 cm : w64) : IProp GF) ∗ crevUB γ.idx q' cm := by
  iintro ⟨H, Hm, Hu⟩
  iunfold revMuBodyLX at H
  icases H with ⟨%log, %ntok, %c, %cp, H⟩
  iNamed H
  ihave %Hcc := crevUB_agree γ.idx _ _ c cm Hc.1 hcm $$ Hcrev Hu
  subst Hcc
  icombine Hcmp Hm gives %Hv
  have Hv : (W64 cp : w64) = W64 c := by first | exact Hv.2 | exact Hv
  iunfold revLag at Hlag
  icases Hlag with ⟨%Hp, Hlag⟩
  have Hpp : cp = c := by
    obtain ⟨-, Hc'⟩ := Hc
    word
  subst Hpp
  iframe Hm Hu
  iunfold revMuBodyX
  iexists log, ntok, cp
  simp only [named]
  iframe Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX
  iframe #
  ipureintro; exact ⟨Hne, Hbudget, Hc⟩

/-- **A holder of the watchable store's lock finds no lag** (`revMuBodyL_wsd`, with the slot). -/
theorem revMuBodyLX_wsd (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    revMuBodyLX (GF := GF) s γ γp X q ∗ ghostVar γ.wsd 1 () ⊢
      revMuBodyX s γ γp X q ∗ ghostVar γ.wsd 1 () := by
  iintro ⟨H, Hw⟩
  icases revMuBodyLX_noLag s γ γp X q $$ H with (Hl | H)
  · ihave %Hv := ghostVar_valid_2 γ.wsd () 1 () q.half.half $$ Hw Hl
    exact absurd Hv.1 (Qp_one_add_not_le _)
  · iframe H Hw

/-- **`s.revMu`'s resource at the current physical names, with a slot** (`revMuCur`). -/
def revMuCurX (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ (p : PhysNames) (o : StoreObjs), curAt (γ.withPhys p) (DFrac.own q.half.half.half) o ∗
    revMuBodyLX s γ (γ.withPhys p) X q)

theorem revMuCurX_fractional (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF)
    (hX : ∀ log c, Fractional (fun q => X q log c)) :
    Fractional (revMuCurX (GF := GF) s γ X) where
  fractional q1 q2 := by
    have hb := fun p => (revMuBodyLX_fractional (GF := GF) s γ (γ.withPhys p) X hX).fractional q1 q2
    unfold revMuCurX
    rw [Qp_half_add, Qp_half_add, Qp_half_add]
    constructor
    · iintro ⟨%p, %o, Hc, H⟩
      icases (curAt_fractional (GF := GF) (γ.withPhys p) o).fractional _ _ |>.1 $$ Hc with ⟨Hc1, Hc2⟩
      icases (hb p).1 $$ H with ⟨H1, H2⟩
      isplitl [Hc1 H1]
      · iexists p, o; iframe Hc1 H1
      · iexists p, o; iframe Hc2 H2
    · iintro ⟨⟨%p1, %o1, Hc1, H1⟩, ⟨%p2, %o2, Hc2, H2⟩⟩
      ihave %Hv := curAt_withPhys_agree γ p1 p2 _ _ o1 o2 $$ [Hc1 Hc2]
      · iframe Hc1 Hc2
      obtain ⟨rfl, rfl⟩ := Hv
      iexists p1, o1
      isplitl [Hc1 Hc2]
      · iapply (curAt_fractional (GF := GF) (γ.withPhys p1) o1).fractional _ _ |>.2; iframe Hc1 Hc2
      iapply (hb p1).2
      iframe H1 H2

/-- **`s.revMu`'s resource, with a slot** (`revMuInv`): restoring, the counters' parts only
(`revMuRest`: the slot's part is the restorer's). -/
def revMuInvX (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ m : Bool, dghostVar γ.rst (DFrac.own q.half) m ∗
    (if m then revMuRest s q else revMuCurX s γ X q))

theorem revMuInvX_fractional (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF)
    (hX : ∀ log c, Fractional (fun q => X q log c)) :
    Fractional (revMuInvX (GF := GF) s γ X) where
  fractional q1 q2 := by
    have hb := (revMuCurX_fractional (GF := GF) s γ X hX).fractional q1 q2
    have hr := (revMuRest_fractional (GF := GF) s).fractional q1 q2
    unfold revMuInvX
    rw [Qp_half_add]
    constructor
    · iintro ⟨%m, Hf, H⟩
      icases (dghostVar_fractional (GF := GF) γ.rst m).fractional q1.half q2.half |>.1 $$ Hf
        with ⟨Hf1, Hf2⟩
      cases m
      · simp only [Bool.false_eq_true, ↓reduceIte] at *
        icases hb.1 $$ H with ⟨H1, H2⟩
        isplitl [Hf1 H1]
        · iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe Hf1 H1
        · iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe Hf2 H2
      · simp only [↓reduceIte] at *
        icases hr.1 $$ H with ⟨H1, H2⟩
        isplitl [Hf1 H1]
        · iexists true; simp only [↓reduceIte]; iframe Hf1 H1
        · iexists true; simp only [↓reduceIte]; iframe Hf2 H2
    · iintro ⟨⟨%m1, Hf1, H1⟩, ⟨%m2, Hf2, H2⟩⟩
      icombine Hf1 Hf2 gives %Hm
      obtain ⟨-, rfl⟩ := Hm
      iexists m1
      isplitl [Hf1 Hf2]
      · iapply (dghostVar_fractional (GF := GF) γ.rst m1).fractional q1.half q2.half |>.2
        iframe Hf1 Hf2
      cases m1
      · simp only [Bool.false_eq_true, ↓reduceIte] at *
        iapply hb.2; iframe H1 H2
      · simp only [↓reduceIte] at *
        iapply hr.2; iframe H1 H2

/-- **`s.revMu`'s resource, not restoring** (`revMuInv_open`, with a slot). -/
theorem revMuInvX_open (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp)
    (dq : DFrac) :
    revMuInvX (GF := GF) s γ X q ∗ dghostVar γ.rst dq false ⊢
      (∃ γp : StoreNames, revMuBodyLX s γ γp X q ∗ revMuTok γ γp q) ∗ dghostVar γ.rst dq false := by
  unfold revMuInvX
  iintro ⟨⟨%m, Hf, H⟩, Hr⟩
  icombine Hf Hr gives %Hm
  obtain ⟨-, rfl⟩ := Hm
  simp only [Bool.false_eq_true, ↓reduceIte]
  iunfold revMuCurX at H
  icases H with ⟨%p, %o, Hc, H⟩
  iframe Hr
  iexists (γ.withPhys p)
  iframe H
  iunfold revMuTok
  iframe Hf
  isplitl
  · iexists o; iexact Hc
  ipureintro; rfl

/-- **`s.revMu`'s resource, not restoring, at the current names** (`revMuInv_open_pin`, with a
slot). -/
theorem revMuInvX_open_pin (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF)
    (p : PhysNames) (q : Qp) (dq dq' : DFrac) (o : StoreObjs) :
    revMuInvX (GF := GF) s γ X q ∗ dghostVar γ.rst dq false ∗ curAt (γ.withPhys p) dq' o ⊢
      revMuBodyLX s γ (γ.withPhys p) X q ∗ revMuTok γ (γ.withPhys p) q ∗ dghostVar γ.rst dq false ∗
        curAt (γ.withPhys p) dq' o := by
  unfold revMuInvX
  iintro ⟨⟨%m, Hf, H⟩, Hr, Hpin⟩
  icombine Hf Hr gives %Hm
  obtain ⟨-, rfl⟩ := Hm
  simp only [Bool.false_eq_true, ↓reduceIte]
  iunfold revMuCurX at H
  icases H with ⟨%p', %o', Hc, H⟩
  ihave %Hv := curAt_withPhys_agree γ p' p _ _ o' o $$ [Hc Hpin]
  · iframe Hc Hpin
  obtain ⟨rfl, rfl⟩ := Hv
  iframe H Hr Hpin
  iunfold revMuTok
  iframe Hf
  isplitl
  · iexists o'; iexact Hc
  ipureintro; rfl

/-- `revMuInvX_open_pin` at the current names themselves. -/
theorem revMuInvX_open_cur (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp)
    (dq dq' : DFrac) (o : StoreObjs) :
    revMuInvX (GF := GF) s γ X q ∗ dghostVar γ.rst dq false ∗ curAt γ dq' o ⊢
      revMuBodyLX s γ γ X q ∗ revMuTok γ γ q ∗ dghostVar γ.rst dq false ∗ curAt γ dq' o :=
  revMuInvX_open_pin s γ X γ.phys q dq dq' o

/-- `s.revMu`'s resource closed, with a lag (`revMuInv_closeL`, with a slot). -/
theorem revMuInvX_closeL (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    revMuBodyLX (GF := GF) s γ γp X q ∗ revMuTok γ γp q ⊢ revMuInvX s γ X q := by
  unfold revMuInvX revMuTok
  iintro ⟨H, Hf, ⟨%o, Hc⟩, %Hp⟩
  iexists false
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe Hf
  iunfold revMuCurX
  iexists γp.phys, o
  rw [← Hp]
  iframe H Hc

theorem revMuInvX_close (s : Loc) (γ γp : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    revMuBodyX (GF := GF) s γ γp X q ∗ revMuTok γ γp q ⊢ revMuInvX s γ X q := by
  iintro ⟨H, Ht⟩
  iapply revMuInvX_closeL s γ γp X q
  iframe Ht
  iapply revMuBodyLX_of s γ γp X q $$ H

/-- **A transaction holding `s.mu` finds `s.revMu`'s resource not restoring** (`revMuInv_open_held`,
with a slot). -/
theorem revMuInvX_open_held (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF) (q : Qp)
    (c : Int) (ti : Loc) :
    revMuInvX (GF := GF) s γ X q ∗ muHeld s γ c ti ⊢
      revMuBodyX s γ γ X q ∗ revMuTok γ γ q ∗ muHeld s γ c ti := by
  iintro ⟨H, Hm⟩
  iunfold muHeld at Hm
  icases Hm with ⟨Hl, Ha, %o, %Ho, Hf⟩
  iunfold fieldShareAt at Hf
  iNamed Hf
  icases revMuInvX_open_cur s γ X q _ _ o $$ [H Hfrst Hcur] with ⟨H, Htk, Hfrst, Hcur⟩
  · iframe H Hfrst Hcur
  iunfold muInvAt at Ha
  iNamed Ha
  icases revMuBodyLX_mu s γ γ X q _ _ c HcM $$ [$H $HcmpM $HcrevM] with ⟨H, HcmpM, HcrevM⟩
  iframe H Htk
  iunfold muHeld
  iframe Hl
  isplitl [HcmpM HcrevM]
  · iunfold muInvAt; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
  iexists o
  isplitl []
  · ipureintro; exact Ho
  iunfold fieldShareAt
  iframe Hcur Hflds Hfrst Hph

/-- **`s.revMu`'s resource, not restoring, at a share's names** (`revMuInv_open_share`, with a
slot). -/
theorem revMuInvX_open_share (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF)
    (p : PhysNames) (q q' : Qp) (o : StoreObjs) :
    revMuInvX (GF := GF) s γ X q ∗ fieldShareAt s (γ.withPhys p) q' o ∗ ghostVar γ.wsd 1 () ⊢
      revMuBodyX s γ (γ.withPhys p) X q ∗ revMuTok γ (γ.withPhys p) q ∗
        fieldShareAt s (γ.withPhys p) q' o ∗ ghostVar γ.wsd 1 () := by
  iintro ⟨H, Hf, Hw⟩
  iunfold fieldShareAt at Hf
  iNamed Hf
  ihave Hfrst : dghostVar (GF := GF) γ.rst (DFrac.own q'.half) false $$ [Hfrst]
  · withPhys_simp; iexact Hfrst
  icases revMuInvX_open_pin s γ X p q _ _ o $$ [H Hfrst Hcur] with ⟨H, Htk, Hfrst, Hcur⟩
  · iframe H Hfrst Hcur
  icases revMuBodyLX_wsd s γ (γ.withPhys p) X q $$ [$H $Hw] with ⟨H, Hw⟩
  iframe H Htk Hw
  iunfold fieldShareAt
  simp only [named]
  withPhys_simp
  iframe Hcur Hflds Hfrst Hph

/-! ## The writer's state and invariant with a slot, and the frozen state -/

/-- **The writer's state, with a slot** `Y` at its log (`writerL` ∗ `Y ilog`). -/
def writerLX (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) : IProp GF :=
  iprop(∃ (ilog : Log) (ntok : Nat),
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hw" ∷ idxWriter γ.idx ilog [] ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hwv" ∷ ghostVar γ.wv (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "HY" ∷ Y ilog)

/-- **The writer's invariant's body, with a slot, a frozen state and a restore deposit**
(`writerInvBody`): at the current objects and names, the frozen flag `fz` whole and down with the
state in (with its registration) or out (the writer's key deposited, with its part of `s.mu`'s
deposit ghost); or **frozen**: the flag half up (the freezer holds the other half) and `F`
deposited (the whole backend share's holder has taken what was there, the state or the key, out:
`writerTaken`); or, while `store.Restore` restores, its deposit ghost, half the index's history's
authority, `Fr` (the restorer's deposit) and the flag whole and down. -/
def writerInvBodyX (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) :
    IProp GF :=
  iprop((∃ (p : PhysNames) (o : StoreObjs),
    curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
    ((ghostVar fz 1 false ∗
        (writerLX s (γ.withPhys p) Y ∗ writerReg s (γ.withPhys p) ∨
          writerKey (γ.withPhys p) ∗ wDep γ ∗ storeRegd s (γ.withPhys p))) ∨
      ghostVar fz (1 : Qp).half true ∗ F)) ∨
    ghostVar γ.wr 1 () ∗ (∃ h : List HistItem, monoListAuthOwn γ.idx.hist (1 : Qp).half h) ∗ Fr ∗
      ghostVar fz 1 false)

/-- The writer's invariant, with a slot (`writerInv`). -/
def writerInvX (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) :
    IProp GF :=
  inv writerN (writerInvBodyX s γ Y F Fr fz)

instance writerInvX_persistent (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr : IProp GF)
    (fz : GName) : Persistent (writerInvX (GF := GF) s γ Y F Fr fz) := by
  unfold writerInvX; infer_instance

/-- **What the frozen state's holder took out**: the writer's state with its registration, or (a
write transaction open) the writer's key with its part of the deposit ghost and the registration. -/
def writerTaken (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) : IProp GF :=
  iprop(writerLX s γ Y ∗ writerReg s γ ∨ writerKey γ ∗ wDep γ ∗ storeRegd s γ)


/-! ## The store, with slots -/

/-- **A store, with slots** (`isStore`, over `revMuInvX` and `writerInvX`). -/
def isStoreX (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF) (Y : Log → IProp GF)
    (F Fr : IProp GF) (fz : GName) : IProp GF :=
  iprop(∃ (le : GoInterface) (lg : Loc) (scfg : StoreConfig) (shs : Loc),
    "#Hle" ∷ s.[store, go!"le"] ↦□ le ∗
    "#Hlessor" ∷ isLessor le γ.leases ∗
    "#Hlg" ∷ s.[store, go!"lg"] ↦□ lg ∗
    "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
    "#Hmu" ∷ sync.isRWMutexGuard (muAddr s) (muInv s γ) ∗
    "#HrevMu" ∷ sync.isRWMutexGuard (revMuAddr s) (revMuInvX s γ X) ∗
    "#Hcfg" ∷ s.[store, go!"cfg"] ↦□ scfg ∗
    "%Hcfgl" ∷ ⌜0 < sint.Z scfg.CompactionBatchLimit' ∧ sint.Z scfg.CompactionBatchLimit' ≤ rangeLimitMax⌝ ∗
    "#Hhashes" ∷ s.[store, go!"hashes"] ↦□
      (interface.mkOk (go.GoType.PointerType hashStorage.ty) #shs : GoInterface) ∗
    "#HhsOk" ∷ mvcc.hashStorageOk shs ∗
    "#Hwi" ∷ writerInvX s γ Y F Fr fz ∗
    "#Hpool" ∷ readerPool γ ∗
    "#Hc0" ∷ idxCert γ.idx [[], []] ∗
    "%Hrb" ∷ ⌜receiptBound GF ≤ 2 ^ 48⌝)

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 800000 in
instance isStoreX_persistent (s : Loc) (γ : StoreNames) (X : Qp → Log → Int → IProp GF)
    (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) :
    Persistent (isStoreX (GF := GF) s γ X Y F Fr fz) := by
  unfold isStoreX; infer_instance

/-- **A store reads only its logical names**. -/
theorem isStoreX_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) (X : Qp → Log → Int → IProp GF)
    (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) :
    isStoreX (GF := GF) s (γ.withPhys p) X Y F Fr fz = isStoreX s γ X Y F Fr fz := rfl

theorem revMuInvX_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) (X : Qp → Log → Int → IProp GF) :
    revMuInvX (GF := GF) s (γ.withPhys p) X = revMuInvX s γ X := rfl

theorem writerInvX_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) (Y : Log → IProp GF)
    (F Fr : IProp GF) (fz : GName) :
    writerInvX (GF := GF) s (γ.withPhys p) Y F Fr fz = writerInvX s γ Y F Fr fz := rfl

end reprs

section lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A writer checks the writer's state out** (`writerInv_checkout`, with a slot), holding `G`,
which excludes the frozen state's deposit (`F ∗ G ⊢ False`: the API's writer holds a share of the
backend share token, the frozen state's holder all of it). -/
theorem writerInvX_checkout (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr G : IProp GF)
    (fz : GName) (hFG : F ∗ G ⊢ False) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInvX (GF := GF) s γ Y F Fr fz -∗ G -∗ curAt γ dq o -∗ storeW s γ -∗ wDep γ ={⊤}=∗
      writerLX s γ Y ∗ storeRegd s γ ∗ G ∗
      (∃ L : Log, ghostVar γ.wv (1 : Qp).half L ∗ bucketViewL γ (1 : Qp).half.half L ∗
        idxCert γ.idx L ∗ ⌜L ≠ []⌝ ∗ compactRes γ) ∗ curAt γ dq o := by
  iintro Hlc #Hi HG Hpin HW Hd
  iunfold writerInvX at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)) $$ Hlc HP with HP
  iunfold writerInvBodyX at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨Hwr1, -⟩)
  rotate_left 1
  · iunfold wDep at Hd
    ihave %Hv := ghostVar_valid_2 γ.wr () 1 () _ $$ Hwr1 Hd
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz, (⟨HL, Hrg⟩ | ⟨Hk', -, #Hreg'⟩)⟩ | ⟨-, HF⟩)
  · imod writerReg_get s γ _ (by solve_ndisj) $$ [$HW $Hrg] with ⟨HWr, #Hreg⟩
    iunfold writerRes at HWr
    icases HWr with ⟨%L, Hwk, Hwv, Hbv, #Hcert, %Hne, Hcres⟩
    imod Hclose $$ [Hc Hwk Hd Hfz] with -
    · inext; iunfold writerInvBodyX; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; ileft; iframe Hfz; iright; iframe Hwk Hd Hreg
    imodintro
    iframe HL Hreg Hpin HG
    iexists L
    iframe Hwv Hbv Hcert Hcres
    ipureintro; exact Hne
  · ihave HWr := storeW_get s γ $$ [$Hreg' $HW]
    iunfold writerRes at HWr
    icases HWr with ⟨%L, Hk, -⟩
    iunfold writerKey at Hk Hk'
    ihave %Hv := ghostVar_valid_2 γ.wk () 1 () 1 $$ Hk Hk'
    exact absurd Hv.1 (Qp_one_add_not_le 1)
  · iexfalso
    iapply hFG
    iframe HF HG

/-- **A writer checks the writer's state back in** (`writerInv_checkin`, with a slot): the frozen
state is excluded as at the checkout (`G`). -/
theorem writerInvX_checkin (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr G : IProp GF)
    (fz : GName) (hFG : F ∗ G ⊢ False) (L : Log) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInvX (GF := GF) s γ Y F Fr fz -∗ G -∗ curAt γ dq o -∗ writerLX s γ Y -∗
      ghostVar γ.wv (1 : Qp).half L ={⊤}=∗
      writerKey γ ∗ wDep γ ∗ G ∗ ghostVar γ.wv (1 : Qp).half L ∗ curAt γ dq o := by
  iintro Hlc #Hi HG Hpin HL Hv
  iunfold writerInvX at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)) $$ Hlc HP with HP
  iunfold writerInvBodyX at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨-, ⟨%h, Hh1⟩, -⟩)
  rotate_left 1
  · iunfold writerLX at HL
    icases HL with ⟨%l1, %n1, HL⟩
    iNamed HL
    iunfold idxWriter at Hw
    icases Hw with ⟨Hh2, -⟩
    ihave %Hv := monoListAuthOwn_agree γ.idx.hist 1 (1 : Qp).half _ _ $$ Hh2 Hh1
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hvv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hvv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz, (⟨HL', -⟩ | ⟨Hk, Hd, #Hreg⟩)⟩ | ⟨-, HF⟩)
  · iunfold writerLX at HL HL'
    icases HL with ⟨%l1, %n1, HL⟩
    icases HL' with ⟨%l2, %n2, HL'⟩
    iNamedSuffix HL "1"
    iNamedSuffix HL' "2"
    icases ghostVar_join_halves γ.wv l1 l2 $$ [Hwv1 Hwv2] with ⟨Hwv12, -⟩
    · iframe Hwv1 Hwv2
    ihave %Hv3 := ghostVar_valid_2 γ.wv l1 1 L (1 : Qp).half $$ Hwv12 Hv
    exact absurd Hv3.1 (Qp_one_add_not_le _)
  · imod writerReg_alloc s γ _ $$ Hreg with #Hrg
    imod Hclose $$ [Hc HL Hfz] with -
    · inext; iunfold writerInvBodyX; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; ileft; iframe Hfz; ileft; iframe HL Hrg
    imodintro; iframe Hk Hd Hv Hpin HG
  · iexfalso
    iapply hFG
    iframe HF HG

/-- **Freezing the writer** (round 16, F2): the holder of `F` (the API's whole backend share token)
deposits it, raises the frozen flag (keeping half of it) and takes out what is there, the writer's
state or the open writer's key (`writerTaken`), at the current names; not while restoring, nor
frozen already (`Fr ∗ F ⊢ False`, `F ∗ F ⊢ False`: the restorer's deposit and the frozen state's
are the whole share too). -/
theorem writerInvX_freeze (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr : IProp GF)
    (fz : GName) (hFr : Fr ∗ F ⊢ False) (hFF : F ∗ F ⊢ False) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInvX (GF := GF) s γ Y F Fr fz -∗ F -∗ curAt γ dq o ={⊤}=∗
      writerTaken s γ Y ∗ ghostVar fz (1 : Qp).half true ∗ curAt γ dq o := by
  iintro Hlc #Hi HF Hpin
  iunfold writerInvX at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)) $$ Hlc HP with HP
  iunfold writerInvBodyX at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨-, -, HFr, -⟩)
  rotate_left 1
  · iexfalso
    iapply hFr
    iframe HFr HF
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz, HT⟩ | ⟨-, HF'⟩)
  · imod ghostVar_update true fz false $$ Hfz with Hfz
    icases (ghostVar_split_half (GF := GF) fz 1 true).1 $$ Hfz with ⟨Hfz1, Hfz2⟩
    imod Hclose $$ [Hc HF Hfz1] with -
    · inext; iunfold writerInvBodyX; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright; iframe Hfz1 HF
    imodintro; iframe Hpin Hfz2; iunfold writerTaken; iexact HT
  · iexfalso
    iapply hFF
    iframe HF HF'

/-- **Thawing the writer**: the frozen state's holder (its half of the flag up) puts back what it
took, lowers the flag and gets `F` back. -/
theorem writerInvX_thaw (s : Loc) (γ : StoreNames) (Y : Log → IProp GF) (F Fr : IProp GF)
    (fz : GName) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInvX (GF := GF) s γ Y F Fr fz -∗ writerTaken s γ Y -∗
      ghostVar fz (1 : Qp).half true -∗ curAt γ dq o ={⊤}=∗ F ∗ curAt γ dq o := by
  iintro Hlc #Hi HT Hfz Hpin
  iunfold writerInvX at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBodyX (GF := GF) s γ Y F Fr fz)) $$ Hlc HP with HP
  iunfold writerInvBodyX at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨-, -, -, Hfz'⟩)
  rotate_left 1
  · ihave %Hv := ghostVar_valid_2 fz false 1 true (1 : Qp).half $$ Hfz' Hfz
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz', -⟩ | ⟨Hfz', HF⟩)
  · ihave %Hv := ghostVar_valid_2 fz false 1 true (1 : Qp).half $$ Hfz' Hfz
    exact absurd Hv.1 (Qp_one_add_not_le _)
  icases ghostVar_join_halves fz true true $$ [Hfz' Hfz] with ⟨Hfz, -⟩
  · iframe Hfz' Hfz
  imod ghostVar_update false fz true $$ Hfz with Hfz
  imod Hclose $$ [Hc HT Hfz] with -
  · inext; iunfold writerInvBodyX; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
    iframe Hc; ileft; iframe Hfz; iunfold writerTaken at HT; iexact HT
  imodintro; iframe HF Hpin

end lc

/-! ## The API's instance -/

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.revMu`'s part of the API's ghost state** at fraction `q` (§1): a quarter of `q` of the
view at the lock's log and compaction revision, and of the compaction revision's authority. -/
def revMuAbs (a : AbsNames) (q : Qp) (L : Log) (c : Int) : IProp GF :=
  iprop(absPart a q.half.half L c ∗ crevAuth a q.half.half c)

instance revMuAbs_fractional (a : AbsNames) (L : Log) (c : Int) :
    Fractional (fun q => revMuAbs (GF := GF) a q L c) where
  fractional q1 q2 := by
    have ha := (absPart_fractional (GF := GF) a L c).fractional q1.half.half q2.half.half
    have hc := (crevAuth_fractional (GF := GF) a c).fractional q1.half.half q2.half.half
    unfold revMuAbs
    rw [Qp_half_add, Qp_half_add]
    constructor
    · iintro ⟨Ha, Hc⟩
      icases ha.1 $$ Ha with ⟨Ha1, Ha2⟩
      icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [Ha1 Hc1]
      · iframe Ha1 Hc1
      · iframe Ha2 Hc2
    · iintro ⟨⟨Ha1, Hc1⟩, ⟨Ha2, Hc2⟩⟩
      isplitl [Ha1 Ha2]
      · iapply ha.2; iframe Ha1 Ha2
      · iapply hc.2; iframe Hc1 Hc2

/-- The writer's part of the pending revision (§1): a quarter for a watchable store (another
quarter is `watchStoreBody`'s), half for a plain one. -/
def pndW (γ : StoreNames) : Qp := if γ.watchQ then (1 : Qp).half.half else (1 : Qp).half

/-- **The writer's part of the API's ghost state** at its log (§1): a quarter of the view, at some
compaction revision, and its part of the pending revision, at `none` (while checked in). -/
def writerAbs (a : AbsNames) (pw : Qp) (L : Log) : IProp GF :=
  iprop(∃ c : Int, absPart a (1 : Qp).half.half L c ∗ pndPart a pw none)

/-- **A store, with the API's ghost state** (`notes/mvcc-api-invariants.md` §1, §2): today's store
with the lock's and the writer's parts of the view, the compaction authority and the pending
revision in their slots, the whole backend share token as the frozen and the restoring deposits,
and the frozen flag `a.frz`. -/
def isStoreA (s : Loc) (γ : StoreNames) (a : AbsNames) : IProp GF :=
  isStoreX s γ (revMuAbs a) (writerAbs a (pndW γ)) (shareTok a 1) (shareTok a 1) a.frz

instance isStoreA_persistent (s : Loc) (γ : StoreNames) (a : AbsNames) :
    Persistent (isStoreA (GF := GF) s γ a) := by
  unfold isStoreA; infer_instance

theorem pndW_withPhys (γ : StoreNames) (p : PhysNames) : pndW (γ.withPhys p) = pndW γ := rfl

theorem isStoreA_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) (a : AbsNames) :
    isStoreA (GF := GF) s (γ.withPhys p) a = isStoreA s γ a := rfl

/-- `s.revMu`'s resource with the API's part is fractional (for `sync.init_RWMutex`). -/
instance revMuInvA_fractional (s : Loc) (γ : StoreNames) (a : AbsNames) :
    Fractional (revMuInvX (GF := GF) s γ (revMuAbs a)) :=
  revMuInvX_fractional s γ (revMuAbs a) (fun L c => revMuAbs_fractional a L c)

/-- The API's exclusions for the writer's frozen and restoring states: a share of the token
excludes the whole share. -/
theorem shareTok_excl' (a : AbsNames) (q : Qp) :
    shareTok (GF := GF) a 1 ∗ shareTok a q ⊢ False := shareTok_excl a q

end inst

end api
end mvcc
end EtcdGrove
end Perennial
