/-
Lemmas for the backend's constructor (`newBackend`, `newBatchTxBuffered`): the locks used
before their invariants exist. Lean-first (no Rocq counterpart); 2026-10-17, branch
`construct`.

`newBatchTxBuffered`'s first `Commit` locks and unlocks the batch transaction's `Mutex` and
`readTx.mu` before the backend's invariants exist (the batch lock's resource `batchFree` and
`readTx.mu`'s `rtRes` are about the transactions that commit begins). So:
- the `Mutex` (Perennial's spin lock on a boolean) is locked and unlocked while owned
  (`wp_Mutex_Lock_own`, `wp_Mutex_Unlock_own`), and its invariant allocated afterwards
  (`sync.init_Mutex`);
- `readTx.mu` is initialized at the protocol level (`rwmutex.init_RWMutex`), locked and unlocked
  through the protocol's own specs, and its guard (`isRWMutexGuard`, with `rtRes`) built
  afterwards (`init_RWMutex_guard`: the second half of Perennial's `sync.init_RWMutex`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BeginCtx
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section locks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

/-- `m.Lock()` on a `Mutex` owned whole and free (no invariant yet): it is locked. -/
theorem wp_Mutex_Lock_own (m : Loc) :
    {{ (m ↦ (false : Bool) : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); m ↦ (true : Bool) }} := by
  wp_start as Hm
  unfold lock.lock
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hm
  iintro Hm
  wp_pures
  iapply HΦ
  iexact Hm

/-- `m.Unlock()` on a `Mutex` owned whole and locked: it is free. -/
theorem wp_Mutex_Unlock_own (m : Loc) :
    {{ (m ↦ (true : Bool) : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); m ↦ (false : Bool) }} := by
  wp_start as Hm
  unfold lock.unlock
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m true true false _ _ rfl $$ Hm
  iintro Hm
  wp_auto
  iapply HΦ
  iexact Hm

/-- A `RWMutex` initialized at the protocol level (`rwmutex.init_RWMutex`, its state back at
unlocked) made a guard over `P` (fractional), its reader slots handed out: the second half of
Perennial's `sync.init_RWMutex`. -/
theorem init_RWMutex_guard (P : Qp → IProp GF) {E : CoPset} (rw : Loc)
    (γ : sync.rwmutex.RWMutexNames) :
    □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
      sync.rwmutex.isRWMutex rw γ (nroot.@"rw") ∗ sync.rwmutex.ownRWMutex γ (rwmutex.RLocked 0) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        sync.rwmutex.ownRLockToken γ) ∗ ▷ P 1 ⊢ |={E}=>
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        sync.ownRWMutex rw P := by
  iintro ⟨#HPf, #His, Hstate, Hrtoks, HP⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γmax, Hauth⟩
  imod ownTokAuth_add (Int.toNat sync.rwmutex.actualMaxReaders) γmax 0 $$ Hauth with ⟨Hauth, Htoks⟩
  simp only [Nat.zero_add]
  imod (update_into_persistently (P := ownTokAuthDfrac (GF := GF) γmax (DFrac.own 1) _)) $$ Hauth
    with #Hauth
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrlocked, Hrauth⟩
  imod ghostVar_alloc () with ⟨%γlocked, Hl⟩
  imod ownToks_0 (GF := GF) γmax with H0
  imod inv_alloc (nroot.@"inv") E
    iprop(∃ st, sync.rwmutex.ownRWMutex γ st ∗ sync.rwmutex_guard.invSt P γrlocked γmax γlocked st)
      $$ [Hstate Hrauth Hl H0 HP] with #Hinv
  · inext
    iexists (rwmutex.RLocked 0)
    iframe Hstate
    simp only [sync.rwmutex_guard.invSt]
    rw [sync.invFrac_0]
    iframe
  imodintro
  ihave #Hmk : (□ (sync.rwmutex.ownRLockToken γ -∗ ownToks γmax 1 -∗ sync.ownRWMutex rw P) :
      IProp GF) $$ []
  · imodintro
    iintro Hrtok Htok
    simp only [sync.ownRWMutex_unseal, sync.ownRWMutexDef]
    iexists γ, γmax, γrlocked, γlocked
    iframe Hrtok Htok
    iframe #
  iapply sync.replicate_helper $$ [$Hmk $Htoks $Hrtoks]

end locks

/-! ## `readTx.mu`'s resource is fractional

The guard of `readTx.mu` (`isRWMutexGuard`) holds that its resource `rtRes` is fractional
(`init_RWMutex_guard`'s premise). Every component of `rtRes` at `q` is fractional in `q` or
persistent, and two fractions agree on the existential witnesses (the ghost variables `γ.rd` and
`γ.rvs`, the history's authority, the read buffer's layout `rbAt_agree`, the buckets map's field).
-/

section frac
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem slice_frac {V : Type} [TypedPointsto (GF := GF) V] [ZeroVal V] (sl : GoSlice) (vs : List V)
    (q1 q2 : Qp) :
    (sl ↦*{DFrac.own (q1 + q2)} vs : IProp GF) ⊣⊢ sl ↦*{DFrac.own q1} vs ∗ sl ↦*{DFrac.own q2} vs := by
  rw [← DFrac.op_own]
  exact (ownSlice_dfractional sl vs).dfractional _ _

theorem cap_frac (V : Type) [TypedPointsto (GF := GF) V] [ZeroVal V] (sl : GoSlice) (q1 q2 : Qp) :
    ownSliceCap (GF := GF) V sl (DFrac.own (q1 + q2)) ⊣⊢
      ownSliceCap V sl (DFrac.own q1) ∗ ownSliceCap V sl (DFrac.own q2) := by
  rw [← DFrac.op_own]
  exact (ownSliceCap_dfractional sl).dfractional _ _

theorem bbAt_frac (bb : Loc) (p : BBPhys) (es : List Ent) (q1 q2 : Qp) :
    bbAt (GF := GF) bb (DFrac.own (q1 + q2)) p es ⊣⊢
      bbAt bb (DFrac.own q1) p es ∗ bbAt bb (DFrac.own q2) p es := by
  unfold bbAt
  constructor
  · iintro ⟨Hb, Hs, Hc, #Hro, #Hin⟩
    icases (typedPointsto_frac_add bb _ q1 q2).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases (slice_frac p.buf p.kvs q1 q2).1 $$ Hs with ⟨Hs1, Hs2⟩
    icases (cap_frac kv p.buf q1 q2).1 $$ Hc with ⟨Hc1, Hc2⟩
    iframe
    iframe #
  · iintro ⟨⟨Hb1, Hs1, Hc1, #Hro, #Hin⟩, ⟨Hb2, Hs2, Hc2, -, -⟩⟩
    ihave Hb := (typedPointsto_frac_add bb _ q1 q2).2 $$ [Hb1 Hb2]
    · iframe
    ihave Hs := (slice_frac p.buf p.kvs q1 q2).2 $$ [Hs1 Hs2]
    · iframe
    ihave Hc := (cap_frac kv p.buf q1 q2).2 $$ [Hc1 Hc2]
    · iframe
    iframe
    iframe #

theorem bbs_frac (Pb : BksPhys) (B : GMap w64 (List Ent)) (q1 q2 : Qp) :
    ([∗map] _id ↦ x;es ∈ Pb;B, bbAt (GF := GF) x.1 (DFrac.own (q1 + q2)) x.2 es) ⊣⊢
      ([∗map] _id ↦ x;es ∈ Pb;B, bbAt (GF := GF) x.1 (DFrac.own q1) x.2 es) ∗
      ([∗map] _id ↦ x;es ∈ Pb;B, bbAt (GF := GF) x.1 (DFrac.own q2) x.2 es) :=
  ⟨(BigSepM2.bigSepM2_mono fun _ _ => (bbAt_frac _ _ _ q1 q2).1).trans
      BigSepM2.bigSepM2_sep_eqv.1,
    BigSepM2.bigSepM2_sep_eqv.2.trans
      (BigSepM2.bigSepM2_mono fun _ _ => (bbAt_frac _ _ _ q1 q2).2)⟩

theorem bksAt_frac (m : GoMap) (Pb : BksPhys) (B : GMap w64 (List Ent)) (q1 q2 : Qp) :
    bksAt (GF := GF) m (DFrac.own (q1 + q2)) Pb B ⊣⊢
      bksAt m (DFrac.own q1) Pb B ∗ bksAt m (DFrac.own q2) Pb B := by
  unfold bksAt
  constructor
  · iintro ⟨Hm, Hb⟩
    icases ownMap_split (K := w64) (V := Loc) m q1 q2 _ $$ Hm with ⟨Hm1, Hm2⟩
    icases (bbs_frac Pb B q1 q2).1 $$ Hb with ⟨Hb1, Hb2⟩
    iframe
  · iintro ⟨⟨Hm1, Hb1⟩, ⟨Hm2, Hb2⟩⟩
    ihave Hm := ownMap_combine (K := w64) (V := Loc) m q1 q2 _ $$ [Hm1 Hm2]
    · iframe
    ihave Hb := (bbs_frac Pb B q1 q2).2 $$ [Hb1 Hb2]
    · iframe
    iframe

theorem rbAt_frac (txr : Loc) (m : GoMap) (Pb : BksPhys) (R : RBuf) (q1 q2 : Qp) :
    rbAt (GF := GF) txr (DFrac.own (q1 + q2)) m Pb R ⊣⊢
      rbAt txr (DFrac.own q1) m Pb R ∗ rbAt txr (DFrac.own q2) m Pb R := by
  unfold rbAt
  constructor
  · iintro ⟨Ht, Hv, Hb⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Ht with ⟨Ht1, Ht2⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases (bksAt_frac m Pb R.bks q1 q2).1 $$ Hb with ⟨Hb1, Hb2⟩
    iframe
  · iintro ⟨⟨Ht1, Hv1, Hb1⟩, ⟨Ht2, Hv2, Hb2⟩⟩
    ihave Ht := (typedPointsto_frac_add _ _ q1 q2).2 $$ [Ht1 Ht2]
    · iframe
    ihave Hv := (typedPointsto_frac_add _ _ q1 q2).2 $$ [Hv1 Hv2]
    · iframe
    ihave Hb := (bksAt_frac m Pb R.bks q1 q2).2 $$ [Hb1 Hb2]
    · iframe
    iframe

theorem rtIntv_frac (γ : BNames) (P : BParams) (rd : RdSt) (cm : GoMap) (D : Data) (q1 q2 : Qp) :
    rtIntv (GF := GF) γ P (q1 + q2) rd cm D ⊣⊢ rtIntv γ P q1 rd cm D ∗ rtIntv γ P q2 rd cm D := by
  unfold rtIntv wgOpen
  split
  · rw [Qp_half_add]
    constructor
    · iintro ⟨Hl, #Hs, #Hi, #Hw, Ho, Ht⟩
      icases ((txLive_fractional rd.rtx).fractional q1.half q2.half).1 $$ Hl with ⟨Hl1, Hl2⟩
      icases ghostVar_split rd.γw () q1 q2 $$ Ho with ⟨Ho1, Ho2⟩
      icases ghostVar_split rd.γt () q1 q2 $$ Ht with ⟨Ht1, Ht2⟩
      iframe
      iframe #
    · iintro ⟨⟨Hl1, #Hs, #Hi, #Hw, Ho1, Ht1⟩, ⟨Hl2, -, -, -, Ho2, Ht2⟩⟩
      ihave Hl := ((txLive_fractional rd.rtx).fractional q1.half q2.half).2 $$ [Hl1 Hl2]
      · iframe
      icombine Ho1 Ho2 as Ho
      icombine Ht1 Ht2 as Ht
      iframe
      iframe #
  · constructor
    · iintro ⟨%Hn, #Hs⟩
      iframe #
      ipureintro; exact ⟨Hn, Hn⟩
    · iintro ⟨⟨%Hn, #Hs⟩, -⟩
      iframe #
      ipureintro; exact Hn

theorem clnPart_frac (γ : BNames) (P : BParams) (rd : RdSt) (rv : RView) (q1 q2 : Qp) :
    clnPart (GF := GF) γ P (q1 + q2) rd rv ⊣⊢ clnPart γ P q1 rd rv ∗ clnPart γ P q2 rd rv := by
  unfold clnPart
  rw [Qp_half_add]
  constructor
  · iintro ⟨Hc, %Hp⟩
    icases ghostVar_split γ.cln _ q1.half q2.half $$ Hc with ⟨Hc1, Hc2⟩
    iframe
    isplitr <;> ipureintro <;> exact Hp
  · iintro ⟨⟨Hc1, %Hp⟩, ⟨Hc2, -⟩⟩
    icombine Hc1 Hc2 as Hc
    iframe
    ipureintro; exact Hp

/-- `rtResAt`'s body at fixed witnesses. -/
def rtW (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (H : GMap (w64 × Nat) RView) (m : GoMap) (Pb : BksPhys) (cm : GoMap) : IProp GF :=
  iprop(rbAt (rbufOf (baseOf rt)) (DFrac.own q) m Pb rv.2 ∗ ⌜bksOk Pb rv.2.bks⌝ ∗
    rbktOf (baseOf rt) ↦{DFrac.own q} cm ∗ rtRest γ P rt q rd rv cm H)

theorem rtW_frac (γ : BNames) (P : BParams) (rt : Loc) (rd : RdSt) (rv : RView)
    (H : GMap (w64 × Nat) RView) (m : GoMap) (Pb : BksPhys) (cm : GoMap) (q1 q2 : Qp) :
    rtW (GF := GF) γ P rt (q1 + q2) rd rv H m Pb cm ⊣⊢
      rtW γ P rt q1 rd rv H m Pb cm ∗ rtW γ P rt q2 rd rv H m Pb cm := by
  unfold rtW rtRest rtCore
  rw [Qp_half_add, Qp_half_add]
  constructor
  · iintro ⟨Hrb, %Hok, Hcm, Hv, Hrd, Hrvs, Hcur, Hcln, Hh, Hrtx, Hwg, %Hp, #Hha, #Hcv, #Hpo, #Hrdt,
      Hin⟩
    icases (rbAt_frac _ m Pb rv.2 q1 q2).1 $$ Hrb with ⟨Hrb1, Hrb2⟩
    icases (typedPointsto_frac_add _ cm q1 q2).1 $$ Hcm with ⟨Hcm1, Hcm2⟩
    icases ghostVar_split γ.view _ q1.half.half q2.half.half $$ Hv with ⟨Hv1, Hv2⟩
    icases ghostVar_split γ.rd rd q1 q2 $$ Hrd with ⟨Hrd1, Hrd2⟩
    icases ghostVar_split γ.rvs _ q1.half q2.half $$ Hrvs with ⟨Hrvs1, Hrvs2⟩
    icases ghostVar_split γ.cur _ q1.half q2.half $$ Hcur with ⟨Hcur1, Hcur2⟩
    icases (clnPart_frac γ P rd rv q1 q2).1 $$ Hcln with ⟨Hcln1, Hcln2⟩
    icases ((ghostMapAuth_fractional γ.hist H).fractional q1 q2).1 $$ Hh with ⟨Hh1, Hh2⟩
    icases (typedPointsto_frac_add _ rd.rtx q1 q2).1 $$ Hrtx with ⟨Hrtx1, Hrtx2⟩
    icases (typedPointsto_frac_add _ rd.wg q1 q2).1 $$ Hwg with ⟨Hwg1, Hwg2⟩
    icases (rtIntv_frac γ P rd cm rv.1 q1 q2).1 $$ Hin with ⟨Hin1, Hin2⟩
    isplitl [Hrb1 Hcm1 Hv1 Hrd1 Hrvs1 Hcur1 Hcln1 Hh1 Hrtx1 Hwg1 Hin1]
    · iframe
      iframe #
      ipureintro; exact ⟨Hok, Hp⟩
    · iframe
      iframe #
      ipureintro; exact ⟨Hok, Hp⟩
  · iintro ⟨⟨Hrb1, %Hok, Hcm1, Hv1, Hrd1, Hrvs1, Hcur1, Hcln1, Hh1, Hrtx1, Hwg1, %Hp, #Hha, #Hcv,
      #Hpo, #Hrdt, Hin1⟩, ⟨Hrb2, -, Hcm2, Hv2, Hrd2, Hrvs2, Hcur2, Hcln2, Hh2, Hrtx2, Hwg2, -, -, -,
      -, -, Hin2⟩⟩
    ihave Hrb := (rbAt_frac _ m Pb rv.2 q1 q2).2 $$ [Hrb1 Hrb2]
    · iframe
    ihave Hcm := (typedPointsto_frac_add _ cm q1 q2).2 $$ [Hcm1 Hcm2]
    · iframe
    icombine Hv1 Hv2 as Hv
    icombine Hrd1 Hrd2 as Hrd
    icombine Hrvs1 Hrvs2 as Hrvs
    icombine Hcur1 Hcur2 as Hcur
    ihave Hcln := (clnPart_frac γ P rd rv q1 q2).2 $$ [Hcln1 Hcln2]
    · iframe
    ihave Hh := ((ghostMapAuth_fractional γ.hist H).fractional q1 q2).2 $$ [Hh1 Hh2]
    · iframe
    ihave Hrtx := (typedPointsto_frac_add _ rd.rtx q1 q2).2 $$ [Hrtx1 Hrtx2]
    · iframe
    ihave Hwg := (typedPointsto_frac_add _ rd.wg q1 q2).2 $$ [Hwg1 Hwg2]
    · iframe
    ihave Hin := (rtIntv_frac γ P rd cm rv.1 q1 q2).2 $$ [Hin1 Hin2]
    · iframe
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hp⟩

/-- Two fractions of `rtResAt`'s body agree on the witnesses. -/
theorem rtW_agree (γ : BNames) (P : BParams) (rt : Loc) (q1 q2 : Qp) (rd rd' : RdSt)
    (rv rv' : RView) (H H' : GMap (w64 × Nat) RView) (m m' : GoMap) (Pb Pb' : BksPhys)
    (cm cm' : GoMap) :
    rtW (GF := GF) γ P rt q1 rd rv H m Pb cm ∗ rtW γ P rt q2 rd' rv' H' m' Pb' cm' ⊢
      ⌜rd = rd' ∧ rv = rv' ∧ H = H' ∧ m = m' ∧ Pb = Pb' ∧ cm = cm'⌝ := by
  unfold rtW rtRest rtCore
  iintro ⟨⟨Hrb1, -, Hcm1, -, Hrd1, Hrvs1, -, -, Hh1, -⟩, ⟨Hrb2, -, Hcm2, -, Hrd2, Hrvs2, -, -, Hh2,
    -⟩⟩
  icombine Hrd1 Hrd2 gives %hrd
  icombine Hrvs1 Hrvs2 gives %hrv
  ihave %hH := ghostMapAuth_agree γ.hist q1 q2 H H' $$ Hh1 Hh2
  icombine Hcm1 Hcm2 gives %hcm
  have hrv' : rv = rv' := (Prod.mk.inj hrv.2).1
  subst hrv'
  ihave %hb := rbAt_agree _ _ _ m m' Pb Pb' rv.2 $$ [Hrb1 Hrb2]
  · iframe
  ipureintro
  exact ⟨hrd.2, rfl, hH, hb.1, hb.2, hcm⟩

theorem rtRes_eq (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) :
    rtRes (GF := GF) γ P rt q =
      iprop(∃ (rd : RdSt) (rv : RView) (H : GMap (w64 × Nat) RView) (m : GoMap) (Pb : BksPhys)
        (cm : GoMap), rtW γ P rt q rd rv H m Pb cm) := rfl

/-- **`rtRes` is fractional** (what `readTx.mu`'s guard needs). -/
theorem rtRes_frac (γ : BNames) (P : BParams) (rt : Loc) :
    ⊢ □ (∀ q1 q2, rtRes (GF := GF) γ P rt (q1 + q2) ∗-∗ rtRes γ P rt q1 ∗ rtRes γ P rt q2) := by
  iintro !> %q1 %q2
  rw [rtRes_eq, rtRes_eq, rtRes_eq]
  isplit
  · iintro ⟨%rd, %rv, %H, %m, %Pb, %cm, Hw⟩
    icases (rtW_frac γ P rt rd rv H m Pb cm q1 q2).1 $$ Hw with ⟨Hw1, Hw2⟩
    isplitl [Hw1]
    · iexists rd, rv, H, m, Pb, cm
      iexact Hw1
    · iexists rd, rv, H, m, Pb, cm
      iexact Hw2
  · iintro ⟨⟨%rd, %rv, %H, %m, %Pb, %cm, Hw1⟩, ⟨%rd', %rv', %H', %m', %Pb', %cm', Hw2⟩⟩
    ihave %he := rtW_agree γ P rt q1 q2 rd rd' rv rv' H H' m m' Pb Pb' cm cm' $$ [Hw1 Hw2]
    · iframe
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
    iexists rd, rv, H, m, Pb, cm
    iapply (rtW_frac γ P rt rd rv H m Pb cm q1 q2).2
    iframe

end frac

end backend
end EtcdGrove
end Perennial
