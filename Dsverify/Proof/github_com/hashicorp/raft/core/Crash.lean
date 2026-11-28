/-
(hraft_robust L0, R1 §1.3–§3; stage R2 proves it) **The crash laws of one server**: opening its crash
invariant `srvDurInv` (with the generation's crash token), the views' agreement and update, arming a
generation (`raft_arm`, at boot, before the generation's WP) and the crash (`raft_crash`: the next
generation's vacant state from the dead one's, firing its pending steps).

The definitions (`SrvDur`, `durBody`, `srvDurInv`, the views `srvV`/`srvVP`/`stV`/`termV`/`cidxV`,
`Pend`/`winRes`) are in `core/Defs.lean`. Statements marked "(R2)" are proved by stage R2; their exact
form may be refined there (with the lead's OK, `/shared/tmp/ps2/hraft/robust/HANDOFF.md`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

variable (γ : GNames) (rc : RCtx GF) (i : SID)

/-! ## Opening the crash invariant -/

/-- **Opening `srvDurInv`** with the generation's crash token (`inv_nc_acc`): the crash state's
body, and the closing update. The generic accessor; the laws below are its uses. -/
theorem durAcc {E : CoPset} (hE : ↑durN ⊆ E) :
    srvDurInvRaw γ rc i ⊢ |NC={E, E \ ↑durN}=> ▷ (∃ X : SrvDur, durBody γ rc i X) ∗
      (▷ (∃ X : SrvDur, durBody γ rc i X) ={E \ ↑durN, E}=∗ True) := by
  unfold srvDurInvRaw
  exact inv_nc_acc hE

/-! ## The body's timeless core and its stores

`durBody` minus the stores' client authorities and `latestDur` (which mention the client's
predicates, not known to be timeless) is timeless: opening `srvDurInv` strips its later. -/

/-- (R2) **The timeless part of `durBody`**: gprot's halves, the views' halves, the couplings, the
compaction bound, the pending-install record's half and the pending steps' premises. -/
def durCore (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    ghostVar rc.dur.sv (1 : Qp).half (X.s, X.tp, X.dp) ∗ ghostVar rc.dur.st (1 : Qp).half (X.D, X.A.staged) ∗
    ghostVar rc.dur.tv (1 : Qp).half X.s.term ∗ ghostVar rc.dur.cv (1 : Qp).half X.s.cidx ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1 ∧ (((∀ d, X.dp = some d → X.lo ≤ d.x) ∧
      (∀ x st id, X.pend = some (x, st, id) → ∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∧ X.lo ≤ latIdxD X.lat + 1) ∧
      ((∀ d, X.dp = some d → X.c < d.x) ∧ ((X.tp = none ∨ X.dp = none) ∧
        (∀ d, X.dp = some d → ∃ m b, X.lat = some (m, b) ∧ uint.nat m.Index' = d.x ∧ uint.nat m.Term' = d.st))))⌝ ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half X.c ∗ ghostVar rc.dur.pend (1 : Qp).half X.pend ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp ∗ monoNatAuthOwn rc.dur.lat 1 (latIdxD X.lat))

/-- (R2) **The rest of `durBody`**: the stores' client authorities and what raft keeps about the
snapshot store (`latestDur`). -/
def durStores (X : SrvDur) : IProp GF :=
  iprop(rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat ∗ latestDur γ rc i X.lat X.pend X.dp)

section timeless
open gprot

instance crash_srvOwn_timeless γ i s : Timeless (srvOwn (GF := GF) γ i s) := by
  unfold srvOwn; infer_instance
instance crash_durView_timeless γ i q d : Timeless (durView (GF := GF) γ i q d) := by
  unfold durView; infer_instance
instance crash_logCouple_timeless γ i L : Timeless (logCouple (GF := GF) γ i L) := by
  unfold logCouple; infer_instance
instance crash_termCouple_timeless γ i t : Timeless (termCouple (GF := GF) γ i t) := by
  unfold termCouple; infer_instance
instance crash_cidxCouple_timeless γ i c : Timeless (cidxCouple (GF := GF) γ i c) := by
  unfold cidxCouple; infer_instance
instance crash_compLb_timeless rc c : Timeless (compLb (GF := GF) rc c) := by
  unfold compLb; infer_instance
instance crash_isSrv_timeless γ i : Timeless (isSrv (GF := GF) γ i) := by
  unfold isSrv; infer_instance
instance crash_leaderIs_timeless γ T ℓ : Timeless (leaderIs (GF := GF) γ T ℓ) := by
  unfold leaderIs; infer_instance
instance crash_candIs_timeless γ c T li lt : Timeless (candIs (GF := GF) γ c T li lt) := by
  unfold candIs; infer_instance
instance crash_termLb_timeless γ i t : Timeless (termLb (GF := GF) γ i t) := by
  unfold termLb; infer_instance
instance crash_llogIdx_timeless γ T k e : Timeless (llogIdx (GF := GF) γ T k e) := by
  unfold llogIdx; infer_instance
instance crash_commitIs_timeless γ T k p : Timeless (commitIs (GF := GF) γ T k p) := by
  unfold commitIs; infer_instance
instance crash_pubIs_timeless γ T k : Timeless (pubIs (GF := GF) γ T k) := by
  unfold pubIs; infer_instance
instance crash_termOk_timeless γ t : Timeless (termOk (GF := GF) γ t) := by
  unfold termOk; infer_instance
instance crash_lciOk_timeless γ T lci : Timeless (lciOk (GF := GF) γ T lci) := by
  unfold lciOk; infer_instance
instance crash_aeValid_timeless γ T prev pt ents lci :
    Timeless (aeValid (GF := GF) γ T prev pt ents lci) := by
  unfold aeValid; infer_instance
instance crash_tpRes_timeless γ tp : Timeless (tpRes (GF := GF) γ tp) := by
  unfold tpRes; rcases tp with _ | (_ | _) <;> infer_instance
instance crash_dpRes_timeless γ i s dp : Timeless (dpRes (GF := GF) γ i s dp) := by
  unfold dpRes; rcases dp with _ | _ <;> infer_instance

end timeless

instance durCore_timeless (X : SrvDur) : Timeless (durCore γ rc i X) := by
  unfold durCore; infer_instance

/-- (R2) `durBody` is its core, its stores and the boot pin. -/
theorem durBody_split (X : SrvDur) :
    durBody γ rc i X ⊣⊢ durCore γ rc i X ∗ durStores γ rc i X ∗ bootPin rc X := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- (R2) **Opening `srvDurInv`**, the core without its later (timeless), the stores under it. -/
theorem durOpen {E : CoPset} (hE : ↑durN ⊆ E) :
    srvDurInv γ rc i ⊢ |NC={E, E \ ↑durN}=> ∃ X : SrvDur, durCore γ rc i X ∗ ▷ durStores γ rc i X ∗
      (∀ X' : SrvDur, durCore γ rc i X' -∗ ▷ durStores γ rc i X' ={E \ ↑durN, E}=∗ True) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- (R2) The main goroutine's view agrees with the crash state. -/
theorem durCore_srvVP_agree (X : SrvDur) (s : SState) (tp : Option TermPend) (dp : Option DiscPend) :
    durCore γ rc i X ∗ srvVP rc s tp dp ⊢
      durCore γ rc i X ∗ srvVP rc s tp dp ∗ ⌜X.s = s ∧ X.tp = tp ∧ X.dp = dp⌝ := by
  iintro ⟨Hc, Hv⟩
  unfold durCore srvVP
  icases Hc with ⟨H1, H2, H3, H4, H5, Hsv, H7⟩
  icombine Hsv Hv gives %H
  have H := H.2
  simp only [Prod.mk.injEq] at H
  iframe
  ipureintro; exact H

/-- (R2) The stable store's view (with the staged commit index) agrees with the crash state. -/
theorem durCore_stVS_agree (X : SrvDur) (D : StableAbs) (g : w64) :
    durCore γ rc i X ∗ stVS rc D g ⊢ durCore γ rc i X ∗ stVS rc D g ∗ ⌜X.D = D ∧ X.A.staged = g⌝ := by
  iintro ⟨Hc, Hv⟩
  unfold durCore stVS
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, Hst, H8⟩
  icombine Hst Hv gives %H
  have H := H.2
  simp only [Prod.mk.injEq] at H
  iframe
  ipureintro; exact H

/-- (R2) The term atomic's view agrees with the crash state's term. -/
theorem durCore_termV_agree (X : SrvDur) (t : Nat) :
    durCore γ rc i X ∗ termV rc t ⊢ durCore γ rc i X ∗ termV rc t ∗ ⌜X.s.term = t⌝ := by
  iintro ⟨Hc, Hv⟩
  unfold durCore termV
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, Htv, H9⟩
  icombine Htv Hv gives %H
  iframe
  ipureintro; exact H.2

/-- (R2) The commit index atomic's view agrees with the crash state's `cidx`. -/
theorem durCore_cidxV_agree (X : SrvDur) (c : Nat) :
    durCore γ rc i X ∗ cidxV rc c ⊢ durCore γ rc i X ∗ cidxV rc c ∗ ⌜X.s.cidx = c⌝ := by
  iintro ⟨Hc, Hv⟩
  unfold durCore cidxV
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, H8, Hcv, H10⟩
  icombine Hcv Hv gives %H
  iframe
  ipureintro; exact H.2

/-- (R2) **A step of the main goroutine on the crash state** (generic): with its view of `s` (and
the pending records `tp`, `dp`), any update of the core and the view together, the stores passed
through under their later (the continuation may use gprot's laws on the core's halves and must
re-establish the couplings). The wrapper laws (`core/CrashLaws.lean`) are its instances. -/
theorem durStep {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) (tp : Option TermPend)
    (dp : Option DiscPend) (P : IProp GF) (Q : SrvDur → IProp GF) :
    srvDurInv γ rc i ∗ srvVP rc s tp dp ∗ P ∗
      (∀ X : SrvDur, ⌜X.s = s ∧ X.tp = tp ∧ X.dp = dp⌝ -∗ durCore γ rc i X -∗ ▷ durStores γ rc i X -∗
        srvVP rc s tp dp -∗ P -∗
        |={E \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗ ▷ durStores γ rc i X' ∗
          srvVP rc X'.s X'.tp X'.dp ∗ Q X') ⊢
      |NC={E}=> ∃ X' : SrvDur, srvVP rc X'.s X'.tp X'.dp ∗ Q X' := by
  iintro ⟨#Hi, Hv, HP, Hf⟩ Hnc
  imod (durOpen γ rc i hE) $$ Hi Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hv]
  · iframe
  imod Hf $$ %X %Hag Hc Hs Hv HP with ⟨%X', Hc', Hs', Hv', HQ⟩
  imod Hcl $$ %X' Hc' Hs' with -
  imodintro
  iframe Hnc
  iexists X'
  iframe

/-! ## Arming and crashing -/

/-- (R2) **What a vacant server keeps of its snapshot store** (`latestDur` with no install pending and
without the dead generation's `lastApplied` half, which a generation's arm makes afresh): the latest's
facts, and its index durable or installed while following with its discard pending. -/
def latestDurV (lat : SnapLatest) (dp : Option DiscPend) : IProp GF :=
  iprop(latestOk γ rc lat ∗
    (⌜lat = none⌝ ∨ ∃ (m : SnapshotMeta) (b : List w8), ⌜lat = some (m, b)⌝ ∗
      (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term') ∗
        ⌜∃ ℓ, dp = some ⟨uint.nat m.Index', uint.nat m.Term', ℓ⟩⌝)))

/-- (hraft_robust L0, R1 §1.3, §6.1) **What a generation of server `i` starts from**: gprot's halves
and the stores' client authorities (`rc.ownL`, `rc.ownS`, `rc.ownSS`: the generation's handles, fixed before it
runs; `rc`'s names are not used) at the crash state `X`, with the couplings, but no generation's names yet (`raft_arm` allocates
them). A fresh server's is its genesis state; a restarted one's comes from `raft_crash`. -/
def srvVacant (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1 ∧ uint.nat X.A.staged ≤ X.s.dur.1 ∧ X.pend = none ∧
      (((∀ d, X.dp = some d → X.lo ≤ d.x) ∧
        (∀ x st id, X.pend = some (x, st, id) → ∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∧ X.lo ≤ latIdxD X.lat + 1) ∧
        ((∀ d, X.dp = some d → X.c < d.x) ∧ ((X.tp = none ∨ X.dp = none) ∧
        (∀ d, X.dp = some d → ∃ m b, X.lat = some (m, b) ∧ uint.nat m.Index' = d.x ∧ uint.nat m.Term' = d.st))))⌝ ∗
    latestDurV γ rc i X.lat X.dp ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

theorem latestOk_snapP (rc0 rc1 : RCtx GF) (lat : SnapLatest) (h : rc1.snapP = rc0.snapP) :
    latestOk γ rc1 lat = latestOk γ rc0 lat := by
  rcases lat with _ | ⟨m, b⟩
  · rfl
  · simp only [latestOk, h]

theorem latestOk_dur (rc0 : RCtx GF) (dn : DurNames) (lat : SnapLatest) :
    latestOk γ { rc0 with dur := dn } lat = latestOk γ rc0 lat := by
  rcases lat with _ | ⟨m, b⟩ <;> rfl

/-- (R2) **Arming a generation** (at boot, before its WP): fresh crash-state names, the crash
invariant (for the context `rc` with those names and the generation's store handles), the crash
token for the crash wand, and the generation's initial resources: the main goroutine's views, the
atomics' views, the `lastApplied` authority (at `0`, both halves), the compaction frontier's
authority (at `X.c`), the main goroutine's half of the pending-install record (none) and its
pending-write record (`pw`, none).
(R2: a fancy update, for the invariant's allocation; was `|==>`.) -/
theorem raft_arm {E : CoPset} (rc0 : RCtx GF) (X : SrvDur) :
    srvVacant γ rc0 i X ⊢ |={E}=> ∃ dn : DurNames,
      srvDurInvRaw γ { rc0 with dur := dn } i ∗ srvCrashTok { rc0 with dur := dn } ∗
      srvVP { rc0 with dur := dn } X.s X.tp X.dp ∗ stVS { rc0 with dur := dn } X.D X.A.staged ∗
      termV { rc0 with dur := dn } X.s.term ∗ cidxV { rc0 with dur := dn } X.s.cidx ∗
      monoNatAuthOwn dn.applied (1 : Qp).half 0 ∗
      (monoNatAuthOwn dn.applied (1 : Qp).half 0 ∨ ⌜∃ d, X.dp = some d⌝) ∗
      monoNatAuthOwn dn.comp (1 : Qp).half X.c ∗
      ghostVar dn.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      ghostVar dn.pw 1 (none : Option Pend) ∗
      dghostVar dn.boot (DFrac.own (1 : Qp).half) (some (X.A, X.lat)) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- (R2) **The dead generation's crash state, without the stores' authorities**: gprot's halves, the
couplings (with the dead stores' states `X.A`, `X.D`), `latestDur`, the pending steps' premises. -/
def deadCore (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1 ∧ (((∀ d, X.dp = some d → X.lo ≤ d.x) ∧
      (∀ x st id, X.pend = some (x, st, id) → ∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∧ X.lo ≤ latIdxD X.lat + 1) ∧
      ((∀ d, X.dp = some d → X.c < d.x) ∧ ((X.tp = none ∨ X.dp = none) ∧
        (∀ d, X.dp = some d → ∃ m b, X.lat = some (m, b) ∧ uint.nat m.Index' = d.x ∧ uint.nat m.Term' = d.st))))⌝ ∗
    latestDur γ rc i X.lat X.pend X.dp ∗ tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

/-- (R2) What `raft_crash` leaves: `deadCore` and `durBody`'s halves of the main goroutine's state
and stable-store views (for a surviving window's agreement, `dead_fire`). -/
def srvDead (X : SrvDur) : IProp GF :=
  iprop(deadCore γ rc i X ∗ ghostVar rc.dur.sv (1 : Qp).half (X.s, X.tp, X.dp) ∗
    ghostVar rc.dur.st (1 : Qp).half (X.D, X.A.staged))

/-- (R2, R1 §1.3) **The crash of a generation**: with `crashed`, the generation's crash token and a
later credit (`durBody`'s stores are not timeless), the crash state is taken out of the invariant
(its crashed side closed with the token): the dead state and the dead generation's store
authorities, for the store's crash lemma (stage R3, `diskCrash`) to re-key to the next generation's
handles at the surviving image. Then a surviving window is fired (`dead_fire`) and the next
generation's vacant state made (`dead_vacant`). (Was one law taking the window; the window can only
be fired once the store's crash lemma says what survived, and that lemma needs the authorities.) -/
theorem raft_crash {E : CoPset} (hE : ↑durN ⊆ E) :
    crashed -∗ srvCrashTok rc -∗ srvDurInvRaw γ rc i -∗ £ 1 ={E}=∗
      ∃ X : SrvDur, srvDead γ rc i X ∗ rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end crash

end github_com.hashicorp.raft

end Perennial
