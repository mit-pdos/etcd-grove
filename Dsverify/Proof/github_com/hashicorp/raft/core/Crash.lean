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
    srvDurInv γ rc i ⊢ |NC={E, E \ ↑durN}=> ▷ (∃ X : SrvDur, durBody γ rc i X) ∗
      (▷ (∃ X : SrvDur, durBody γ rc i X) ={E \ ↑durN, E}=∗ True) := by
  unfold srvDurInv
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
      uint.nat X.A.ci ≤ X.s.dur.1⌝ ∗
    compLb rc X.c ∗ ghostVar rc.dur.pend (1 : Qp).half X.pend ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

/-- (R2) **The rest of `durBody`**: the stores' client authorities and what raft keeps about the
snapshot store (`latestDur`). -/
def durStores (X : SrvDur) : IProp GF :=
  iprop(rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat ∗ latestDur γ rc i X.lat X.pend)

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

/-- (R2) `durBody` is its core and its stores. -/
theorem durBody_split (X : SrvDur) : durBody γ rc i X ⊣⊢ durCore γ rc i X ∗ durStores γ rc i X := by
  unfold durBody durCore durStores
  refine ⟨?_, ?_⟩
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, HL, HS, HSS, Hp, Hc, Hl, Hpe, Ht, Hd⟩
    iframe
  · iintro ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, Hp, Hc, Hpe, Ht, Hd⟩, HL, HS, HSS, Hl⟩
    iframe

/-- (R2) **Opening `srvDurInv`**, the core without its later (timeless), the stores under it. -/
theorem durOpen {E : CoPset} (hE : ↑durN ⊆ E) :
    srvDurInv γ rc i ⊢ |NC={E, E \ ↑durN}=> ∃ X : SrvDur, durCore γ rc i X ∗ ▷ durStores γ rc i X ∗
      (∀ X' : SrvDur, durCore γ rc i X' -∗ ▷ durStores γ rc i X' ={E \ ↑durN, E}=∗ True) := by
  iintro #Hi Hnc
  imod (durAcc γ rc i hE) $$ Hi Hnc with ⟨Hnc, HX, Hcl⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  ihave HX := later_mono (durBody_split γ rc i X).1 $$ HX
  icases HX with ⟨>Hc, Hs⟩
  imodintro
  iframe Hnc
  iexists X
  iframe Hc Hs
  iintro %X' Hc' Hs'
  iapply Hcl
  iapply later_exists_mp
  iexists X'
  inext
  iapply (durBody_split γ rc i X').2
  iframe

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

/-- (hraft_robust L0, R1 §1.3, §6.1) **What a generation of server `i` starts from**: gprot's halves
and the stores' client authorities (`rc.ownL`, `rc.ownS`, `rc.ownSS`: the generation's handles, fixed before it
runs; `rc`'s names are not used) at the crash state `X`, with the couplings, but no generation's names yet (`raft_arm` allocates
them). A fresh server's is its genesis state; a restarted one's comes from `raft_crash`. -/
def srvVacant (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1 ∧ uint.nat X.A.staged ≤ X.s.dur.1 ∧ X.pend = none⌝ ∗
    latestOk γ rc X.lat ∗
    (⌜X.lat = none⌝ ∨ ∃ (m : SnapshotMeta) (b : List w8), ⌜X.lat = some (m, b)⌝ ∗
      (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term'))) ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

/-- (R2) **Arming a generation** (at boot, before its WP): fresh crash-state names, the crash
invariant (for the context `rc` with those names and the generation's store handles), the crash
token for the crash wand, and the generation's initial resources: the main goroutine's views, the
atomics' views, the `lastApplied` authority (at `0`, both halves), the compaction frontier's
authority (at `X.c`) and the main goroutine's half of the pending-install record (none).
(R2: a fancy update, for the invariant's allocation; was `|==>`.) -/
theorem raft_arm {E : CoPset} (rc0 : RCtx GF) (X : SrvDur) :
    srvVacant γ rc0 i X ⊢ |={E}=> ∃ dn : DurNames,
      srvDurInv γ { rc0 with dur := dn } i ∗ srvCrashTok { rc0 with dur := dn } ∗
      srvVP { rc0 with dur := dn } X.s X.tp X.dp ∗ stVS { rc0 with dur := dn } X.D X.A.staged ∗
      termV { rc0 with dur := dn } X.s.term ∗ cidxV { rc0 with dur := dn } X.s.cidx ∗
      monoNatAuthOwn dn.applied 1 0 ∗ monoNatAuthOwn dn.comp 1 X.c ∗
      ghostVar dn.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **The dead generation's crash state, without the stores' authorities**: gprot's halves, the
couplings (with the dead stores' states `X.A`, `X.D`), `latestDur`, the pending steps' premises. -/
def deadCore (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1⌝ ∗
    latestDur γ rc i X.lat X.pend ∗ tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

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
    crashed -∗ srvCrashTok rc -∗ srvDurInv γ rc i -∗ £ 1 ={E}=∗
      ∃ X : SrvDur, srvDead γ rc i X ∗ rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **The window resource at the main goroutine's state `s`** (what a write's caller lends as
the contracts' `W`, `winAt_winRes`): its view `srvV rc s`, its stable-store view with the staged
commit index (lent too, so that the crash knows the written commit index durable), the law's
premises, and the store facts the step's coupling needs (`winPure`). -/
def winPure (s : SState) (D : StableAbs) (g : w64) : Pend → Prop
  | .app _ => uint.nat g ≤ s.dur.1
  | .cfg _ _ _ => uint.nat g ≤ s.dur.1
  | .fstore _ _ _ lci _ lc => (lc = none → uint.nat g ≤ s.dur.1) ∧
      (∀ v, lc = some v → uint.nat g ≤ Min.min lci v)
  | .vote c _ _ => D.bytes.lookup (go!"LastVoteCand" : List w8) = some c
  | _ => True

def winAt (s : SState) (p : Pend) : IProp GF :=
  iprop(winRes γ rc i s p ∗ ∃ (D : StableAbs) (g : w64), stVS rc D g ∗ ⌜winPure s D g p⌝)

theorem winAt_winRes (s : SState) (p : Pend) : winAt γ rc i s p ⊢ winRes γ rc i s p := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **What a write that fires `p` from `s` leaves in the stores** (`A'`, `D'`, against the dead
state's `X.A`, `X.D`): what the store's crash lemma must say of the surviving image (the stores'
volatile parts, `hi` and `staged`, are not constrained). -/
def pendStoreOk (p : Pend) (s : SState) (X : SrvDur) (A' : LogAbs) (D' : StableAbs) : Prop :=
  match p with
  | .app es => A'.m = LogAbs.ins X.A.m (s.log.length + 1) es ∧ A'.ci = X.A.staged ∧ D' = X.D
  | .cfg e _ _ => A'.m = LogAbs.ins X.A.m (s.log.length + 1) [e] ∧ A'.ci = X.A.staged ∧ D' = X.D
  | .fstore _ _ ents _ j _ => A'.m = LogAbs.ins X.A.m (s.log.length + 1) (ents.drop j) ∧
      A'.ci = X.A.staged ∧ D' = X.D
  | .trunc prev _ _ _ j => (∃ mx : Nat, s.log.length ≤ mx ∧ A'.m = LogAbs.del X.A.m (prev + 1 + j) mx) ∧
      A'.ci = X.A.ci ∧ D' = X.D
  | .discard _ => (∃ mn mx : Nat, (∀ k e, X.A.m.lookup k = some e → mn ≤ k ∧ k ≤ mx) ∧
      A'.m = LogAbs.del X.A.m mn mx) ∧ A'.ci = X.A.ci ∧ D' = X.D
  | .vote _ _ _ => A'.m = X.A.m ∧ A'.ci = X.A.ci ∧ ∃ T : w64, uint.nat T = s.term ∧
      D' = { X.D with ints := X.D.ints.insert (go!"LastVoteTerm" : List w8) T }
  | .term tp => A'.m = X.A.m ∧ A'.ci = X.A.ci ∧ ∃ t : w64,
      (tp = .set (uint.nat t) ∨ (tp = .elect ∧ uint.nat t = s.term + 1)) ∧
      D' = { X.D with ints := X.D.ints.insert (go!"CurrentTerm" : List w8) t }

/-- (R2, R1 §3: `pend_fire`) **Firing a surviving window**: the window's view agrees with the dead
state's (`s = X.s`), and its step is fired with gprot's law on `deadCore`'s halves, the couplings
re-established against the surviving image `A'`, `D'` (`pendStoreOk`). A term write's step is only
recorded (`tp`), fired by `dead_vacant`. -/
theorem dead_fire {E : CoPset} (hE : ↑gprotN ⊆ E) [hRB : ReceiptBoundLe GF (2 ^ 62)]
    (p : Pend) (s : SState) (X : SrvDur) (A' : LogAbs) (D' : StableAbs)
    (hst : pendStoreOk p s X A' D') :
    Inv γ ∗ srvDead γ rc i X ∗ winAt γ rc i s p ⊢ |={E}=> ∃ X' : SrvDur, deadCore γ rc i X' ∗
      ⌜X'.A.m = A'.m ∧ X'.A.ci = A'.ci ∧ X'.D = D' ∧ X'.lat = X.lat ∧ X'.pend = X.pend⌝ := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) No window survived: the dead state as is. -/
theorem srvDead_deadCore (X : SrvDur) : srvDead γ rc i X ⊢ deadCore γ rc i X := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **The next generation's vacant state**, from the dead state and the store authorities of
the next generation's handles `rc'` at the surviving image (the same entries and written commit
index; the staged index durable, `0` after a reopen): the pending term step fired
(`setTerm_upd`/`electTerm_upd` from `tpRes`), the pending install record dropped (its `snapFollow`
kept), and the commit index reset (`setCidx_upd … 0`, the atomic being volatile). A pending discard
is kept (`dp`, for `NewRaft`'s fix 2), unless the term step changed the term (then dropped). -/
theorem dead_vacant {E : CoPset} (hE : ↑gprotN ⊆ E) [hRB : ReceiptBoundLe GF (2 ^ 62)]
    (rc' : RCtx GF) (X : SrvDur) (A' : LogAbs) (D' : StableAbs) (lat' : SnapLatest)
    (h : A'.m = X.A.m ∧ A'.ci = X.A.ci ∧ uint.nat A'.staged ≤ X.s.dur.1 ∧ D' = X.D ∧
      lat' = X.lat ∧ rc'.snapP = rc.snapP) :
    Inv γ ∗ deadCore γ rc i X ∗ rc'.ownL A' ∗ rc'.ownS D' ∗ rc'.ownSS lat' ⊢ |={E}=>
      ∃ X' : SrvDur, srvVacant γ rc' i X' ∗
        ⌜X'.s.cidx = 0 ∧ X'.tp = none ∧ X'.A = A' ∧ X'.D = D' ∧ X'.lat = lat' ∧
          X'.s.log = X.s.log ∧ X'.s.dur = X.s.dur⌝ := by
  sorry -- hraft_robust R2: proof pending

end crash

end github_com.hashicorp.raft

end Perennial
