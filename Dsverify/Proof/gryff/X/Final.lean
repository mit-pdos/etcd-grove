/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Final.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: the executor's laws at `GF`, and the interface's specs

`execLaws` builds `ExecLaws` from `Replica2/*` and `Proto2/*` (the lock invariant
`replicaLockInv`, `critical_step`, `resolveExec.wp`, `pendingOuts_self`, `step_ok_exec`,
`traceHalf_lb`, `traceHalf_lb_prefix`); `strongconnect_wp` and `executeCommands_wp` are
`Replica2/Results.lean`'s `strongconnect.wp` and `executeCommands.wp` (restated; the link module
proves them by these) from the generic `wp_sc` and `wp_executeCommands`.
-/
module

public import Dsverify.Proof.gryff.X.Bridge
public import Dsverify.Proof.gryff.X.ExecCmds
public import Dsverify.Proof.gryff.Replica.Base
public import Dsverify.Proof.gryff.Proto2.Laws
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy Msg Ev Out StepRes committedCopy execGuard inBox)
open Perennial.gryff.replica (XS Node TInv Post)
open Perennial.gryff.replica2
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


/-! ## The remaining equalities -/

theorem bagAt_eq {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t] (ρ : Repl2Names) (T : Type) (l : Loc)
    (f : GoString) (nm : String) (P : V → IProp GF) :
    bagAt (t := t) ρ T l f nm P = bagAtG (hG := hG) (t := t) ρ T l f nm P := by
  unfold bagAt bagAtG; rfl

theorem recoverChanP_eq (ρ : Repl2Names) :
    recoverChanP ρ = recoverChanPG (hG := hG) ρ := by
  funext p; unfold recoverChanP recoverChanPG; rfl

theorem eoChanP_eq (γ : GryffNames GF) (k : Fin 3) :
    eoChanP γ k = eoChanPG (hG := hG) (fun m => iprop(∃ n, rxTok γ.proto k k n m)) := by
  funext p; unfold eoChanP eoChanPG msgAt; rfl

theorem execPriv2_eq (ρ : Repl2Names) (h : Loc) (xs : XS) (S : List replica.Node) :
    execPriv2 ρ h xs S = execPrivG (hG := hG) ρ h xs S := by
  unfold execPriv2 execPrivG; rfl

omit sem in
theorem handlerIface_inj [GoSemanticsFunctions] [go.BasicIntoValInj] {h h' : Loc} (e : handlerIface h = handlerIface h') : h = h' := by
  unfold handlerIface at e
  exact go.intoVal_inj ((interface_mkOk_inj _ _ _ _).1 e).2

theorem dlog_of_gryff :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ⊢ globalAddr src.dlog.DLOG ↦□ false := by
  iintro #H
  iapply replica.dlog_init_access
  iPkgInit

/-! ## The laws' predicates -/

/-- The replica's heap but the EPaxos handler's part and the search state's half (`replicaOwnX`'s
other conjuncts, the handler fixed to `h`). -/
def RsX (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (s : RState) : IProp GF :=
  iprop(∃ (gR pa co : Loc),
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗
    r.[src.gryff.Replica, go!"coord"] ↦□ co ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    partiOwn pa (replicaIface r) k s.tag s.ongoing ∗ valOwn gR s.val ∗
    coordOwn ρ co (replicaIface r) k s ∗
    proposeOwn ρ gR s.proposeQ ∗ scratchOwn r ∗ ⌜s.id = rid32 k⌝)

/-- The persistent facts. -/
def InvX (γ : GryffNames GF) (r h : Loc) : IProp GF :=
  iprop(gryffInv2 γ.proto ∗ predsSet γ.proto ∗ r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h)

instance InvX_pers (γ : GryffNames GF) (r h : Loc) : Persistent (InvX γ r h) := by
  unfold InvX; infer_instance

theorem epaxosOwn_toG (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwn ρ h r xs s ⊢ epaxosOwnG (hG := hG) ρ h r xs s := by
  rw [epaxosOwn_eq]

theorem epaxosOwn_ofG (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwnG (hG := hG) ρ h r xs s ⊢ epaxosOwn ρ h r xs s := by
  rw [epaxosOwn_eq]

/-- `lockedAt`, with the handler's field, opened. -/
theorem lockedAt_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (p : ProphId)
    (t : List Ev) (xs : XS) :
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗ lockedAt γ ρ k r p t xs ⊢
      traceHalf γ.proto k t ∗ replicaProph γ.proto k p t [] ∗ RsX ρ k r h (stOf k t) ∗
      epaxosOwnG (hG := hG) ρ h r xs (stOf k t) ∗ ghostVar ρ.xs (1 : Qp).half xs ∗
      pendingOuts γ ρ k r t [] ∗ ghostVar ρ.boot (1 : Qp).half false := by
  iintro ⟨#Hh, HL⟩
  unfold lockedAt
  icases HL with ⟨HTH, HPr, HRO, HPO, HBt⟩
  icases (replicaOwnX_split ..).1 $$ HRO with ⟨%gR, %pa, %co, %h', #HrR, #Hpa, #Hco, #Hh', Hparti,
    Hval, Hcoord, HEP, Hxs, Hprop, Hscr, %Hid⟩
  icombine Hh Hh' gives %he
  cases handlerIface_inj he
  iframe
  isplitr [HEP]
  · unfold RsX; iexists gR, pa, co; iframe; iframe HrR Hpa Hco Hh; ipureintro; exact Hid
  · iapply epaxosOwn_toG; iexact HEP

theorem lockedAt_close (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (p : ProphId)
    (t : List Ev) (xs : XS) :
    traceHalf γ.proto k t ∗ replicaProph γ.proto k p t [] ∗ RsX ρ k r h (stOf k t) ∗
      epaxosOwnG (hG := hG) ρ h r xs (stOf k t) ∗ ghostVar ρ.xs (1 : Qp).half xs ∗
      pendingOuts γ ρ k r t [] ∗ ghostVar ρ.boot (1 : Qp).half false ⊢
    lockedAt γ ρ k r p t xs := by
  iintro ⟨HTH, HPr, HRs, HEP, Hxs, HPO, HBt⟩
  unfold lockedAt RsX
  icases HRs with ⟨%gR, %pa, %co, #HrR, #Hpa, #Hco, #Hh, Hparti, Hval, Hcoord, Hprop, Hscr, %Hid⟩
  iframe
  iapply (replicaOwnX_split ..).2
  iexists gR, pa, co, h
  iframe
  iframe HrR Hpa Hco Hh
  isplitl [HEP]
  · iapply epaxosOwn_ofG; iexact HEP
  · ipureintro; exact Hid

theorem RsX_congr (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (s s' : RState)
    (h0 : s'.id = s.id) (h1 : s'.tag = s.tag) (h2 : s'.ongoing = s.ongoing) (h3 : s'.val = s.val)
    (h4 : s'.maxN = s.maxN) (h5 : s'.rops = s.rops) (h6 : s'.wops = s.wops)
    (h7 : s'.ongoingReqs = s.ongoingReqs) (h8 : s'.proposeQ = s.proposeQ) (h9 : s'.id = s.id) :
    RsX (GF := GF) ρ k r h s ⊢ RsX ρ k r h s' := by
  unfold RsX
  rw [h0, h1, h2, h3, h8]
  iintro ⟨%gR, %pa, %co, #H1, #H2, #H3, #H4, Hp, Hv, Hc, Hq, Hs, %Hid⟩
  iexists gR, pa, co
  iframe
  iframe H1 H2 H3 H4
  isplitl [Hc]
  · iapply coordOwn_congr ρ co _ k s s' h4 h5 h6 h7; iexact Hc
  · ipureintro; exact Hid

theorem gryffN_top : (↑gryffN : CoPset) ⊆ ⊤ := CoPset.subseteq_top

/-- **The executor's laws at `GF`.** -/
def execLaws (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (p : ProphId) :
    ExecLaws (GF := GF) k ρ r h p where
  TH := traceHalf γ.proto k
  TLb := traceLb γ.proto k
  Pr t ws := replicaProph γ.proto k p t ws
  PO := pendingOuts γ ρ k r
  Rs := RsX ρ k r h
  Bt := ghostVar ρ.boot (1 : Qp).half false
  B := ghostVar ρ.boot (1 : Qp).half true
  Tok m := iprop(∃ n, rxTok γ.proto k k n m)
  LI := replicaLockInv γ ρ k r p
  Inv := InvX γ r h
  tlb_pers _ := inferInstance
  inv_pers := inferInstance
  li_open := by
    iintro ⟨#HI, HLI⟩
    unfold replicaLockInv
    icases HLI with (⟨%t, %xs, HL⟩ | HB)
    · ileft
      iexists t, xs
      iapply lockedAt_open (hG := hG)
      unfold InvX
      icases HI with ⟨-, -, #Hh⟩
      iframe
      iexact Hh
    · iright
      unfold lockBoot
      icases HB with ⟨%h', %xs, #Hh', HEP, Hxs, HB⟩
      unfold InvX
      icases HI with ⟨-, -, #Hh⟩
      icombine Hh Hh' gives %he
      cases handlerIface_inj he
      iexists xs
      iframe
      iapply epaxosOwn_toG; iexact HEP
  li_closeA t xs := by
    iintro H
    unfold replicaLockInv
    ileft
    iexists t, xs
    iapply lockedAt_close (hG := hG)
    iexact H
  li_closeB xs := by
    iintro ⟨#HI, HEP, Hxs, HB⟩
    unfold replicaLockInv
    iright
    unfold lockBoot InvX
    icases HI with ⟨-, -, #Hh⟩
    iexists h, xs
    iframe
    isplitr
    · iexact Hh
    · iapply epaxosOwn_ofG; iexact HEP
  th_lb t := by
    iintro H
    -- `traceHalf_lb` reads `(|==> traceHalf γ k t) ∗ traceLb γ k t`
    icases traceHalf_lb γ.proto k t $$ H with ⟨H, #Hlb⟩
    imod H
    imodintro
    iframe
    iexact Hlb
  th_relock t t' := by
    iintro ⟨#HI, H, #Hlb⟩
    unfold InvX
    icases HI with ⟨#Hinv, -, -⟩
    imod trace_stable γ.proto k t t' ⊤ gryffN_top $$ [H] with ⟨H, %hs⟩ -- H-X-1
    · iframe; iframe Hinv Hlb
    imodintro
    iframe
    ipureintro
    exact ⟨hs.1, hs.2.1⟩
  th_kept t t' := by
    iintro ⟨#HI, H, #Hlb⟩
    unfold InvX
    icases HI with ⟨#Hinv, -, -⟩
    imod trace_stable γ.proto k t t' ⊤ gryffN_top $$ [H] with ⟨H, %hs⟩ -- H-X-1
    · iframe; iframe Hinv Hlb
    imodintro
    iframe
    ipureintro
    exact hs.2.2
  th_deps t := by
    iintro ⟨#HI, H⟩
    unfold InvX
    icases HI with ⟨#Hinv, -, -⟩
    imod trace_depsOk γ.proto k t ⊤ gryffN_top $$ [H] with ⟨H, %hd⟩ -- H-X-3
    · iframe; iexact Hinv
    imodintro
    iframe
    ipureintro
    exact hd
  th_ok t q i c hb hc hs hg := by
    iintro ⟨#HI, H⟩
    unfold InvX
    icases HI with ⟨#Hinv, -, -⟩
    iapply step_ok_exec γ.proto k t q i c hb hc hs hg ⊤ gryffN_top
    iframe
    iexact Hinv
  res_wp t ws q i := resolveExec.wp γ k r q i p t ws
  crit t q i s' outs hst := by
    iintro ⟨#HI, HTH, HPr, Hlc, HPO⟩
    unfold InvX
    icases HI with ⟨#Hinv, #Hpreds, -⟩
    iapply critical_step γ ρ k r p t (.exec q i) s' outs
    rw [show evTok γ.proto k (.exec q i) = iprop(True) from rfl]
    iframe
    isplitr
    · ipureintro; exact hst
    isplitr
    · iexact Hinv
    iexact Hpreds
  self t m outs := by
    iintro ⟨#HI, HPO⟩
    unfold InvX
    icases HI with ⟨#Hinv, -, -⟩
    imod pendingOuts_self γ ρ k r t m outs ⊤ gryffN_top $$ [HPO] with ⟨%j, HPO, Htok⟩
    · iframe; iexact Hinv
    imodintro
    iframe
  rs_congr s s' q i outs hst := by
    obtain ⟨c, hc, he⟩ := stepExec_ok hst
    obtain ⟨pv, rfl⟩ := execRes_state he
    exact RsX_congr ρ k r h _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rs_id s := by
    unfold RsX
    iintro ⟨%gR, %pa, %co, -, -, -, -, -, -, -, -, -, %Hid⟩
    ipureintro; exact Hid

theorem lockedAt_LA (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (p : ProphId) (t : List Ev) (xs : XS) :
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗ lockedAt γ ρ k r p t xs ⊢
      (execLaws γ ρ k r h p).LA t xs :=
  lockedAt_open γ ρ k r h p t xs

theorem LA_lockedAt (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (p : ProphId) (t : List Ev) (xs : XS) :
    (execLaws γ ρ k r h p).LA t xs ⊢ lockedAt γ ρ k r p t xs :=
  lockedAt_close γ ρ k r h p t xs

/-- The executor's handle at `GF`, from `isExec`. -/
theorem isExec_toG (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isExec γ ρ k r h ⊢
      ∃ (gR mtx ex : Loc) (p : ProphId), (execLaws γ ρ k r h p).isExecG gR mtx ex := by
  iintro ⟨#Hpkg, #HX⟩
  icases (isExec_open ..).1 $$ HX with ⟨%gR, %mtx, %ex, %p, #HrR, #Hh, #Hm, #Hp, -, #HR, #Hex,
    #Hexr, #HId, #HN, #HSd, #Hlock, #Heo, #Hrec, #Hinv, #Hpreds⟩
  ihave #Hdlog := dlog_of_gryff $$ Hpkg
  iexists gR, mtx, ex, p
  iapply (ExecLaws.isExecG_open ..).2
  rw [eoChanP_eq, recoverChanP_eq, bagAt_eq, bagAt_eq] at *
  rw [show (execLaws γ ρ k r h p).LI = replicaLockInv γ ρ k r p from rfl,
    show (execLaws γ ρ k r h p).Tok = (fun m => iprop(∃ n, rxTok γ.proto k k n m)) from rfl]
  isplitr
  · iexact HrR
  isplitr
  · iexact Hh
  isplitr
  · iexact Hm
  isplitr
  · iexact Hp
  isplitr
  · iexact HR
  isplitr
  · iexact Hex
  isplitr
  · iexact Hexr
  isplitr
  · iexact HId
  isplitr
  · iexact HN
  isplitr
  · iexact HSd
  isplitr
  · iexact Hlock
  isplitr
  · iexact Heo
  isplitr
  · iexact Hrec
  isplitr
  · unfold execLaws InvX
    isplitr
    · iexact Hinv
    isplitr
    · iexact Hpreds
    · iexact Hh
  · iexact Hdlog

/-! ## The interface's specs -/

/-- **`Replica2/Results.lean`'s `strongconnect.wp`** (from `wp_sc`; `scFacts2` is `SCF` since
H-X-2 (a)). -/
theorem strongconnect_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h ex mtx : Loc)
    (p : ProphId) (t : List Ev) (xs : XS) (S : List replica.Node) (idx : Nat)
    (Gs : List replica.Node) (vn : replica.Node) (v idxp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isExec γ ρ k r h ∗
        h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ r.[src.gryff.Replica, go!"mtx"] ↦□ mtx ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ sync.ownMutex mtx ∗ lockedAt γ ρ k r p t xs ∗
        execPriv2 ρ h xs S ∗ idxp ↦ W64 (idx : Int) ∗ ghostMapElem ρ.ptrs vn DFrac.discard v ∗
        ⌜TInv (model.depR (pure.stOf k t)) (xs.toT S idx) Gs ∧ vn ∉ xs.1 ∧ xs.numF vn = 0 ∧
          (model.committedCopy (pure.stOf k t) vn).isSome ∧ scFacts2 (pure.stOf k t) xs S idx⌝ }}
      (App (App (Val (ex @!! go.GoType.PointerType src.gryff.Exec.ty @!! go!"strongconnect"))
        (Val #v)) (Val #idxp))
    {{ RET #true; ∃ (t' : List Ev) (xs' : XS) (S' : List replica.Node) (idx' : Nat),
        sync.ownMutex mtx ∗ lockedAt γ ρ k r p t' xs' ∗ execPriv2 ρ h xs' S' ∗
        idxp ↦ W64 (idx' : Int) ∗
        ⌜t <+: t' ∧ Post (model.depR (pure.stOf k t')) (xs.toT S idx) Gs vn (xs'.toT S' idx') ∧
          scFacts2 (pure.stOf k t') xs' S' idx'⌝ }} := by
  iintro %Φ ⟨#Hpkg, #HX, #Hex, #Hm, #Hp, Hown, HL, Hpriv, Hidx, #Hv, %Hpre⟩ HΦ
  ihave ⟨%gR, %mtx', %ex', %p', #HG⟩ := isExec_toG γ ρ k r h $$ [Hpkg HX]
  · isplitr
    · iexact Hpkg
    · iexact HX
  icases (ExecLaws.isExecG_open ..).1 $$ HG with ⟨#HrR, #Hh, #Hm', #Hp', #HR, #Hex', #Hexr, -⟩
  icombine Hm Hm' gives %e1
  icombine Hp Hp' gives %e2
  icombine Hex Hex' gives %e3
  subst e1 e2 e3
  ihave HLA := lockedAt_LA γ ρ k r h p t xs $$ [HL]
  · isplitr
    · iexact Hh
    · iexact HL
  rw [execPriv2_eq]
  wp_apply wp_sc (execLaws γ ρ k r h p) gR mtx ex t xs S idx Gs vn v idxp
    $$ [Hown HLA Hpriv Hidx]
  · isplitr
    · iexact HG
    isplitl [Hown]
    · iexact Hown
    isplitl [HLA]
    · iexact HLA
    isplitl [Hpriv]
    · iexact Hpriv
    isplitl [Hidx]
    · iexact Hidx
    isplitr
    · iexact Hv
    ipureintro
    exact ⟨Hpre.1, Hpre.2.1, Hpre.2.2.1, Hpre.2.2.2.1, Hpre.2.2.2.2⟩ -- `scFacts2` = `SCF` (H-X-2 (a))
  iintro ⟨%t', %xs', %S', %idx', Hown, HLA, Hpriv, Hidx, %Hpost⟩
  iapply HΦ
  iexists t', xs', S', idx'
  ihave HL := LA_lockedAt γ ρ k r h p t' xs' $$ HLA
  rw [execPriv2_eq]
  iframe
  ipureintro
  exact ⟨Hpost.1, Hpost.2.1, Hpost.2.2⟩

/-- **`Replica2/Results.lean`'s `executeCommands.wp`** (from `wp_executeCommands`; `r.Shutdown ↦□
false` from `isExec` (H-X-4), the empty search state from the precondition (H-X-2 (b))). -/
theorem executeCommands_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (xs : XS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isExec γ ρ k r h ∗
        execPriv2 ρ h xs [] ∗ ⌜xs.1 = [] ∧ ∀ u, xs.numF u = 0⌝ }}
      (App (epM h go!"executeCommands") (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hpkg, #HX, Hpriv, %Hxs0⟩ HΦ
  ihave #HrSd : r.[src.gryff.Replica, go!"Shutdown"] ↦□ false $$ [HX]
  · icases (isExec_open ..).1 $$ HX with ⟨%gR, %mtx, %ex, %p, -, -, -, -, #HSd, -⟩
    iexact HSd
  ihave ⟨%gR, %mtx, %ex, %p, #HG⟩ := isExec_toG γ ρ k r h $$ [Hpkg HX]
  · isplitr
    · iexact Hpkg
    · iexact HX
  rw [execPriv2_eq]
  wp_apply wp_executeCommands (execLaws γ ρ k r h p) gR mtx ex xs $$ [Hpriv]
  · isplitr
    · iexact HG
    isplitr
    · iexact HrSd
    isplitl [Hpriv]
    · iexact Hpriv
    ipureintro
    exact Hxs0 -- H-X-2 (b)
  iapply HΦ
  itrivial

end

end Perennial.gryff.X
