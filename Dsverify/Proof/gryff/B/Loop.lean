/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Loop.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: the run loop (`EPaxosRMWHandler.Loop`): one `select` over 35 channels; each event case
locks, asserts the element's type, resolves the event (`Resolve.lean`), takes the step
(`critical_step_proof`), runs the handler (its `stepSpec`, a hypothesis here: the H units'),
unlocks.
-/
module

public import Dsverify.Proof.gryff.B.Resolve
public import Dsverify.Proof.gryff.B.Step
public import Dsverify.Proof.gryff.B.LockBoot
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model model.codec replica2
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
/-- An `*EPaxosRMWHandler` method value. -/
abbrev epMB (h : Loc) (f : GoString) : Expr :=
  Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! f)

end

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]

/-- The EPaxos handler `h` of `r` (`Replica2/Specs.lean`'s `handlerOf`). -/
abbrev handlerOfB (r h : Loc) : IProp GF :=
  iprop(r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h)

/-- A receive case of a `select` on a bag channel: two credits (shared by all cases: the cases'
preconditions are a conjunction), the bag, and the case body's WP on each element. -/
theorem clause_bag {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] [Pos.Countable V] (ch : Loc) (γc : ChanNames)
    (P : V → IProp GF) (body : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag γc ch P ∗ (▷ ∀ v, P v -∗ WP (App body (Val (PairV #v #true))) {{ Ψ }}) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Ψ := by
  iintro ⟨Hlc1, Hlc2, #Hb, Hk⟩
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Hb
  iapply bag_recv_au γc ch P (fun v ok => iprop(WP (App body (Val (PairV #v #ok))) {{ Ψ }})) $$
    [Hlc1 Hlc2] Hb Hk
  iframe

/-- `Replica2/Specs.lean`'s `stepSpec` (a handler refines its event's step). -/
def stepSpecB (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (call : Expr)
    (Pre : IProp GF) (e : Ev) : Prop :=
  ∀ (t : List Ev) (s s' : RState) (outs : List Out), model.stepR k s e = .ok (s', outs) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ Pre }}
      call
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }}

theorem msgKind_inv_read1 {m : Msg} (h : msgKind m = "read1") : ∃ mm, m = .read1 mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_read2 {m : Msg} (h : msgKind m = "read2") : ∃ mm, m = .read2 mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_read1Reply {m : Msg} (h : msgKind m = "read1Reply") : ∃ mm, m = .read1Reply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_read2Reply {m : Msg} (h : msgKind m = "read2Reply") : ∃ mm, m = .read2Reply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_write1 {m : Msg} (h : msgKind m = "write1") : ∃ mm, m = .write1 mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_write2 {m : Msg} (h : msgKind m = "write2") : ∃ mm, m = .write2 mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_write1Reply {m : Msg} (h : msgKind m = "write1Reply") : ∃ mm, m = .write1Reply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_write2Reply {m : Msg} (h : msgKind m = "write2Reply") : ∃ mm, m = .write2Reply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_preAccept {m : Msg} (h : msgKind m = "preAccept") : ∃ mm, m = .preAccept mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_preAcceptReply {m : Msg} (h : msgKind m = "preAcceptReply") : ∃ mm, m = .preAcceptReply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_preAcceptOK {m : Msg} (h : msgKind m = "preAcceptOK") : ∃ mm, m = .preAcceptOK mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_accept {m : Msg} (h : msgKind m = "accept") : ∃ mm, m = .accept mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_acceptReply {m : Msg} (h : msgKind m = "acceptReply") : ∃ mm, m = .acceptReply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_commit {m : Msg} (h : msgKind m = "commit") : ∃ mm, m = .commit mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_prepare {m : Msg} (h : msgKind m = "prepare") : ∃ mm, m = .prepare mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_prepareReply {m : Msg} (h : msgKind m = "prepareReply") : ∃ mm, m = .prepareReply mm := by
  cases m <;> simp [msgKind] at h ⊢

theorem msgKind_inv_executed {m : Msg} (h : msgKind m = "executed") : ∃ mm, m = .executed mm := by
  cases m <;> simp [msgKind] at h ⊢

/-- A client request element of the channel of kind `kd`, its struct of that kind (B-R2). -/
abbrev reqElem {T : Type} [TypedPointsto (GF := GF) T] (γ : GryffNames GF) (ρ : Repl2Names)
    (k : Fin 3) (ty : go.GoType) (evOf : T → Ev) (cidOf : T → w32) (c : Loc) : IProp GF :=
  iprop(∃ (p w : Loc) (g : T),
    c ↦ (src.genericsmr.ClientRPC.mk (interface.mkOk (go.GoType.PointerType ty) #p) w) ∗
    p ↦ g ∗ writerIs ρ (cidOf g) w ∗ evTok γ.proto k (evOf g) ∗ ⌜(evOf g).Producible⌝)

theorem reqChanP_read (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (c : Loc) :
    reqChanP γ ρ k "read" c ⊢
      reqElem γ ρ k src.gryffproto.Read.ty readEvOf (fun g => g.ClientId') c := by
  unfold reqChanP
  unfold reqAt
  simp only [String.reduceEq, ↓reduceIte]
  iintro ⟨%p, %w, %e, %cid, %rid, %i, Hc, Hreq, Hw, Htok, %He⟩
  icases Hreq with ⟨%g, Hp, %Hg⟩
  subst Hg
  obtain ⟨Hcr, Hpr⟩ := He
  simp only [readEvOf, model.Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at Hcr
  obtain ⟨rfl, -⟩ := Hcr
  iexists p, w, g
  isimp
  iframe
  ipureintro
  exact Hpr

theorem reqChanP_write (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (c : Loc) :
    reqChanP γ ρ k "write" c ⊢
      reqElem γ ρ k src.gryffproto.Write.ty writeEvOf (fun g => g.ClientId') c := by
  unfold reqChanP
  unfold reqAt
  simp only [String.reduceEq, ↓reduceIte]
  iintro ⟨%p, %w, %e, %cid, %rid, %i, Hc, Hreq, Hw, Htok, %He⟩
  icases Hreq with ⟨%g, Hp, %Hg⟩
  subst Hg
  obtain ⟨Hcr, Hpr⟩ := He
  simp only [writeEvOf, model.Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at Hcr
  obtain ⟨rfl, -⟩ := Hcr
  iexists p, w, g
  isimp
  iframe
  ipureintro
  exact Hpr

theorem reqChanP_rmw (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (c : Loc) :
    reqChanP γ ρ k "rmw" c ⊢
      reqElem γ ρ k src.gryffproto.RMW.ty rmwEvOf (fun g => g.ClientId') c := by
  unfold reqChanP
  unfold reqAt
  simp only [String.reduceEq, ↓reduceIte]
  iintro ⟨%p, %w, %e, %cid, %rid, %i, Hc, Hreq, Hw, Htok, %He⟩
  icases Hreq with ⟨%g, Hp, %Hg⟩
  subst Hg
  obtain ⟨Hcr, Hpr⟩ := He
  simp only [rmwEvOf, model.Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at Hcr
  obtain ⟨rfl, -⟩ := Hcr
  iexists p, w, g
  isimp
  iframe
  ipureintro
  exact Hpr

/-- The recovery trigger's guard: the element's lower bound is below `crtInstance[q]`. -/
theorem recover_guard (q i : w32) (s : RState) (qf : Fin 3) (hqf : qf.val = (sint.Z q).toNat)
    (h0 : 0 ≤ sint.Z q)
    (Hle : (sint.Z i).toNat + 1 ≤ (sint.Z (s.crt (rid32 qf))).toNat) :
    sint.Z i < sint.Z (s.crt q) := by
  have hr : rid32 qf = q := by
    unfold rid32
    rw [hqf]
    have e : (((sint.Z q).toNat : Nat) : Int) = sint.Z q := Int.toNat_of_nonneg h0
    rw [e]
    word
  rw [hr] at Hle
  omega

set_option maxHeartbeats 16000000 in
theorem Loop_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h sc : Loc)
    (γsc : ChanNames)
    (h_read1 : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleRead1Proxied") (Val #p))
      (msgAt p (.read1 m)) (.msg (.read1 m)))
    (h_read2 : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleRead2Proxied") (Val #p))
      (msgAt p (.read2 m)) (.msg (.read2 m)))
    (h_write1 : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleWrite1Proxied") (Val #p))
      (msgAt p (.write1 m)) (.msg (.write1 m)))
    (h_write2 : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleWrite2Proxied") (Val #p))
      (msgAt p (.write2 m)) (.msg (.write2 m)))
    (h_read1Reply : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleRead1Reply") (Val #p))
      (msgAt p (.read1Reply m)) (.msg (.read1Reply m)))
    (h_read2Reply : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleRead2Reply") (Val #p))
      (msgAt p (.read2Reply m)) (.msg (.read2Reply m)))
    (h_write1Reply : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleWrite1Reply") (Val #p))
      (msgAt p (.write1Reply m)) (.msg (.write1Reply m)))
    (h_write2Reply : ∀ m p, stepSpecB γ ρ k r (App (repMB r go!"handleWrite2Reply") (Val #p))
      (msgAt p (.write2Reply m)) (.msg (.write2Reply m)))
    (h_prepare : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handlePrepare") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.prepare m)) (.msg (.prepare m)))
    (h_preAccept : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handlePreAccept") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.preAccept m)) (.msg (.preAccept m)))
    (h_accept : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handleAccept") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.accept m)) (.msg (.accept m)))
    (h_commit : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handleCommit") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.commit m)) (.msg (.commit m)))
    (h_prepareReply : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handlePrepareReply") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.prepareReply m)) (.msg (.prepareReply m)))
    (h_preAcceptReply : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handlePreAcceptReply") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.preAcceptReply m)) (.msg (.preAcceptReply m)))
    (h_preAcceptOK : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handlePreAcceptOK") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.preAcceptOK m)) (.msg (.preAcceptOK m)))
    (h_acceptReply : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handleAcceptReply") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.acceptReply m)) (.msg (.acceptReply m)))
    (h_executed : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"handleExecuted") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.executed m)) (.msg (.executed m)))
    (h_executeOverwrite : ∀ m p, stepSpecB γ ρ k r (App (epMB h go!"executeOverwrite") (Val #p))
      iprop(handlerOfB r h ∗ msgAt p (.executeOverwrite m)) (.msg (.executeOverwrite m)))
    (h_read : ∀ p w (g : src.gryffproto.Read), stepSpecB γ ρ k r (App (repMB r go!"handleRead") (Val #p))
      iprop(p ↦ g ∗ writerIs ρ g.ClientId' w) (readEvOf g))
    (h_write : ∀ p w (g : src.gryffproto.Write), stepSpecB γ ρ k r (App (repMB r go!"handleWrite") (Val #p))
      iprop(p ↦ g ∗ writerIs ρ g.ClientId' w) (writeEvOf g))
    (h_rmw : ∀ p w (g : src.gryffproto.RMW), stepSpecB γ ρ k r (App (epMB h go!"HandleRMW") (Val #p))
      iprop(handlerOfB r h ∗ p ↦ g ∗ writerIs ρ g.ClientId' w) (rmwEvOf g))
    (h_forceWrite : stepSpecB γ ρ k r (App (repMB r go!"handleForceWrite") (Val #())) iprop(True)
      .forceWrite)
    (h_recover : ∀ q i, stepSpecB γ ρ k r
      (App (App (epMB h go!"startRecoveryForInstance") (Val #q)) (Val #i)) (handlerOfB r h)
      (.recover q i)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        handlerOfB r h ∗ isChanBag γsc sc (fun _ : Bool => iprop(False)) ∗ loopTok γ ρ k r }}
      (App (epMB h go!"Loop") (Val #sc))
    {{ RET #(); loopTok γ ρ k r }} := by
  unfold epMB
  wp_start as ⟨#Hrep, #Hh, #Hsc, Htok⟩
  icases (isReplica_open γ ρ k r).1 $$ Hrep with
    ⟨%gR, %h', #Hexec, #HgR, #Hshut, #Hproxy, #HsctR, #Hbeacon, #Hdreply, #Hdur, #Hchans, #Hgen⟩
  icases (isExec_open γ ρ k r h').1 $$ Hexec with
    ⟨%gR', %mtx, %ex, %pr, #HgR', #Hh', #Hmtx, #Hpr, -, #HR, #Hex, #Hexr, #HId, #HN, #HgShut, #Hlock,
      #Heo, #Hrec, #Hinv, #Hpreds⟩
  iunfold bagAt at Heo Hrec
  icases Heo with ⟨%c_eo, #Hf_eo, #Hb_eo⟩
  icases Hrec with ⟨%c_rec, #Hf_rec, #Hb_rec⟩
  icombine Hh Hh' gives %Hhh
  have Hhh' : h' = h := by
    simp only [handlerIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
      true_and] at Hhh
    exact GoGlobalContext.intoVal_inj_loc Hhh.symm
  subst Hhh'
  icombine HgR HgR' gives %HgRR
  subst HgRR
  iunfold replicaChans at Hchans
  iunfold bagAt at Hchans
  icases Hchans with ⟨⟨%c_read1, #Hf_read1, #Hb_read1⟩, ⟨%c_read2, #Hf_read2, #Hb_read2⟩, ⟨%c_write1, #Hf_write1, #Hb_write1⟩, ⟨%c_write2, #Hf_write2, #Hb_write2⟩, ⟨%c_read1Reply, #Hf_read1Reply, #Hb_read1Reply⟩, ⟨%c_read2Reply, #Hf_read2Reply, #Hb_read2Reply⟩, ⟨%c_write1Reply, #Hf_write1Reply, #Hb_write1Reply⟩, ⟨%c_write2Reply, #Hf_write2Reply, #Hb_write2Reply⟩, ⟨%c_prepare, #Hf_prepare, #Hb_prepare⟩, ⟨%c_preAccept, #Hf_preAccept, #Hb_preAccept⟩, ⟨%c_accept, #Hf_accept, #Hb_accept⟩, ⟨%c_commit, #Hf_commit, #Hb_commit⟩, ⟨%c_prepareReply, #Hf_prepareReply, #Hb_prepareReply⟩, ⟨%c_preAcceptReply, #Hf_preAcceptReply, #Hb_preAcceptReply⟩, ⟨%c_preAcceptOK, #Hf_preAcceptOK, #Hb_preAcceptOK⟩, ⟨%c_acceptReply, #Hf_acceptReply, #Hb_acceptReply⟩, ⟨%c_executed, #Hf_executed, #Hb_executed⟩, ⟨%c_read, #Hf_read, #Hb_read⟩, ⟨%c_write, #Hf_write, #Hb_write⟩, ⟨%c_rmw, #Hf_rmw, #Hb_rmw⟩, ⟨%c_forceWrite, #Hf_forceWrite, #Hb_forceWrite⟩, ⟨%c_w1timeout, #Hf_w1timeout, #Hb_w1timeout⟩, ⟨%c_w2timeout, #Hf_w2timeout, #Hb_w2timeout⟩, ⟨%c_commitShort, #Hf_commitShort, #Hb_commitShort⟩, ⟨%c_tryPreAccept, #Hf_tryPreAccept, #Hb_tryPreAccept⟩, ⟨%c_tryPreAcceptReply, #Hf_tryPreAcceptReply, #Hb_tryPreAcceptReply⟩, ⟨%c_preAcceptOKReply, #Hf_preAcceptOKReply, #Hb_preAcceptOKReply⟩, ⟨%c_acceptOKReply, #Hf_acceptOKReply, #Hb_acceptOKReply⟩, ⟨%c_beacon, #Hf_beacon, #Hb_beacon⟩, ⟨%c_doneAdapting, #Hf_doneAdapting, #Hb_doneAdapting⟩, ⟨%c_onClientConnect, #Hf_onClientConnect, #Hb_onClientConnect⟩⟩
  ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
  · iapply replica.dlog_init_access; iPkgInit
  wp_auto_lc 2
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- slow
    iapply clause_bag
    iframe Hlc1 Hlc2 Hsc
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- beacon
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_beacon
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- doneAdapting
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_doneAdapting
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- read
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_read
    inext
    iintro %v Hel
    icases reqChanP_read γ ρ k v $$ Hel with ⟨%p, %w, %g, Hc, Hg, Hw, Hev, %Hprod⟩
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRead_proof γ k r p g pr t [] $$ [Hp Hg] as ⟨Hp, Hg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_req γ.proto k t (readEvOf g) (rfl) Hprod ⊤ (by simp) $$ [Ht Hev] with ⟨Ht, Hev, %Hok⟩
    · iframe; iframe #
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_read p w g _ _ s' outs Hs) $$ [Hown Hpo Hg Hw] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- write
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_write
    inext
    iintro %v Hel
    icases reqChanP_write γ ρ k v $$ Hel with ⟨%p, %w, %g, Hc, Hg, Hw, Hev, %Hprod⟩
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveWrite_proof γ k r p g pr t [] $$ [Hp Hg] as ⟨Hp, Hg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_req γ.proto k t (writeEvOf g) (rfl) Hprod ⊤ (by simp) $$ [Ht Hev] with ⟨Ht, Hev, %Hok⟩
    · iframe; iframe #
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_write p w g _ _ s' outs Hs) $$ [Hown Hpo Hg Hw] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- rmw
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_rmw
    inext
    iintro %v Hel
    icases reqChanP_rmw γ ρ k v $$ Hel with ⟨%p, %w, %g, Hc, Hg, Hw, Hev, %Hprod⟩
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRMW_proof γ k r p g pr t [] $$ [Hp Hg] as ⟨Hp, Hg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_req γ.proto k t (rmwEvOf g) (rfl) Hprod ⊤ (by simp) $$ [Ht Hev] with ⟨Ht, Hev, %Hok⟩
    · iframe; iframe #
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_rmw p w g _ _ s' outs Hs) $$ [Hown Hpo Hg Hw] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- write1
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_write1
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_write1 Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveWrite1_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.write1 mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_write1 mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- write2
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_write2
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_write2 Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveWrite2_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.write2 mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_write2 mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- read1
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_read1
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_read1 Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRead1_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.read1 mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_read1 mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- read2
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_read2
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_read2 Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRead2_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.read2 mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_read2 mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- write1Reply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_write1Reply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_write1Reply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveWrite1Reply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.write1Reply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_write1Reply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- w1timeout
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_w1timeout
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- w2timeout
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_w2timeout
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- write2Reply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_write2Reply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_write2Reply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveWrite2Reply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.write2Reply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_write2Reply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- read1Reply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_read1Reply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_read1Reply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRead1Reply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.read1Reply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_read1Reply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- read2Reply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_read2Reply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_read2Reply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRead2Reply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.read2Reply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_read2Reply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- forceWrite
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_forceWrite
    inext
    iintro %v -
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveForceWrite_proof γ k r pr t [] $$ [Hp] as ⟨Hp, -⟩
    · iframe; iframe #
    have Hok : ∃ s' o, model.stepR k (pure.stOf k t) .forceWrite = .ok (s', o) :=
      ⟨_, _, pure.stepR_forceWrite k _⟩
    ihave Hev : evTok γ.proto k .forceWrite $$ []
    · unfold evTok; simp only [Ev.clientReq]; itrivial
    iapply fupd_wp
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_forceWrite _ _ s' outs Hs) $$ [Hown Hpo] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- prepare
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_prepare
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_prepare Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolvePrepare_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, Hg, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.prepare mm) $$ [Hg]
    · unfold msgAt; iexists g; iframe; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.prepare mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_prepare mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- preAccept
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_preAccept
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_preAccept Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolvePreAccept_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, %sl, Hg, #Hsl, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.preAccept mm) $$ [Hg]
    · unfold msgAt; iexists g, sl; iframe; iframe #; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.preAccept mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_preAccept mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- accept
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_accept
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_accept Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveAccept_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, %sl, Hg, #Hsl, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.accept mm) $$ [Hg]
    · unfold msgAt; iexists g, sl; iframe; iframe #; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.accept mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_accept mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- commit
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_commit
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_commit Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveCommit_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, %sl, Hg, #Hsl, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.commit mm) $$ [Hg]
    · unfold msgAt; iexists g, sl; iframe; iframe #; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.commit mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_commit mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- commitShort
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_commitShort
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- prepareReply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_prepareReply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_prepareReply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolvePrepareReply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, %sl, Hg, #Hsl, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.prepareReply mm) $$ [Hg]
    · unfold msgAt; iexists g, sl; iframe; iframe #; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.prepareReply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_prepareReply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- preAcceptReply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_preAcceptReply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_preAcceptReply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolvePreAcceptReply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, Hg, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.preAcceptReply mm) $$ [Hg]
    · unfold msgAt; iexists g; iframe; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.preAcceptReply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_preAcceptReply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- preAcceptOK
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_preAcceptOK
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_preAcceptOK Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolvePreAcceptOK_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, Hg, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.preAcceptOK mm) $$ [Hg]
    · unfold msgAt; iexists g; iframe; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.preAcceptOK mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_preAcceptOK mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- acceptReply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_acceptReply
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_acceptReply Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveAcceptReply_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, Hg, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.acceptReply mm) $$ [Hg]
    · unfold msgAt; iexists g; iframe; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.acceptReply mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_acceptReply mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- tryPreAccept
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_tryPreAccept
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- tryPreAcceptReply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_tryPreAcceptReply
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- executed
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_executed
    inext
    iintro %v Hel
    iunfold msgChanP at Hel
    icases Hel with ⟨%p, %m, %Hkv, Hmsg, %k', %n, Hrx⟩
    obtain ⟨Hkd, Hv⟩ := Hkv
    obtain ⟨mm, rfl⟩ := msgKind_inv_executed Hkd
    subst Hv
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveExecuted_proof γ k r p mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iunfold msgAt at Hmsg
    icases Hmsg with ⟨%g, Hg, %Hgm⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    ihave Hmsg : msgAt p (.executed mm) $$ [Hg]
    · unfold msgAt; iexists g; iframe; ipureintro; exact Hgm
    iapply fupd_wp
    imod step_ok_msg γ.proto k k' t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.executed mm)) $$ [Hrx]
    · unfold evTok; iexists k', n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_executed mm p _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- preAcceptOKReply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_preAcceptOKReply
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- acceptOKReply
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_acceptOKReply
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- executeOverwrite
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_eo
    inext
    iintro %v Hel
    iunfold eoChanP at Hel
    icases Hel with ⟨%mm, Hmsg, %n, Hrx⟩
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveExecuteOverwrite_proof γ k r v mm pr t [] $$ [Hp Hmsg] as ⟨Hp, Hmsg⟩
    · iframe; iframe #
    iapply fupd_wp
    imod step_ok_msg γ.proto k k t n _ ⊤ (by simp) $$ [Ht Hrx] with ⟨Ht, Hrx, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.msg (.executeOverwrite mm)) $$ [Hrx]
    · unfold evTok; iexists k, n; iexact Hrx
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_executeOverwrite mm v _ _ s' outs Hs) $$ [Hown Hpo Hmsg] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- onClientConnect
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_onClientConnect
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2; isplit
  · -- recover
    iapply clause_bag
    iframe Hlc1 Hlc2 Hb_rec
    inext
    iintro %v Hel
    iunfold recoverChanP at Hel
    icases Hel with ⟨%q, %i, Hiid, %Hqi, %hq3, Hlb⟩
    wp_auto_lc 2
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hli⟩
    imod lock_boot_proof γ ρ k r pr $$ [Hli Htok] with ⟨Hlk, Htok⟩
    · iframe; iframe #
    icases Hlk with ⟨%t, %xs, Hlk⟩
    iunfold lockedAt at Hlk
    icases Hlk with ⟨Ht, Hp, Hown, Hpo, Hboot⟩
    wp_apply resolveRecover_proof γ k r q i pr t [] $$ [Hp] as ⟨Hp, -⟩
    · iframe; iframe #
    icases replicaOwnX_crtLb_le ρ k r xs (pure.stOf k t) ⟨(sint.Z q).toNat, by omega⟩
      ((sint.Z i).toNat + 1) $$ [Hown Hlb] with ⟨Hown, %Hle⟩
    · iframe
    have hc := recover_guard q i (pure.stOf k t) _ rfl
      (by have := Hqi.1; simp [model.rowOk] at this; omega) Hle
    iapply fupd_wp
    imod step_ok_recover γ.proto k t q i Hqi.1 Hqi.2 hc ⊤ (by simp) $$ [Ht] with ⟨Ht, %Hok⟩
    · iframe; iframe #
    ihave Hev : evTok γ.proto k (.recover q i) $$ []
    · unfold evTok; simp only [Ev.clientReq]; itrivial
    imod loop_step_open γ ρ k r pr t xs _ Hok $$
      [Hev Hlc1 Hlc2 Ht Hp Hown Hpo Hboot] with ⟨%s', %outs, %Hs, Hown, Hpo, Hclose⟩
    · iframe; iframe #
    imodintro
    try wp_auto
    wp_apply (h_recover q i _ _ s' outs Hs) $$ [Hown Hpo] as ⟨Hown, Hpo⟩
    · iframe; iframe #
    ihave Hlk := Hclose $$ Hown Hpo
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlk]
    · inext; unfold replicaLockInv; ileft; iexact Hlk
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_nil.2
  itrivial

end

end Perennial.gryff.unitB
