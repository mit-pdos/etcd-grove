/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2/Replica.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Stage 2's laws of a replica (statements; proofs in Prove): its trace prophecy (`pred_set` at
`NewReplica`, `replicaProph_resolve` at each `ResolveU64`), its step (`replica_step`: the
invariant moves with reality, linearizes what the new frontier passes, and gives the step's
output obligations), and its client listener's request tokens (`req_mint`).

**The prophecy** (D9, D13). The gryff package's initialization creates `p` with `proph p pvs`
(every node; the client node and the master drop it); a replica node's boot records its
prediction, the words of `pvs` (`wordsOf`: its longest prefix of `u64` literals; every resolution
is a `ResolveU64`, so the words are all the resolutions), under its node index `n` (`pred_set`:
`predIs γ n (wordsOf pvs)`), before it registers; the master's registration of node `n` as replica
id `k` sets `predIdIs γ k` to it (`pred_register`), and the registry's `Ready` answer gives all
three (`predsSet`) and `k`'s slot resources (`idSlotRes`: the trace's half at `[]`). `NewReplica`
then holds `replicaProph γ k p [] []` (`replicaProph_intro`). The lock invariant then holds,
between steps, `replicaProph γ k p t [] ∗ traceHalf γ k t` (and the heap's projection to
`stOf k t`). A handler resolves its event's words one at a time (`replicaProph_resolve`, after
each `ResolveU64`), reaching `replicaProph γ k p t (enc e)`, then takes the step.

**The step.** With the trace's half at `t`, the words of `e` resolved, the event's token
(`evTok`: a message's receive token, a request's token), all three predictions set (`predsSet`)
and `⌜stepR k (stOf k t) e = .ok (s', outs)⌝` (a pure conjunct of the precondition; from
`step_ok_msg`, `step_ok_req`, `step_ok_recover`, `step_ok_exec`, `stepR_forceWrite`), `replica_step` appends `(k, e)` to the history, fires the atomic updates of the
operations the new linearization adds (stage 1's `Proto/Fire.lean`; the pure layer's `lin_prefix`,
`lin_congr_proj`, `lin_replay`), and returns the trace's half at `t ++ [e]`, its lower bound (the
right to send the step's messages: `peerStream_send`, `streamLb_intro` + `recv_msg` for
self-messages), and an `opDone` for each client reply among `outs` (`lin_reply`).
-/
module

public import Dsverify.Proof.gryff.Proto2.Laws
public import Dsverify.Proof.gryff.Proto2.Wire
public import Dsverify.Proof.gryff.Proto.WireLaws
public import Perennial.Spec.github_com.goose_lang.primitive.ProphId__ResolveU64
public import Dsverify.Proof.gryff.Proto2P.Done

@[expose] public section

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto dsverify_lab.harness
open model kahn pure p2
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The words of a prophecy's values: its longest prefix of `u64` values (`#x`; Goose's `intoVal`
is abstract, injective on `w64`: unit I's hub request R-I-2 replaced the stage-2 draft's match on
`LitV (LitInt x)`, which `#x` need not be). -/
noncomputable def wordsOf [GooseExts] [GoGlobalContext] : List val → List w64
  | [] => []
  | v :: vs =>
    @dite _ (∃ x : w64, (#x : val) = v) (Classical.propDecidable _)
      (fun h => h.choose :: wordsOf vs) (fun _ => [])

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem wordsOf_cons (x : w64) (vs : List val) :
    wordsOf ((#x : val) :: vs) = x :: wordsOf vs := by
  have h : ∃ x' : w64, (#x' : val) = #x := ⟨x, rfl⟩
  rw [wordsOf, dif_pos h]
  congr 1
  exact GoGlobalContext.intoVal_inj_w64 h.choose_spec

/-- Replica id `k`'s prophecy `p` (the lock invariant's): its remaining values' words, after the
words of the trace `t` and the words `ws` of the event being resolved, are its prediction's rest. -/
def replicaProph (γ : ProtoNames) (k : Fin 3) (p : ProphId) (t : List Ev) (ws : List w64) :
    IProp GF :=
  iprop(∃ pvs : List val, proph p pvs ∗
    predIdIs γ k (((t.map evCodec.enc).flatten ++ ws) ++ wordsOf pvs))

/-- **A replica node's boot** (node index `n`, after the gryff package's initialization, which
created the prophecy `p`, and before `RegisterWithMaster`, D13): record the node's prediction,
the words of `pvs`, with the start's token `predTok γ n`. The prophecy is unchanged (nothing
resolved it yet). -/
theorem pred_set (γ : ProtoNames) (n : Nat) (p : ProphId) (pvs : List val) (E : CoPset)
    (hE : ↑gryffN ⊆ E) :
    gryffInv2 γ ∗ predTok γ n ∗ proph p pvs ⊢
      |={E}=> proph p pvs ∗ predIs γ n (wordsOf pvs) := by
  iintro ⟨#Hinv, Htok, Hp⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod HNP
  unfold predTok
  ihave %hNP := ghost_map_lookup $$ HNP Htok
  imod ghost_map_update (some (wordsOf pvs)) $$ HNP Htok with ⟨HNP, Hel⟩
  imod ghostMapElem_persist $$ Hel with #Hel
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists { S with NP := S.NP.insert n (some (wordsOf pvs)) }
    iframe
    ipureintro; exact facts_pred_set Hf hNP
  imodintro
  unfold predIs
  iframe Hp Hel

/-- **`NewReplica`'s prophecy** (replica id `k`, registered as node `n`'s id, D13): the node's
recorded prediction is replica id `k`'s (the registry's answer: `predIdIs γ k ws` with node `n`'s
`predIs γ n ws`), so the unresolved prophecy is the lock invariant's at the empty trace. -/
theorem replicaProph_intro (γ : ProtoNames) (k : Fin 3) (n : Nat) (p : ProphId) (pvs : List val)
    (ws : List w64) :
    proph p pvs ∗ predIs γ n (wordsOf pvs) ∗ predIs γ n ws ∗ predIdIs γ k ws ⊢
      replicaProph γ k p [] [] := by
  iintro ⟨Hp, #H1, #H2, #H3⟩
  icases predIs_agree (GF := GF) γ n (wordsOf pvs) ws $$ [H1 H2] with %Hws
  · iframe #
  subst Hws
  unfold replicaProph
  iexists pvs
  iframe Hp
  simp only [List.map_nil, List.flatten_nil, List.append_nil, List.nil_append]
  iexact H3

/-- The prediction, from the lock invariant's prophecy. -/
theorem replicaProph_predIs (γ : ProtoNames) (k : Fin 3) (p : ProphId) (t : List Ev)
    (ws : List w64) :
    replicaProph γ k p t ws ⊢ ∃ ws', predIdIs γ k ws' := by
  unfold replicaProph
  iintro ⟨%pvs, -, #H⟩
  iexists _
  iexact H

/-- **One `ResolveU64(x)`** of a handler's event words: open the prophecy, resolve
(`ProphId.wp_ResolveU64_ptr`: `pvs = #x :: pvs'`), close with `x` resolved. -/
theorem replicaProph_resolve (γ : ProtoNames) (k : Fin 3) (p : ProphId) (t : List Ev)
    (ws : List w64) :
    replicaProph γ k p t ws ⊢
      ∃ pvs : List val, proph p pvs ∗ ∀ (x : w64) (pvs' : List val),
        ⌜pvs = (#x : val) :: pvs'⌝ -∗ proph p pvs' -∗ replicaProph γ k p t (ws ++ [x]) := by
  unfold replicaProph
  iintro ⟨%pvs, Hp, #H⟩
  iexists pvs
  iframe Hp
  iintro %x %pvs' %h Hp'
  iexists pvs'
  iframe Hp'
  subst h
  rw [wordsOf_cons] at *
  have : (t.map evCodec.enc).flatten ++ (ws ++ [x]) ++ wordsOf pvs' =
      (t.map evCodec.enc).flatten ++ ws ++ x :: wordsOf pvs' := by simp
  rw [this]
  iexact H

/-- **The step** of replica id `k` on event `e` (the run loop's handlers, the executor's
`strongconnect`), under its lock, after resolving `e`'s words: the invariant moves to the trace
`t ++ [e]` (the history to `l1 ++ [(k, e)]`), the operations the new linearization adds are
linearized (their clients' atomic updates fired: two later credits, as stage 1's `store_update`).
Returned: the trace's half and lower bound at `t ++ [e]`, the prophecy at `t ++ [e]`, the step's
messages appended to `k`'s streams (to send in order: `peerStream_send`; to itself: `recv_msg`),
and the witness of each client reply's operation and output (to write to the client:
`clientReplyOk_intro`). -/
theorem replica_step (γ : ProtoNames) (k : Fin 3) (p : ProphId) (t : List Ev) (e : Ev)
    (s' : RState) (outs : List Out) (E : CoPset) (hE : E = ⊤) :
    ⌜stepR k (stOf k t) e = .ok (s', outs)⌝ ∗
        gryffInv2 γ ∗ predsSet γ ∗ traceHalf γ k t ∗ replicaProph γ k p t (evCodec.enc e) ∗
        evTok γ k e ∗ £ 2 ⊢
      |={E}=> traceHalf γ k (t ++ [e]) ∗ traceLb γ k (t ++ [e]) ∗
        replicaProph γ k p (t ++ [e]) [] ∗
        ⌜∀ q : Fin 3, streamOf k q (t ++ [e]) = streamOf k q t ++ sentToR q outs⌝ ∗
        [∗list] x ∈ extsIn outs, opDone γ x.keyZ x.out := by
  subst hE
  have hE1 : (↑gryffN : CoPset) ⊆ ⊤ := CoPset.subseteq_top
  iintro ⟨%hstep, #Hinv, #Hpreds, Htr, Hph, Htok, Hlc1, Hlc2⟩
  unfold predsSet
  icases Hpreds with ⟨%ws0, %ws1, %ws2, #Hp0, #Hp1, #Hp2⟩
  unfold replicaProph
  icases Hph with ⟨%pvs, Hpr, #Hpk⟩
  ihave #Hpk' := preds_get (GF := GF) γ ws0 ws1 ws2 k $$ [Hp0 Hp1 Hp2]
  · iframe Hp0 Hp1 Hp2
  ihave %hws := predIdIs_agree (GF := GF) γ k.val
    (((t.map evCodec.enc).flatten ++ evCodec.enc e) ++ wordsOf pvs) (ws3 ws0 ws1 ws2 k)
    $$ [Hpk Hpk']
  · iframe Hpk Hpk'
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE1
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Hreg; imod Ht0; imod Ht1; imod Ht2; imod Hhist; imod HP; imod Hlin; imod Hrx; imod Hreqs
  ihave %hP := preds_lookup (GF := GF) γ S.P ws0 ws1 ws2 $$ HP Hp0 Hp1 Hp2
  ihave Htr3 : traces3 (GF := GF) γ S.T $$ [Ht0 Ht1 Ht2]
  · unfold traces3; iframe Ht0 Ht1 Ht2
  imod traces3_update (GF := GF) γ S.T k t e $$ [Htr3 Htr] with ⟨%hTk, Htr3, Htr, #Htlb⟩
  · iframe Htr3 Htr
  subst hTk
  imod evTok_consume (GF := GF) γ S k e $$ [Hrx Hreqs Htok] with
    ⟨%rx', %reqs', %htok, Hrx, Hreqs⟩
  · iframe Hrx Hreqs Htok
  obtain ⟨l2', hout⟩ := step_pure Hf hP hws hstep htok
  generalize hS' : stepSt S k e rx' reqs' (frontVal (S.l1 ++ [(k, e)]) (S.l1 ++ [(k, e)]).length)
    (linEntries ((S.l1 ++ [(k, e)]) ++ l2') (S.l1 ++ [(k, e)]).length) = S' at hout
  obtain ⟨new, hlin', hrep, hnewreg⟩ := hout.grow
  have hnd : ((S.linL ++ new).map Prod.fst).Nodup := by rw [← hlin']; exact hout.facts.linNodup
  have hT' : S'.T = traceSnoc S.T k e := by rw [← hS']; rfl
  have hl1' : S'.l1 = S.l1 ++ [(k, e)] := by rw [← hS']; rfl
  imod monoListAuthOwn_update_app (GF := GF) [(k, e)] $$ Hhist with ⟨Hhist, #Hhlb⟩
  imod monoListAuthOwn_update_app (GF := GF) new $$ Hlin with ⟨Hlin, #Hllb⟩
  imod fire_new (GF := GF) γ S.info S.linL new S.σ S'.σ (⊤ \ ↑gryffN)
    rfl hrep hnewreg hnd $$ [Hreg Hres Hlc1 Hlc2] with ⟨Hreg, Hres⟩
  · iframe Hreg Hres Hlc1 Hlc2
  imod Hclose $$ [Hreg Htr3 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR Hcur
    Hrx Hreqs Hres] with -
  · inext
    iexists S'
    have hfacts := hout.facts
    rw [hT', hl1', hlin']
    rw [← hS'] at hfacts ⊢
    iunfold traces3 at Htr3
    icases Htr3 with ⟨H0, H1, H2⟩
    iframe
    ipureintro
    exact hfacts
  imodintro
  have hstr := hout.streams
  rw [hT', traceSnoc_self] at hstr
  iframe Htr Htlb
  isplitl [Hpr]
  · iexists pvs
    iframe Hpr
    have : (((S.T k ++ [e]).map evCodec.enc).flatten ++ []) ++ wordsOf pvs =
        ((S.T k).map evCodec.enc).flatten ++ evCodec.enc e ++ wordsOf pvs := by simp
    rw [this]
    iexact Hpk
  isplitr
  · ipureintro; exact hstr
  have hrepl := hout.replies
  rw [hlin', hl1'] at hrepl
  iapply opDone_all (GF := GF) γ (S.linL ++ new) (S.l1 ++ [(k, e)]) (extsIn outs) hnd hrepl
  unfold histLb
  iframe Hllb Hhlb

/-! ## Client requests -/

/-- **A client request's token** (replica id `k`'s client listener, after `clientReqsOk_elim`):
a registered request `req` of client id `hs` on its bound connection `conn`, above the
connection's counter `last`, gets its token at `k`; the connection's replica id is fixed at its
first request (`last < 0`: `placeRight_intro`'s `-1`) and shown afterwards. -/
theorem req_mint (γ : GryffNames GF) (k : Fin 3) (hs : w32) (conn : Nat) (last req : Int)
    (i : RegInput w64) (hlt : last < req) (h0 : 0 ≤ req) :
    □ protoInvs γ ∗ clientConnAt γ hs conn ∗ placeRight γ conn last ∗
        (⌜last < 0⌝ ∨ connRepIs γ.proto conn k) ∗ opReg γ.proto (sint.Z hs, req) i ⊢
      |={⊤}=> placeRight γ conn req ∗ connRepIs γ.proto conn k ∗
        reqTok γ.proto k (sint.Z hs, req) i := by
  unfold protoInvs
  iintro ⟨#⟨Hinv, HPinv⟩, #Hconn, Hpr, Hrep, Hreg⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact (fun x _ => CoPset.subseteq_top x ‹_›)
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg', Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Hplacers; imod Hconns; imod HcR; imod Hreqs; imod Hops
  iinv HPinv with Hp HPclose
  all_goals try exact placersN_sub_diff
  unfold placersInv
  icases Hp with ⟨%P, %D, >HPa, >HDa, >%hD, >HPm⟩
  ihave %hP := ghostMapAuth_agree (GF := GF) γ.proto.placers _ _ S.placers P $$ Hplacers HPa
  subst hP
  unfold clientConnAt placeRight opReg
  ihave %hconn := ghost_map_lookup $$ Hconns Hconn
  ihave %hpl := ghost_map_lookup $$ Hplacers Hpr
  icases Hreg with ⟨%nI, HnI, %hin⟩
  ihave %hinfo := ghost_map_lookup $$ Hops HnI
  ihave %hrep := connRep_lookup (GF := GF) γ.proto S.connRep conn k last $$ HcR Hrep
  obtain ⟨hnone, hrnone, hf'⟩ := facts_req_mint Hf hconn hpl hlt h0 hrep hinfo hin
  imod connRep_update (GF := GF) γ.proto S.connRep conn k last hrnone $$ [HcR Hrep]
    with ⟨HcR, #Hrk⟩
  · iframe HcR Hrep
  imod ghost_map_insert (sint.Z hs, req) (k.val, i) hnone $$ Hreqs with ⟨Hreqs, Htok⟩
  ihave Hfull := (ghostMapAuth_halves (GF := GF) γ.proto.placers S.placers).2
    $$ [Hplacers HPa]
  · iframe Hplacers HPa
  imod ghost_map_update req $$ Hfull Hpr with ⟨Hfull, Hpr⟩
  icases (ghostMapAuth_halves (GF := GF) γ.proto.placers (S.placers.insert conn req)).1
    $$ Hfull with ⟨Hplacers, HPa⟩
  imod HPclose $$ [HPa HDa HPm] with -
  · inext
    iexists S.placers.insert conn req, D
    iframe HPa HDa
    isplitr
    · ipureintro
      intro c
      by_cases hc : c = conn
      · subst hc; rw [hD c, hpl]; simp
      · simp [Ne.symm hc, hD c]
    icases (BigSepM.bigSepM_delete (Φ := fun c (_ : Int) => connFresh (Gg := G) c true)
      (show get? S.placers conn = some last from hpl)).1 $$ HPm with ⟨Hc, HPm⟩
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun c (_ : Int) => connFresh (Gg := G) c true)).2
    iframe Hc HPm
  imod Hclose $$ [Hreg' Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists { S with placers := S.placers.insert conn req, connRep := S.connRep.insert conn k.val, reqs := S.reqs.insert (sint.Z hs, req) (k.val, i) }
    iframe
    ipureintro; exact hf'
  imodintro
  unfold reqTok
  iframe Hpr Hrk Htok

end

end Perennial.gryff
