/-
**The watch API's predicates over the stream's history, and `wsRecv_ok.law`'s entailment**
(stage 2 of the mvcc API proof, the watch chain: `notes/mvcc-api-risk.md`, M1; 2026-11-04).
Lean-first (no Rocq counterpart).

A stream's API ghost names (`WsAbs`): its store's (`st`), its history (`ev`, a monotone list of
`Api/StreamLog.lean`'s events, the authority the channel invariant's), the count of its client's
events (`ns`, a monotone count: the authority whole in `wsState`, so that a receiver's lower bound
of the history, minted with a lower bound of the count, carries no client event the client has not
made), the consumer's view (`rcv`, half the client's `wsRecv`, half the channel invariant's; `rx`,
the client's exclusive count of it), and its channel.

- `logTok ι l dec`: a lower bound `l` of the history, well formed with the filters decoded by
  `dec` (each name's saved filters), and each send's lower bounds (`evTok`: the notified log, the
  compaction revision). Persistent; every lower bound of a well-formed history is one.
- `mvccStateI a σ`: the client's part of the store's API ghost state (half the view, half the
  pending revision, half the compaction authority, the whole notified-log authority, and `σ`
  reachable).
- `wsStateI ι S`: the client's count of its events, at a lower bound of the history whose replay is
  `S` (the lower bound minted at the client's last event).
- `wsRecvI ι rs`: the consumer's view at `rs`, a prefix of a lower bound's sends.
- `wsSentLbI ι n`: a lower bound with at least `n` sends.

`wsRecv_okI`: the four give `wsRecvOk σ S rs`, a plain entailment: the two lower bounds are
comparable (`mono_list_lb_valid`); if the receiver's is the longer, its extra events are sends
only (the count's lower bound against the client's authority), so its replay's stream state is
`S`; the filters agree by their saved names (`savedFilters_agree`, no later); each send's bounds
are below the client's state (its authorities).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamLog
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Ghost
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiGhost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc sent

/-- **A watch stream's API ghost names** (see the file header). -/
structure WsAbs where
  st : AbsNames
  ev : GName
  ns : GName
  rcv : GName
  rx : GName
  ch : GoChan
  chn : ChanNames

/-- A reachable state's compaction revision is at least `-1`. -/
theorem reach_crev : ∀ σ : MvccState, MvccReachable σ → -1 ≤ σ.crev := by
  intro σ h
  induction h with
  | start => simp [mvccStart]
  | notify σ pend _ _ _ ih => simpa [MvccState.notify] using ih
  | commit σ _ ih => simpa [MvccState.commitPending] using ih
  | compact σ r _ _ _ hr _ ih => simp [MvccState.compactTo]; omega

/-- A send's bounds below `N` and `c` (other events: nothing). -/
def sendLbs (N : Log) (c : Int) : SEv → Prop
  | .send _ _ _ _ L c0 _ _ => L <+: N ∧ c0 ≤ c
  | _ => True

theorem lbsOk_of_sendLbs (σ : MvccState) (dec : GName → List (EvM → Bool)) (l : List SEv)
    (h : ∀ e ∈ l, sendLbs σ.notifiedLog σ.crev e) : lbsOk σ (replay dec l).F := by
  revert h
  refine snoc_induction (P := fun l => (∀ e ∈ l, sendLbs σ.notifiedLog σ.crev e) →
    lbsOk σ (replay dec l).F) (fun _ f hf => by simp [replay, rStart] at hf) ?_ l
  intro l e ih h f hf
  have hl : ∀ e ∈ l, sendLbs σ.notifiedLog σ.crev e := fun e' he' => h e' (List.mem_append_left _ he')
  have he : sendLbs σ.notifiedLog σ.crev e := h e (List.mem_append_right _ (List.mem_singleton_self _))
  rw [replay_snoc] at hf
  cases e with
  | reg id rg fg lo => rw [step_reg] at hf; exact ih hl f hf
  | cancel id => rw [step_cancel] at hf; exact ih hl f hf
  | close => rw [step_close] at hf; exact ih hl f hf
  | send r fg rg lo L c0 cov dead =>
    rw [step_send] at hf
    rcases List.mem_append.1 hf with hf | hf
    · exact ih hl f hf
    · rw [List.mem_singleton] at hf; subst hf; exact he

section defs
variable {GF : BundledGFunctors} [AllG GF]

instance crevAtLeast_timeless (a : AbsNames) (c : Int) : Timeless (crevAtLeast (GF := GF) a c) := by
  unfold crevAtLeast; infer_instance

/-- What a send's event carries (persistent): its bounds, below the store's state when sent. -/
def evTok (a : AbsNames) : SEv → IProp GF
  | .send _ _ _ _ L c0 _ _ => iprop(nlLb a L ∗ crevAtLeast a c0)
  | _ => iprop(True)

instance evTok_persistent (a : AbsNames) (e : SEv) : Persistent (evTok (GF := GF) a e) := by
  cases e <;> unfold evTok <;> infer_instance
instance evTok_timeless (a : AbsNames) (e : SEv) : Timeless (evTok (GF := GF) a e) := by
  cases e with
  | send r fg rg lo L c0 cov dead =>
    show Timeless iprop(nlLb (GF := GF) a L ∗ crevAtLeast a c0); infer_instance
  | reg => show Timeless iprop(True); infer_instance
  | cancel => show Timeless iprop(True); infer_instance
  | close => show Timeless iprop(True); infer_instance

/-- **A well-formed lower bound of the stream's history** (persistent; see the file header). -/
def logTok (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool)) : IProp GF :=
  iprop(monoListLbOwn ι.ev l ∗ ⌜LogWF dec l⌝ ∗ ([∗list] fg ∈ fgsOf l, savedFilters fg (dec fg)) ∗
    [∗list] e ∈ l, evTok ι.st e)

instance logTok_persistent (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool)) :
    Persistent (logTok (GF := GF) ι l dec) := by
  unfold logTok; infer_instance

/-- **The store's state is `σ`**: the client's part of the store's API ghost state. -/
def mvccStateI (a : AbsNames) (σ : MvccState) : IProp GF :=
  iprop(absPart a (1 : Qp).half σ.log σ.crev ∗ pndPart a (1 : Qp).half σ.pending ∗
    crevAuth a (1 : Qp).half σ.crev ∗ nlAuth a 1 σ.notifiedLog ∗ ⌜MvccReachable σ⌝)

/-- **The stream's state is `S`.** -/
def wsStateI (ι : WsAbs) (S : StreamState) : IProp GF :=
  iprop(∃ (l : List SEv) (dec : GName → List (EvM → Bool)),
    monoNatAuthOwn ι.ns 1 (nsCount l) ∗ logTok ι l dec ∗ ⌜(replay dec l).S = S⌝)

/-- **The consumer has received `rs`.** -/
def wsRecvI (ι : WsAbs) (rs : List WResp) : IProp GF :=
  iprop(∃ (l : List SEv) (dec : GName → List (EvM → Bool)),
    ghostVar ι.rcv (1 : Qp).half rs ∗ monoNatAuthOwn ι.rx 1 rs.length ∗ logTok ι l dec ∗
    monoNatLbOwn ι.ns (nsCount l) ∗ ⌜rs <+: sendsOf l⌝)

/-- **The stream has sent at least `n` responses** (`0` from nothing). -/
def wsSentLbI (ι : WsAbs) (n : Nat) : IProp GF :=
  iprop(⌜n = 0⌝ ∨ ∃ l : List SEv, monoListLbOwn ι.ev l ∗ ⌜n ≤ (sendsOf l).length⌝)

instance wsSentLbI_persistent (ι : WsAbs) (n : Nat) : Persistent (wsSentLbI (GF := GF) ι n) := by
  unfold wsSentLbI; infer_instance

instance mvccStateI_timeless (a : AbsNames) (σ : MvccState) : Timeless (mvccStateI (GF := GF) a σ) := by
  unfold mvccStateI; infer_instance

instance savedFilters_timeless (γ : GName) (fs : List (EvM → Bool)) :
    Timeless (savedFilters (GF := GF) γ fs) := by
  unfold savedFilters savedAnythingOwn; infer_instance

instance logTok_timeless (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool)) :
    Timeless (logTok (GF := GF) ι l dec) := by
  unfold logTok; infer_instance

instance wsStateI_timeless (ι : WsAbs) (S : StreamState) : Timeless (wsStateI (GF := GF) ι S) := by
  unfold wsStateI; infer_instance

instance wsRecvI_timeless (ι : WsAbs) (rs : List WResp) : Timeless (wsRecvI (GF := GF) ι rs) := by
  unfold wsRecvI; infer_instance

/-! ## Exclusivity -/

theorem mvccStateI_excl (a : AbsNames) (σ σ' : MvccState) :
    mvccStateI (GF := GF) a σ ∗ mvccStateI a σ' ⊢ False := by
  unfold mvccStateI nlAuth
  iintro ⟨⟨-, -, -, H1, -⟩, ⟨-, -, -, H2, -⟩⟩
  iapply monoListAuthOwn_exclusive a.nl _ _ $$ H1 H2

theorem wsStateI_excl (ι : WsAbs) (S S' : StreamState) :
    wsStateI (GF := GF) ι S ∗ wsStateI ι S' ⊢ False := by
  unfold wsStateI
  iintro ⟨⟨%l, %d, H1, -⟩, ⟨%l', %d', H2, -⟩⟩
  iapply monoNatAuthOwn_exclusive ι.ns _ _ $$ H1 H2

theorem wsRecvI_excl (ι : WsAbs) (rs rs' : List WResp) :
    wsRecvI (GF := GF) ι rs ∗ wsRecvI ι rs' ⊢ False := by
  unfold wsRecvI
  iintro ⟨⟨%l, %d, -, H1, -⟩, ⟨%l', %d', -, H2, -⟩⟩
  iapply monoNatAuthOwn_exclusive ι.rx _ _ $$ H1 H2

theorem wsSentLbI_zero (ι : WsAbs) : ⊢ wsSentLbI (GF := GF) ι 0 := by
  unfold wsSentLbI; iintro; ileft; ipureintro; rfl

/-! ## The entailment -/

/-- A persistent big separating conjunction's element. -/
theorem sepL_get {A : Type} (Φ : A → IProp GF) [hΦ : ∀ x, Persistent (Φ x)] :
    ∀ l : List A, ([∗list] x ∈ l, Φ x) ⊢ □ ∀ x, ⌜x ∈ l⌝ -∗ Φ x
  | [] => by
    iintro -
    imodintro
    iintro %x %hx
    cases hx
  | y :: l => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#Hy, Hl⟩
    ihave #IH := sepL_get Φ l $$ Hl
    imodintro
    iintro %x %hx
    rcases List.mem_cons.1 hx with rfl | h
    · iexact Hy
    · iapply IH; ipureintro; exact h

/-- One send's bounds, from its token and the client's authorities. -/
theorem evTok_lbs (a : AbsNames) (σ : MvccState) (hr : MvccReachable σ) (e : SEv) :
    nlAuth (GF := GF) a 1 σ.notifiedLog ∗ crevAuth a (1 : Qp).half σ.crev ∗ evTok a e ⊢
      ⌜sendLbs σ.notifiedLog σ.crev e⌝ := by
  cases e with
  | send r fg rg lo L c0 cov dead =>
    unfold evTok
    iintro ⟨Hn, Hc, Hlb, Hca⟩
    ihave %h1 := nlLb_valid a 1 σ.notifiedLog L $$ [$Hn $Hlb]
    ihave %h2 := crevAtLeast_valid a _ σ.crev c0 (reach_crev σ hr) $$ [$Hc $Hca]
    ipureintro; exact ⟨h1, h2⟩
  | reg => iintro -; ipureintro; trivial
  | cancel => iintro -; ipureintro; trivial
  | close => iintro -; ipureintro; trivial

/-- The sends' bounds, from their tokens and the client's authorities. -/
theorem evToks_lbs (a : AbsNames) (σ : MvccState) (hr : MvccReachable σ) :
    ∀ l : List SEv, nlAuth (GF := GF) a 1 σ.notifiedLog ∗ crevAuth a (1 : Qp).half σ.crev ∗
      ([∗list] e ∈ l, evTok a e) ⊢ ⌜∀ e ∈ l, sendLbs σ.notifiedLog σ.crev e⌝
  | [] => by iintro -; ipureintro; intro e he; cases he
  | e :: l => by
    iintro ⟨Hn, Hc, #H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#He, #Hl⟩
    icases persistent_entails_right (evToks_lbs a σ hr l) $$ [$Hn $Hc $Hl] with ⟨%ih, ⟨Hn, Hc, -⟩⟩
    ihave %h := evTok_lbs a σ hr e $$ [$Hn $Hc $He]
    ipureintro
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | h'
    · exact h
    · exact ih e' h'

/-- Saved filters under the same names agree. -/
theorem savedFilters_agreeL (A B : List GName) (d d' : GName → List (EvM → Bool)) :
    ([∗list] fg ∈ A, savedFilters (GF := GF) fg (d fg)) ∗
      ([∗list] fg ∈ B, savedFilters fg (d' fg)) ⊢ ⌜∀ fg ∈ A, fg ∈ B → d fg = d' fg⌝ := by
  iintro ⟨HA, HB⟩
  ihave #GA := sepL_get (fun fg => savedFilters (GF := GF) fg (d fg)) A $$ HA
  ihave #GB := sepL_get (fun fg => savedFilters (GF := GF) fg (d' fg)) B $$ HB
  iapply pure_forall.2; iintro %fg
  iapply pure_forall.2; iintro %hA
  iapply pure_forall.2; iintro %hB
  ihave #S1 := GA $$ %fg %hA
  ihave #S2 := GB $$ %fg %hB
  iapply savedFilters_agree fg (d fg) (d' fg) $$ [$S1 $S2]

/-- **`wsRecv_ok.law`'s entailment** (see the file header): a plain entailment, no invariant
opened. -/
theorem wsRecv_okI (ι : WsAbs) (rs : List WResp) (S : StreamState) (σ : MvccState) :
    wsRecvI (GF := GF) ι rs ∗ wsStateI ι S ∗ mvccStateI ι.st σ ⊢ ⌜wsRecvOk σ S rs⌝ := by
  unfold wsRecvI wsStateI mvccStateI logTok
  iintro ⟨⟨%lr, %dr, -, -, ⟨#Hlbr, %Hwfr, #Hfr, #Her⟩, #Hnsr, %Hrs⟩,
          ⟨%lc, %dc, Hns, ⟨#Hlbc, %Hwfc, #Hfc, #Hec⟩, %HS⟩,
          ⟨-, -, Hc, Hn, %Hreach⟩⟩
  ihave %hcmp := mono_list_lb_valid ι.ev lr lc $$ Hlbr Hlbc
  ihave %hns := monoNatLbOwn_valid ι.ns 1 (nsCount lc) (nsCount lr) $$ Hns Hnsr
  ihave %hag := savedFilters_agreeL (fgsOf lc) (fgsOf lr) dc dr $$ [$Hfc $Hfr]
  rcases hcmp with hp | hp
  · -- the client's lower bound is the longer
    ihave %hlb := evToks_lbs ι.st σ Hreach lc $$ [$Hn $Hc $Hec]
    ipureintro
    rw [← HS]
    exact wsRecvOk_of_log σ dc lc rs Hwfc (lbsOk_of_sendLbs σ dc lc hlb)
      (Hrs.trans (sendsOf_prefix hp))
  · -- the receiver's is the longer: its extra events are sends only
    ihave %hlb := evToks_lbs ι.st σ Hreach lr $$ [$Hn $Hc $Her]
    ipureintro
    obtain ⟨t, rfl⟩ := hp
    have ht : nsCount t = 0 := by rw [nsCount_append] at hns; omega
    have hS : (replay dr (lc ++ t)).S = S := by
      rw [(replay_sends dr lc t ht).1, ← HS]
      rw [replay_congr dr dc lc (fun fg hfg =>
        (hag fg hfg (by rw [fgsOf_append]; exact List.mem_append_left _ hfg)).symm)]
    rw [← hS]
    exact wsRecvOk_of_log σ dr (lc ++ t) rs Hwfr (lbsOk_of_sendLbs σ dr _ hlb) Hrs

end defs

end api
end mvcc
end EtcdGrove
end Perennial
