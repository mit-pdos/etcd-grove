/-
**The API part of a stream's channel invariant and its steps** (stage 2 of the mvcc API proof,
the watch chain: `notes/mvcc-api-invariants.md`, "Hand-off: stage 2, the watch chain", item 1;
2026-11-05). Lean-first (no Rocq counterpart).

`chanApiAt ι l dec recv`: the history's authority at `l` (well formed, decoded by `dec`), its
filters' saved names and its sends' bounds, the channel invariant's half of the consumer's view
(`recv`, a prefix of the sends), and a lower bound of the client's event count. The channel
invariant (`watchChanInv`) is to hold it with its sent list projecting to `sendsOf l`.

The steps, each what a frozen contract's post needs of the stream's ghost state:
- `chanApi_alloc` (`NewWatchStream`): a new stream's names, `wsState ι wsStart`, `wsRecv ι []`;
- `chanApiAt_send` (every send): a send's event appended, its premises (`stepOk`) proved by the
  sender;
- `chanApiAt_reg` (`Watch`'s update): the registration at the exact sent count, the client's
  `wsState` moved to `S.register id ⟨rg, fs, lo, k, true⟩` with `wsSentLb ι k`;
- `chanApiAt_cancel` (`Cancel`'s update): `wsState ι (S.cancel id)`;
- `chanApiAt_recv` (a receive): `wsRecv ι (recv ++ [r])`, the receiver's lower bound minted;
- `chanApiAt_sentLb` (the non-blocking receive's empty case): `wsSentLb ι n` is at most the sends.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamGhost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc sent

/-! ## Well-formedness depends on the decoding only at the history's names -/

theorem sendFact_congr (dec dec' : GName → List (EvM → Bool)) (r : WResp) (fg : GName)
    (rg : WatchRange) (lo : Nat) (L : Log) (c0 : Int) (cov : List CovRec) (dead : List w64)
    (h : ∀ x ∈ (SEv.send r fg rg lo L c0 cov dead).fgs, dec x = dec' x) :
    sendFact dec r fg rg lo L c0 cov dead = sendFact dec' r fg rg lo L c0 cov dead := by
  have hcov : cov.map (fun c => (⟨c.1, c.2.1, dec c.2.2.1, c.2.2.2⟩ : CovEntry)) =
      cov.map (fun c => (⟨c.1, c.2.1, dec' c.2.2.1, c.2.2.2⟩ : CovEntry)) := by
    apply List.map_congr_left
    intro c hc
    rw [h c.2.2.1 (by simp only [SEv.fgs, List.mem_cons, List.mem_map]; exact Or.inr ⟨c, hc, rfl⟩)]
  simp only [sendFact, hcov, h fg (by simp [SEv.fgs])]

theorem stepOk_congr (dec dec' : GName → List (EvM → Bool)) (st : RState) (e : SEv)
    (h : ∀ x ∈ e.fgs, dec x = dec' x) : stepOk dec st e ↔ stepOk dec' st e := by
  cases e with
  | send r fg rg lo L c0 cov dead =>
    simp only [stepOk, sendFact_congr dec dec' r fg rg lo L c0 cov dead h]
  | reg => exact Iff.rfl
  | cancel => exact Iff.rfl
  | close => exact Iff.rfl

theorem LogWF_congr (dec dec' : GName → List (EvM → Bool)) (l : List SEv)
    (h : ∀ x ∈ fgsOf l, dec x = dec' x) (hwf : LogWF dec l) : LogWF dec' l := by
  intro p e hp
  have hmem : e ∈ l := List.mem_of_getElem? hp
  have hpre : l.take p <+: l := List.take_prefix p l
  rw [← replay_congr dec dec' (l.take p) (fun x hx => h x (fgsOf_prefix hpre x hx))]
  refine (stepOk_congr dec dec' _ e (fun x hx => h x ?_)).1 (hwf p e hp)
  simp only [fgsOf, List.mem_flatMap]; exact ⟨e, hmem, hx⟩

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- A big separating conjunction with pointwise equal summands. -/
theorem sepL_congr {A : Type} (Φ Ψ : A → IProp GF) :
    ∀ l : List A, (∀ x ∈ l, Φ x = Ψ x) → ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l, Ψ x
  | [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; itrivial
  | y :: l, h => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hy, Hl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hy]
    · rw [← h y (List.mem_cons_self ..)]; iexact Hy
    · iapply sepL_congr Φ Ψ l (fun x hx => h x (List.mem_cons_of_mem _ hx)) $$ Hl

/-- **The API part of a stream's channel invariant** (see the file header). -/
def chanApiAt (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool)) (recv : List WResp) :
    IProp GF :=
  iprop(monoListAuthOwn ι.ev 1 l ∗ ⌜LogWF dec l ∧ recv <+: sendsOf l⌝ ∗
    ([∗list] fg ∈ fgsOf l, savedFilters fg (dec fg)) ∗ ([∗list] e ∈ l, evTok ι.st e) ∗
    ghostVar ι.rcv (1 : Qp).half recv ∗ monoNatLbOwn ι.ns (nsCount l))

/-- A lower bound of the history, from the invariant. -/
theorem chanApiAt_tok (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) :
    chanApiAt (GF := GF) ι l dec recv ⊢ chanApiAt ι l dec recv ∗ logTok ι l dec := by
  unfold chanApiAt logTok
  iintro ⟨Ha, %hw, #Hf, #He, Hr, #Hn⟩
  ihave #Hlb := monoListLbOwn_get ι.ev 1 l $$ Ha
  iframe Ha Hr
  isplitr
  · iframe #; ipureintro; exact hw
  · iframe #; ipureintro; exact hw.1

/-- **A new stream** (`NewWatchStream`): its names, the channel invariant's part at the empty
history, the client's state at `wsStart` and its consumer's view at `[]`. -/
theorem chanApi_alloc (st : AbsNames) (ch : GoChan) (chn : ChanNames) :
    ⊢ |==> ∃ ι : WsAbs, ⌜ι.st = st ∧ ι.ch = ch ∧ ι.chn = chn⌝ ∗
      chanApiAt (GF := GF) ι [] (fun _ => []) [] ∗ wsStateI ι wsStart ∗ wsRecvI ι [] := by
  imod mono_list_own_alloc (GF := GF) ([] : List SEv) with ⟨%gev, Hev, #Hevlb⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gns, Hns, #Hnslb⟩
  imod ghostVar_alloc (GF := GF) ([] : List WResp) with ⟨%grcv, Hrcv⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%grx, Hrx, -⟩
  icases (ghostVar_split_half grcv (1 : Qp) ([] : List WResp)).1 $$ Hrcv with ⟨Hr1, Hr2⟩
  imodintro
  iexists ⟨st, gev, gns, grcv, grx, ch, chn⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  have hwf : LogWF (fun _ => []) ([] : List SEv) := fun p e hp => by simp at hp
  unfold chanApiAt wsStateI wsRecvI logTok
  isplitl [Hev Hr1]
  · iframe Hev Hr1
    isplitr
    · ipureintro; exact ⟨hwf, List.nil_prefix⟩
    simp only [fgsOf, List.flatMap_nil, nsCount]
    iframe Hnslb
    isplitl <;> (iapply BigSepL.bigSepL_nil.2; itrivial)
  isplitl [Hns]
  · iexists [], (fun _ => [])
    simp only [nsCount, fgsOf, List.flatMap_nil]
    iframe Hns Hevlb
    isplitr
    · isplitr
      · ipureintro; exact hwf
      isplitl <;> (iapply BigSepL.bigSepL_nil.2; itrivial)
    · ipureintro; rfl
  · iexists [], (fun _ => [])
    simp only [nsCount, fgsOf, List.flatMap_nil, List.length_nil]
    iframe Hr2 Hrx Hevlb Hnslb
    isplitr
    · isplitr
      · ipureintro; exact hwf
      isplitl <;> (iapply BigSepL.bigSepL_nil.2; itrivial)
    · ipureintro; exact List.nil_prefix

/-- **A send** (the channel invariant's step at every send): its event appended, the sender
having proved its premises and holding its filters' saved names and its bounds' tokens. -/
theorem chanApiAt_send (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (e : SEv) (hns : nsCount [e] = 0) (he : stepOk dec (replay dec l) e) :
    chanApiAt (GF := GF) ι l dec recv ∗ ([∗list] fg ∈ e.fgs, savedFilters fg (dec fg)) ∗
      evTok ι.st e ==∗ chanApiAt ι (l ++ [e]) dec recv := by
  unfold chanApiAt
  iintro ⟨⟨Ha, %hw, #Hf, #He, Hr, #Hn⟩, #Hef, #Het⟩
  imod monoListAuthOwn_update (l ++ [e]) (List.prefix_append l [e]) $$ Ha with ⟨Ha, -⟩
  imodintro
  iframe Ha Hr
  isplitr
  · ipureintro
    exact ⟨(LogWF_snoc dec l e).2 ⟨hw.1, he⟩, hw.2.trans (sendsOf_prefix (List.prefix_append _ _))⟩
  rw [fgsOf_append, nsCount_append, hns, Nat.add_zero]
  iframe Hn
  isplitl
  · iapply BigSepL.bigSepL_append.2
    iframe Hf
    simp only [fgsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    iexact Hef
  · iapply BigSepL.bigSepL_append.2
    iframe He
    iapply BigSepL.bigSepL_cons.2
    iframe Het
    iapply BigSepL.bigSepL_nil.2; itrivial

/-- The client's lower bound is the invariant's history up to sends, its state the replay's. -/
theorem chanApiAt_wsState (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (S : StreamState) :
    chanApiAt (GF := GF) ι l dec recv ∗ wsStateI ι S ⊢
      chanApiAt ι l dec recv ∗ monoNatAuthOwn ι.ns 1 (nsCount l) ∗ ⌜(replay dec l).S = S⌝ := by
  unfold chanApiAt wsStateI logTok
  iintro ⟨⟨Ha, %hw, #Hf, #He, Hr, #Hn⟩, ⟨%lc, %dc, Hns, ⟨#Hlbc, %Hwfc, #Hfc, #Hec⟩, %HS⟩⟩
  ihave %hpre := mono_list_auth_lb_valid ι.ev 1 l lc $$ Ha Hlbc
  ihave %hle := monoNatLbOwn_valid ι.ns 1 (nsCount lc) (nsCount l) $$ Hns Hn
  ihave %hag := savedFilters_agreeL (fgsOf lc) (fgsOf l) dc dec $$ [$Hfc $Hf]
  obtain ⟨-, t, hlt⟩ := hpre
  have ht : nsCount t = 0 := by rw [← hlt, nsCount_append] at hle; omega
  have hcnt : nsCount l = nsCount lc := by rw [← hlt, nsCount_append, ht, Nat.add_zero]
  have hS : (replay dec l).S = S := by
    rw [← hlt, (replay_sends dec lc t ht).1, ← HS]
    exact congrArg RState.S (replay_congr dec dc lc (fun x hx =>
      (hag x hx (by rw [← hlt, fgsOf_append]; exact List.mem_append_left _ hx)).symm))
  isplitl [Ha Hr]
  · iframe Ha Hr Hf He Hn; ipureintro; exact hw
  isplitl [Hns]
  · rw [hcnt]; iexact Hns
  · ipureintro; exact hS

/-- A client event appended: the history's authority, the client's count and the invariant's lower
bound of it, the client's new lower bound. -/
theorem chanApiAt_client (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (e : SEv) (hns : nsCount [e] = 1) (hwf : LogWF dec (l ++ [e]))
    (hrcv : recv <+: sendsOf l) :
    monoListAuthOwn (GF := GF) ι.ev 1 l ∗ monoNatAuthOwn ι.ns 1 (nsCount l) ∗
      ghostVar ι.rcv (1 : Qp).half recv ∗
      ([∗list] fg ∈ fgsOf (l ++ [e]), savedFilters fg (dec fg)) ∗
      ([∗list] e' ∈ l ++ [e], evTok ι.st e') ==∗
      chanApiAt ι (l ++ [e]) dec recv ∗ monoNatAuthOwn ι.ns 1 (nsCount (l ++ [e])) ∗
      logTok ι (l ++ [e]) dec := by
  iintro ⟨Ha, Hns, Hr, #Hf, #He⟩
  imod monoListAuthOwn_update (l ++ [e]) (List.prefix_append l [e]) $$ Ha with ⟨Ha, #Hlb⟩
  have hcnt : nsCount (l ++ [e]) = nsCount l + 1 := by rw [nsCount_append, hns]
  imod mono_nat_own_update (γ := ι.ns) (nsCount (l ++ [e])) (by omega) $$ Hns with ⟨Hns, #Hnlb⟩
  imodintro
  unfold chanApiAt logTok
  iframe Ha Hr Hns Hnlb Hlb
  isplitr
  · iframe #; ipureintro
    exact ⟨hwf, hrcv.trans (sendsOf_prefix (List.prefix_append _ _))⟩
  · iframe #; ipureintro; exact hwf

/-- **A registration** (`Watch`'s update): the watcher registered at the exact sent count, the
client's state moved, and the sent count's lower bound. -/
theorem chanApiAt_reg (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (S : StreamState) (id : w64) (rg : WatchRange) (fg : GName)
    (fs : List (EvM → Bool)) (lo : Nat) (hnone : S.ws !! id = none) (hneg : id ≠ W64 (-1)) :
    chanApiAt (GF := GF) ι l dec recv ∗ wsStateI ι S ∗ savedFilters fg fs ==∗
      ∃ dec' : GName → List (EvM → Bool), chanApiAt ι (l ++ [.reg id rg fg lo]) dec' recv ∗
        wsStateI ι (S.register id ⟨rg, fs, lo, (sendsOf l).length, true⟩) ∗
        wsSentLbI ι (sendsOf l).length := by
  iintro ⟨Hc, Hs, #Hfg⟩
  icases chanApiAt_wsState ι l dec recv S $$ [$Hc $Hs] with ⟨Hc, Hns, %HS⟩
  iunfold chanApiAt at Hc
  icases Hc with ⟨Ha, %hw, #Hf, #He, Hr, -⟩
  -- the new name's filters agree with the decoding wherever the history has it
  ihave #Gf := sepL_get (fun x => savedFilters (GF := GF) x (dec x)) (fgsOf l) $$ Hf
  ihave %hdec : ⌜fg ∈ fgsOf l → dec fg = fs⌝ $$ []
  · iapply pure_forall.2; iintro %hin
    ihave #H1 := Gf $$ %fg %hin
    iapply savedFilters_agree fg (dec fg) fs $$ [$H1 $Hfg]
  let dec' : GName → List (EvM → Bool) := fun x => if x = fg then fs else dec x
  have hagr : ∀ x ∈ fgsOf l, dec x = dec' x := by
    intro x hx
    by_cases hxe : x = fg
    · subst hxe; simp [dec', hdec hx]
    · simp [dec', hxe]
  have hw' : LogWF dec' l := LogWF_congr dec dec' l hagr hw.1
  have hrep : replay dec' l = replay dec l := (replay_congr dec dec' l hagr).symm
  have hwf : LogWF dec' (l ++ [.reg id rg fg lo]) := by
    refine (LogWF_snoc dec' l _).2 ⟨hw', ?_⟩
    show (replay dec' l).S.ws !! id = none ∧ id ≠ W64 (-1)
    rw [hrep, HS]; exact ⟨hnone, hneg⟩
  ihave #Hf' : [∗list] x ∈ fgsOf (l ++ [.reg id rg fg lo]), savedFilters (GF := GF) x (dec' x) $$ []
  · rw [fgsOf_append]
    iapply BigSepL.bigSepL_append.2
    isplitl
    · iapply sepL_congr (fun x => savedFilters (GF := GF) x (dec x))
        (fun x => savedFilters (GF := GF) x (dec' x)) (fgsOf l)
        (fun x hx => by simp only [hagr x hx]) $$ Hf
    · simp only [fgsOf, SEv.fgs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      iapply BigSepL.bigSepL_cons.2
      isplitl
      · simp only [dec', if_pos rfl]; iexact Hfg
      · iapply BigSepL.bigSepL_nil.2; itrivial
  ihave #He' : [∗list] e' ∈ l ++ [.reg id rg fg lo], evTok (GF := GF) ι.st e' $$ []
  · iapply BigSepL.bigSepL_append.2
    iframe He
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · unfold evTok; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  imod chanApiAt_client ι l dec' recv (.reg id rg fg lo) rfl hwf hw.2 $$ [$Ha $Hns $Hr $Hf' $He']
    with ⟨Hc, Hns, #Htok⟩
  imodintro
  iexists dec'
  iframe Hc
  isplitl [Hns]
  · unfold wsStateI
    iexists l ++ [.reg id rg fg lo], dec'
    iframe Hns Htok
    ipureintro
    rw [replay_snoc, step_reg, hrep, HS]
    simp only [dec', if_pos rfl]; rw [sendsOf_eq dec l, List.length_map]
  · unfold wsSentLbI logTok
    icases Htok with ⟨#Hlb, -⟩
    iright
    iexists l ++ [.reg id rg fg lo]
    iframe Hlb
    ipureintro
    rw [sendsOf_append]; simp

/-- **A cancel** (`Cancel`'s update at its first check): the client's state moved. -/
theorem chanApiAt_cancel (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (S : StreamState) (id : w64) :
    chanApiAt (GF := GF) ι l dec recv ∗ wsStateI ι S ==∗
      chanApiAt ι (l ++ [.cancel id]) dec recv ∗ wsStateI ι (S.cancel id) := by
  iintro ⟨Hc, Hs⟩
  icases chanApiAt_wsState ι l dec recv S $$ [$Hc $Hs] with ⟨Hc, Hns, %HS⟩
  iunfold chanApiAt at Hc
  icases Hc with ⟨Ha, %hw, #Hf, #He, Hr, -⟩
  have hwf : LogWF dec (l ++ [.cancel id]) := (LogWF_snoc dec l _).2 ⟨hw.1, trivial⟩
  ihave #Hf' : [∗list] x ∈ fgsOf (l ++ [.cancel id]), savedFilters (GF := GF) x (dec x) $$ []
  · rw [fgsOf_append]; simp only [fgsOf, SEv.fgs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    iexact Hf
  ihave #He' : [∗list] e' ∈ l ++ [.cancel id], evTok (GF := GF) ι.st e' $$ []
  · iapply BigSepL.bigSepL_append.2
    iframe He
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · unfold evTok; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  imod chanApiAt_client ι l dec recv (.cancel id) rfl hwf hw.2 $$ [$Ha $Hns $Hr $Hf' $He']
    with ⟨Hc, Hns, #Htok⟩
  imodintro
  iframe Hc
  unfold wsStateI
  iexists l ++ [.cancel id], dec
  iframe Hns Htok
  ipureintro
  rw [replay_snoc, step_cancel, HS]

/-- **A receive**: the next response sent received, the receiver's lower bound minted. -/
theorem chanApiAt_recv (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (r : WResp) (hnext : recv ++ [r] <+: sendsOf l) :
    chanApiAt (GF := GF) ι l dec recv ∗ wsRecvI ι recv ==∗
      chanApiAt ι l dec (recv ++ [r]) ∗ wsRecvI ι (recv ++ [r]) := by
  iintro ⟨Hc, Hw⟩
  icases chanApiAt_tok ι l dec recv $$ Hc with ⟨Hc, #Htok⟩
  iunfold chanApiAt at Hc
  icases Hc with ⟨Ha, %hw, #Hf, #He, Hr, #Hn⟩
  iunfold wsRecvI at Hw
  icases Hw with ⟨%l', %d', Hr', Hrx, -, -, -⟩
  imod ghostVar_update_2 (recv ++ [r]) ι.rcv recv (1 : Qp).half recv (1 : Qp).half
    (Qp.half_add_half 1) $$ Hr Hr' with ⟨Hr, Hr'⟩
  imod mono_nat_own_update (γ := ι.rx) (recv ++ [r]).length (by simp) $$ Hrx with ⟨Hrx, -⟩
  imodintro
  unfold chanApiAt wsRecvI
  iframe Ha Hr
  isplitr
  · iframe #; ipureintro; exact ⟨hw.1, hnext⟩
  · iexists l, dec
    iframe Hr' Hrx Htok Hn
    ipureintro; exact hnext

/-- **The non-blocking receive's empty case**: a lower bound of the sent count is at most the
sends of the history. -/
theorem chanApiAt_sentLb (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (n : Nat) :
    chanApiAt (GF := GF) ι l dec recv ∗ wsSentLbI ι n ⊢
      chanApiAt ι l dec recv ∗ ⌜n ≤ (sendsOf l).length⌝ := by
  unfold wsSentLbI
  iintro ⟨Hc, (%h0 | ⟨%l', #Hlb, %hn⟩)⟩
  · iframe Hc; ipureintro; omega
  · iunfold chanApiAt at Hc
    icases Hc with ⟨Ha, Hrest⟩
    ihave %hp := mono_list_auth_lb_valid ι.ev 1 l l' $$ Ha Hlb
    iunfold chanApiAt
    iframe Ha Hrest
    ipureintro
    exact Nat.le_trans hn (sendsOf_prefix hp.2).length_le

/-! ## The senders' tokens -/

/-- **The watcher `id` was registered in the stream's history with this info** (persistent): what a
sender of its responses holds, for `factAgree` (`replay_reg`). -/
def regTok (ι : WsAbs) (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) : IProp GF :=
  iprop(∃ l : List SEv, monoListLbOwn ι.ev l ∗ ⌜SEv.reg id rg fg lo ∈ l⌝)

instance regTok_persistent (ι : WsAbs) (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) :
    Persistent (regTok (GF := GF) ι id rg fg lo) := by
  unfold regTok; infer_instance

/-- **The registered watcher `id` was cancelled in the stream's history** (persistent): what a `-1`
response's sender holds of a watcher it does not cover (`deadIn`, `replay_cancel`). -/
def cancelTok (ι : WsAbs) (id : w64) : IProp GF :=
  iprop(∃ (l : List SEv) (rg : WatchRange) (fg : GName) (lo : Nat),
    monoListLbOwn ι.ev (l ++ [.cancel id]) ∗ ⌜SEv.reg id rg fg lo ∈ l⌝)

instance cancelTok_persistent (ι : WsAbs) (id : w64) : Persistent (cancelTok (GF := GF) ι id) := by
  unfold cancelTok; infer_instance

/-- A registration in the history gives its token. -/
theorem chanApiAt_regTok (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat)
    (hm : SEv.reg id rg fg lo ∈ l) :
    chanApiAt (GF := GF) ι l dec recv ⊢ chanApiAt ι l dec recv ∗ regTok ι id rg fg lo := by
  unfold chanApiAt regTok
  iintro ⟨Ha, Hr⟩
  ihave #Hlb := monoListLbOwn_get ι.ev 1 l $$ Ha
  iframe Ha Hr
  iexists l; iframe Hlb; ipureintro; exact hm

/-- A cancel after a registration in the history gives its token. -/
theorem chanApiAt_cancelTok (ι : WsAbs) (l1 l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat)
    (hp : l1 ++ [.cancel id] <+: l) (hm : SEv.reg id rg fg lo ∈ l1) :
    chanApiAt (GF := GF) ι l dec recv ⊢ chanApiAt ι l dec recv ∗ cancelTok ι id := by
  unfold chanApiAt cancelTok
  iintro ⟨Ha, Hr⟩
  ihave #Hlb := monoListLbOwn_get ι.ev 1 l $$ Ha
  ihave #Hlb' := monoListLbOwn_le (l1 ++ [.cancel id]) hp $$ Hlb
  iframe Ha Hr
  iexists l1, rg, fg, lo; iframe Hlb'; ipureintro; exact hm

/-- **A sender's registration token, at the history**: the replay has the watcher's info. -/
theorem chanApiAt_regAgree (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) :
    chanApiAt (GF := GF) ι l dec recv ∗ regTok ι id rg fg lo ⊢
      chanApiAt ι l dec recv ∗ ⌜regAgree (replay dec l).S id rg (dec fg) lo⌝ := by
  unfold chanApiAt regTok
  iintro ⟨⟨Ha, %hw, Hr⟩, %l', #Hlb, %hm⟩
  ihave %hp := mono_list_auth_lb_valid ι.ev 1 l l' $$ Ha Hlb
  iframe Ha Hr
  isplitr
  · ipureintro; exact hw
  ipureintro
  obtain ⟨t, rfl⟩ := hp.2
  exact replay_reg dec _ hw.1 id rg fg lo (List.mem_append_left _ hm)

/-- **A sender's cancel token, at the history**: the id is in the replay's cancelled set. -/
theorem chanApiAt_dead (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool))
    (recv : List WResp) (id : w64) :
    chanApiAt (GF := GF) ι l dec recv ∗ cancelTok ι id ⊢
      chanApiAt ι l dec recv ∗ ⌜id ∈ (replay dec l).D⌝ := by
  unfold chanApiAt cancelTok
  iintro ⟨⟨Ha, %hw, Hr⟩, %l1, %rg, %fg, %lo, #Hlb, %hm⟩
  ihave %hp := mono_list_auth_lb_valid ι.ev 1 l _ $$ Ha Hlb
  iframe Ha Hr
  isplitr
  · ipureintro; exact hw
  ipureintro
  exact replay_cancel dec l1 l hw.1 id rg fg lo hp.2 hm

end ghost

end api
end mvcc
end EtcdGrove
end Perennial
