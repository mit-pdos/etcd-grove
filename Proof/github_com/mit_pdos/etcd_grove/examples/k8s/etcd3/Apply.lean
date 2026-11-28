/-
Lean-first (no Rocq counterpart).

The proof of `Apply(s, input)` (stage 6f, as linkvtxn's): `NewProph()` gives a prophecy of the
`ResolveU64`s at the end, the first of the output's error kind; the commit (`InvSteps.lean`) is
chosen by the input's kind and whether the prophecy says `EOther` (the call's effect unknown)
before the store is called:

- not `EOther`: a `Create`'s one-shot updates commit `lintest`'s update at the write's firing
  (`create_au`); a `Delete`'s or update's commit where the store hands the token of a call
  invariant holding `lintest`'s update (`rwCall`, `rw_au`); a `Get`'s at the first firing at the
  revision the client prophesies (`getCall`, `get_maker`), `Apply` taking the continuation after
  the reply (`getCall_take`); a list's likewise at its first page's (`listCall`, `list_maker`,
  later pages `list_makerP`, `listCall_take`). An `EOther` output contradicts the prophecy.
- `EOther`: commit now, a write pending (`write_err_commit`; the store's updates are its late
  effect, `pend_au1`, `pend_rw`), a read failed (`read_err_commit`, plain reads, `plainL` for a
  list); any other output contradicts the prophecy (`kStep_err`, `kStep_get_ne4`, `lOut_ans`).

The goroutine's `threadTok` (lent by `lintest`, needed by `call`) is curried into the continuation
(`Φt`), so the call invariants hold `linU … Φt` as before (stage 7e-4).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.objOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.call
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__putW
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchCommit
public import Perennial.Spec.sync.atomic.Int64__Add
public import Perennial.Proof.sync.atomic.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- An output of the plain value `z` is `z` with some `Raw`. -/
private theorem setRaw_of_plain {y z : Output} (h : plainOut y = z) : ∃ r, y = { z with Raw' := r } :=
  ⟨y.Raw', by rw [← h]⟩

/-- The continuation at an output is the continuation at any output of its plain value. -/
private theorem contAt_plain (g0 : HSt) (x : Input) (y z : Output) (Φ : val → IProp GF)
    (h : plainOut y = plainOut z) : contAt g0 x z Φ ⊢ contAt g0 x y Φ := by
  iintro HΦ %y' %hy' Hio
  ihave H := HΦ $$ %y' %(hy'.trans h) Hio
  iexact H

/-- `ansOk` reads the plain fields only. -/
private theorem ansOk_plain (c : StoreCfg GF DObj) (y : Output) : ansOk c y = ansOk c (plainOut y) := rfl

set_option hygiene false in
/-- `Apply`'s three `ResolveU64`s, the first with the output's error kind (`Hxs`). -/
local macro "resolve3" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
    p_ptr _ p xs _) $$ [p Hp] as %xs1 ⟨%Hxs, p, Hp⟩
  · iframe
  (try wp_auto)
  wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
    p_ptr _ p xs1 _) $$ [p Hp] as %xs2 ⟨-, p, Hp⟩
  · iframe
  (try wp_auto)
  wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
    p_ptr _ p xs2 _) $$ [p Hp] as %xs3 ⟨-, p, Hp⟩
  · iframe
  (try wp_auto)))

set_option hygiene false in
/-- (stage E of 7f-6) `tbl.done.Add(1)`: the counter in its invariant (`isCache`), any value. -/
local macro "done_add" : tactic => `(tactic| (
  (try wp_auto)
  ihave #Htbl2 := Htbl
  iunfold isCache at Htbl2
  icases Htbl2 with ⟨-, -, #Hd⟩
  wp_apply_core sync.atomic.Int64.wp_Add _ (W64 1) $$ [] [-]
  · iPkgInit
  iinv Hd with ⟨%v, >Hv⟩ Hclose
  all_goals (try (exact fun _ _ => CoPset.mem_full))
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑cacheDoneN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hclose2 with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  (try wp_auto)))

set_option hygiene false in
/-- `Apply`'s end: an answer with a name becomes the client's cached object (`cache.put`, its
`cachedObjOk` from `ansOk`), then the continuation. -/
local macro "cache_tail" : tactic => `(tactic| (
  by_cases hE : y.Err' = W64 0
  · rw [decide_eq_true hE]
    wp_auto
    by_cases hN : y.Name' = []
    · rw [hN]
      wp_auto
      done_add
      iapply (hfin y)
      iframe HΦc Htt
      iright; iexact Hraw
    · simp only [decide_eq_false hN, Bool.not_false]
      wp_auto
      iunfold ansOk at Hans
      isimp only [if_pos (show y.Err' = W64 0 ∧ y.Name' ≠ [] from ⟨hE, hN⟩), cachedOf] at Hans
      wp_apply (wp_objOf y) $$ []
      (try wp_auto)
      wp_apply (wp_put c tbl x.Client' (objOfL y)) $$ []
      · iframe #
      (try wp_auto)
      done_add
      iapply (hfin y)
      iframe HΦc Htt
      iright; iexact Hraw
  · rw [decide_eq_false hE]
    wp_auto
    done_add
    iapply (hfin y)
    iframe HΦc Htt
    iright; iexact Hraw))


set_option hygiene false in
/-- A list's end: its answer has no name (`lOut_name`), so nothing is cached. -/
local macro "list_tail" : tactic => `(tactic| (
  by_cases hE : y.Err' = W64 0
  · rw [decide_eq_true hE]
    wp_auto
    rw [hN]
    wp_auto
    done_add
    iapply (hfin y)
    iframe HΦc Htt
    iright; iexact Hraw
  · rw [decide_eq_false hE]
    wp_auto
    done_add
    iapply (hfin y)
    iframe HΦc Htt
    iright; iexact Hraw))

set_option maxHeartbeats 3200000 in
theorem Apply.wp_proof (wp_call : call.spec (GF := GF) (hG := hG))
    (wp_put : cache.put.spec (GF := GF) (hG := hG))
    (wp_objOf : objOf.spec (GF := GF) (hG := hG))
    (wp_runWatch : runWatch.spec (GF := GF) (hG := hG))
    (wp_putW : cache.putW.spec (GF := GF) (hG := hG)) :
    Apply.spec (GF := GF) (hG := hG) := by
  intro _ _ _ γ sp tbl c g0 γk hc hpfx hrp hdi hvi hAs hse htb hnr hg
  iintro #Hpkg #Hpe #Hst #Hinvs %hne #Htbl #Hrs #HinvK #Hsw #Hwl
  have hcd : CfgD c := ⟨by rw [hc]; rfl, by simp only [StoreCfg.pfx, hpfx, hrp]; rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 ∈ c.K.kvs := by
    cases h : c.K.kvs with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, List.mem_cons_self⟩
  ihave #Hinv := (BigSepL.bigSepL_mem (Φ := fun sv : KVNames => kInv γ c g0 sv) hs0)
    $$ Hinvs
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave ⟨%lD, %lU, #HD, #HU, -, -⟩ := drvInit_sents $$ Hi
  iintro %i
  imodintro
  iintro %Φ ⟨Hin, Htt⟩ HAU
  iunfold kInOk at Hin
  icases Hin with ⟨%x, %Hin, #Hca⟩
  obtain ⟨rfl, HgenA, hfl⟩ := Hin
  -- the continuation, with the goroutine's token curried (`lintest`'s post gives it back)
  obtain ⟨Φt, hΦt⟩ : ∃ Φt : val → IProp GF, Φt = fun v => iprop(threadTok -∗ Φ v) := ⟨_, rfl⟩
  -- (stage E of 7f-6) a watch's answer is never `EOther`, its resource version parses small
  have hrv5 : x.Kind' = W64 5 → ∀ n, parseRVD x.MinRV' = some n → uint.Z n < 2 ^ 63 := by
    intro h5 n hn
    rcases HgenA with hu | hw
    · exact absurd h5 (by rcases hu.2.1 with h | h | h | h | h <;> rw [h] <;> decide)
    · cases hs : x.Skip'
      · obtain ⟨-, -, -, n0, hn0, hb, -⟩ := hw.2.2.2 hs
        rw [hn0] at hn; cases hn; word
      · rw [hw.2.2.1 hs] at hn; cases hn; decide
  have hioOk : ∀ y : Output, (x.Kind' = W64 5 → y.Err' ≠ W64 4) →
      ((⌜x.Kind' = W64 5 ∨ plainOut y = otherL⌝ ∨ k8s_correctness.rawOk x y) ∗
        (⌜x.Kind' ≠ W64 5⌝ ∨ k8s_correctness.wrawOk g0.st.rv x y) : IProp GF) ⊢
        (k8setcd3S (GF := GF) g0).ioOk (boxIn x) (boxOut y) :=
    fun y hy => by
      simp only [k8setcd3S]
      iintro ⟨Hr, Hw⟩
      iexists x, y
      iframe Hr Hw
      ipureintro
      exact ⟨rfl, rfl, fun h => ⟨hy h, hrv5 h⟩, HgenA, hfl⟩
  have hfinW : ∀ y : Output, (x.Kind' = W64 5 → y.Err' ≠ W64 4) →
      contAt g0 x y Φt ∗ threadTok ∗
        (⌜x.Kind' = W64 5 ∨ plainOut y = otherL⌝ ∨ k8s_correctness.rawOk x y) ∗
        (⌜x.Kind' ≠ W64 5⌝ ∨ k8s_correctness.wrawOk g0.st.rv x y) ⊢ Φ #(boxOut y) := by
    intro y hy
    subst hΦt
    iintro ⟨HΦc, Htt, Hr, Hw⟩
    ihave HΦc := HΦc $$ %y %rfl [Hr Hw]
    · iapply hioOk y hy
      isplitl [Hr]
      · iexact Hr
      · iexact Hw
    iapply HΦc
    iexact Htt
  wp_func_call
  wp_call
  wp_auto_lc 2
  ihave HU : linU γ g0 (boxIn x) Φt $$ [HAU]
  · subst hΦt
    iunfold linU
    imod HAU with ⟨%S, HS, Hcl⟩
    imodintro
    iexists S
    iframe HS
    iintro %S' %o Hst
    imod Hcl $$ [Hst] with Hk
    · iexact Hst
    imodintro
    iintro %o' %heq Hio Htt
    iapply Hk
    iframe
    try (ipureintro; exact heq)
  wp_if_destruct
  · -- (stage E of 7f-6) a watcher's watch: `runWatch`, committed as the model's observation at
    -- the state at the commit (`watch_commit`), its last object the watcher's
    have hk5 := Hif
    have Hw : GenInW x := HgenA.resolve_left (fun h => by
      rcases h.2.1 with h | h | h | h | h <;> rw [h] at hk5 <;> exact absurd hk5 (by decide))
    obtain ⟨-, -, -, hw⟩ := Hw
    obtain ⟨k, hk⟩ : ∃ k, k = (k8s.prepareKeyM go!"/objs" x.WKey' x.Recursive').getD [] := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, n = (parseRVD x.MinRV').getD 0 := ⟨_, rfl⟩
    have hok : x.Skip' = false → prepareKeyM c.resourcePrefix x.WKey' x.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV x.MinRV' = some n ∧
        uint.Z n < 2 ^ 63 - 1 := by
      intro hs
      obtain ⟨-, hpk, hwl, n0, hn0, hn0b, -⟩ := hw hs
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.1 hpk
      have hkk : k = k0 := by rw [hk, hk0]; rfl
      have hnn : n = n0 := by rw [hn, hn0]; rfl
      subst hkk hnn
      refine ⟨by rw [hrp]; exact hk0, ?_, by rw [hc]; exact hn0, by word⟩
      have := prepareKeyM_length hk0
      rw [hpfx]; simp only [List.length_append]
      unfold opKeyMax; simp only [List.length_cons, List.length_nil] at *; omega
    ihave Hl0 := monoListLbOwn_nil (GF := GF) (A := List mvcc.Change) γ.ch
    imod Hl0 with #Hl0
    -- (k8s 7g) the read updates fire past the seeded revision `s0n`: the watch starts after the seeds
    obtain ⟨s0n, hs0n⟩ : ∃ s0n, s0n = uint.nat g0.st.rv := ⟨_, rfl⟩
    imod (kInv_lb_seed γ c g0 γk hg) $$ HinvK with ⟨%ls, #Hls, %hls⟩
    icases (threadTok_level0 (GF := GF)).1 $$ Htt with ⟨Hlt, Htt⟩
    wp_apply (wp_runWatch sp c γk x k n (fun lb σ => watchQ γ c (max lb s0n) σ) hc
      (fun lb σ => by
        iintro H
        ihave %h := watchQ_pure γ c _ σ $$ H
        ipureintro
        exact ⟨Nat.le_trans (Nat.le_max_left _ _) h.1, h.2⟩)
      (fun lb lb' σ σ' => watchQ_same γ c _ _ σ σ') hnr htb hok) $$ [$Hlt] as %y %o %ok ⟨Hlt, Hy⟩
    · iframe #
      isplitr
      · imodintro
        iapply watch_readAus γ c g0 γk ls (max 0 s0n) (by rw [Nat.zero_max, hs0n]; exact hls)
        iframe #
      imodintro
      iintro %lb %σ #HQ
      iunfold watchQ at HQ
      icases HQ with ⟨%Hq, #Hlb⟩
      imodintro
      have hrev : σ.rev ≤ σ.changes.length := by
        unfold KVState.rev; rw [Hq.2.2.2.2.2.2.1]; simp
      have hmax : max σ.rev s0n = σ.rev :=
        Nat.max_eq_left (Nat.le_trans (Nat.le_max_right lb s0n) Hq.1)
      rw [hmax]
      iapply watch_readAus γ c g0 γk σ.changes σ.rev hrev
      iframe #
    ihave Htt := (threadTok_level0 (GF := GF)).2 $$ [Hlt Htt]
    · iframe
    -- the commit: the answer is accepted at the state then
    have Hcommit : ∀ (l : List (List mvcc.Change)) (P : Prop),
        (∀ (σe : KVState) (cf : linkv.PCfg HSt Input), l <+: σe.changes → KHistI γ σe →
          kvWfHist c σe → KRelH cf.st σe → cf.st.hist.length = σe.rev →
          watchOkL x y cf.st = true) →
        (∀ (σe : KVState) (cf : linkv.PCfg HSt Input), l <+: σe.changes → KHistI γ σe →
          kvWfHist c σe → KRelH cf.st σe → cf.st.hist.length = σe.rev → P) → y.Err' ≠ W64 4 →
        kInv γ c g0 γk ∗ monoListLbOwn γ.ch l ∗ linU γ g0 (boxIn x) Φt ⊢
          |={⊤}=> contAt g0 x y Φt ∗ ⌜P⌝ := by
      intro l P hw' hP' hE
      iintro ⟨#Hi, #Hl, HU⟩
      iapply watch_commit γ c g0 γk x y hk5 hE l Φt P hw' hP'
      iframe Hi HU Hl
    icases Hy with (%Hy | ⟨%wes, %kes, %rs, %rsl, %Hy, #Hrs, Hseen⟩)
    · obtain ⟨rfl, rfl, -⟩ := Hy
      have hE : wFailedOut.Err' ≠ W64 4 := by
        unfold wFailedOut; rw [show (zero_val Output).Err' = W64 0 from rfl]; decide
      iapply fupd_wp
      imod (Hcommit [] True (fun _ cf _ _ _ _ _ => by unfold watchOkL; simp [wFailedOut])
        (fun _ _ _ _ _ _ _ => trivial) hE) $$ [HU] with ⟨HΦc, -⟩
      · iframe HinvK Hl0 HU
      imodintro
      (try wp_auto)
      iapply (hfinW _ (fun _ => hE))
      iframe HΦc Htt
      isplitr
      · ileft; ipureintro; exact Or.inl hk5
      · iright; iunfold k8s_correctness.wrawOk; ileft; ipureintro; exact Or.inr rfl
    · obtain ⟨hsk, rfl, hwr, hlo, hws, hlen⟩ := Hy
      have hE : (wEventsRawOut (encWEventsL wes) rsl).Err' ≠ W64 4 := by
        unfold wEventsRawOut wEventsOut; rw [show (zero_val Output).Err' = W64 0 from rfl]; decide
      obtain ⟨hlk, hpk, -, n0, hn0, -, hin, hb, h1⟩ := hw hsk
      have hnn : n = n0 := by rw [hn, hn0]; rfl
      subst hnn
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.1 hpk
      have hkk : k = k0 := by rw [hk, hk0]; rfl
      subst hkk
      iunfold kSeen at Hseen
      icases Hseen with (%Herr | ⟨%lb, %lb0, %st, %σ, %σ0, #HQ, #HQ0, %Hss⟩)
      · -- only Error events
        have hall : ∀ w ∈ wes, w.t = 4 := by
          intro w hw0
          obtain ⟨e, he, hr⟩ := forall₂_mem_right hws w hw0
          have : e.t = 4 := by
            refine Classical.byContradiction fun hne4 => ?_
            have : e ∈ kNonErr kes := List.mem_filter.2 ⟨he, by simpa using hne4⟩
            rw [Herr] at this; cases this
          rw [hr.1, this]
        have hokw : ∀ w ∈ wes, WEvOk w := by
          intro w hw0
          obtain ⟨e, he, hr⟩ := forall₂_mem_right hws w hw0
          exact wevOk_of_rel hr (by have := hall w hw0; rw [hr.1] at this; omega) (hlen w hw0)
        have hfromE : k8s_correctness.WatchFromL g0.st.rv x wes := by
          have hne : nonErr wes = [] := by rw [nonErr_rel hws, Herr]; rfl
          unfold k8s_correctness.WatchFromL
          rw [hne]
          split <;> intro e he <;> simp at he
        have hdec := decWEventsL_enc wes hokw
        iapply fupd_wp
        imod (Hcommit [] True (fun _ cf _ _ _ _ _ =>
            watchOkL_errs x _ cf.st wes n hn0 rfl hokw hall) (fun _ _ _ _ _ _ _ => trivial) hE)
          $$ [HU] with ⟨HΦc, -⟩
        · iframe HinvK Hl0 HU
        imodintro
        (try wp_auto)
        all_goals (try (wp_if_destruct))
        all_goals (try (wp_apply (wp_putW c tbl x.Client' o)))
        all_goals (try (iexact Htbl))
        all_goals (try wp_auto)
        all_goals
          iapply (hfinW _ (fun _ => hE))
          iframe HΦc Htt
          isplitr
          · ileft; ipureintro; exact Or.inl hk5
          iright; iunfold k8s_correctness.wrawOk; iright; iexists rs
          isplitr
          · iExactEq Hrs; rfl
          ipureintro
          exact ⟨by rw [← hwr]; exact hdec, by rw [← hwr]; exact hfromE⟩
      · -- a stream from the start firing's state, received at the read firing's
        iunfold watchQ at HQ HQ0
        icases HQ with ⟨%Hq, #Hlb⟩
        icases HQ0 with ⟨%Hq0, -⟩
        obtain ⟨hstart, hs⟩ := Hss
        have ht4 : ∀ e ∈ kes, e.t ≤ 4 := hs.1
        have hokw : ∀ w ∈ wes, WEvOk w := by
          intro w hw0
          obtain ⟨e, he, hr⟩ := forall₂_mem_right hws w hw0
          exact wevOk_of_rel hr (ht4 e he) (hlen w hw0)
        have hs' : kStreamOk driverCodec.dec (selD x) (predEmptyL x) c.S.zero
            (kInScope (go!"/registry" ++ k) x.Recursive') (kModeOf (sieOfL x) x.Bookmarks' n) σ st
            kes := by
          have e1 : c.S.dec = driverCodec.dec := hcd.1
          have e2 : kScopeOf c k x.Recursive' = kInScope (go!"/registry" ++ k) x.Recursive' := by
            unfold kScopeOf; rw [hpfx]
          rw [← e1, ← e2]; exact hs
        have hst : uint.nat g0.st.rv ≤ st := by
          have h0r : uint.nat g0.st.rv ≤ σ0.rev := hs0n ▸ Nat.le_trans (Nat.le_max_right _ s0n) Hq0.1
          have hreq : (kModeOf (sieOfL x) x.Bookmarks' n).req = uint.nat n := rfl
          unfold kStartOk at hstart
          rw [hreq] at hstart
          split at hstart
          · omega
          · split at hstart
            · rcases hfl n hn0 with h | h
              · subst h; simp at *
              · omega
            · omega
        have hdec := decWEventsL_enc wes hokw
        iapply fupd_wp
        imod (Hcommit σ.changes (k8s_correctness.WatchFromL g0.st.rv x wes)
            (fun σe cf hpre hkh hwh hrel hlen' => by
              obtain ⟨hsame, hle⟩ := sameHist_of_khist Hq.2.2.2.2.2.2 hkh hpre
              exact watchOkL_stream_commit x k n hk0 hlk hn0 hin hb h1.1 kes wes hws hokw c.S.zero
                σ σ0 σe st hsame hle Hq0.2.2.2.2.2.2.2.2.2 hstart hs' cf.st hrel hlen'
                (khistW_of c hcd γ σe hwh hkh))
            (fun σe cf hpre hkh hwh hrel hlen' => by
              obtain ⟨hsame, hle⟩ := sameHist_of_khist Hq.2.2.2.2.2.2 hkh hpre
              exact watchFromL_of_kStreamOk g0.st.rv x cf.st σe σ0 k n
                (kModeOf (sieOfL x) x.Bookmarks' n) (selD x) (predEmptyL x) c.S.zero st kes wes
                hrel hlen' (khistW_of c hcd γ σe hwh hkh) hk0 hlk (fun _ => rfl)
                (fun he o => selD_of_empty x he o) (kModeOk_of x n hb h1.1)
                Hq0.2.2.2.2.2.2.2.2.2 hstart (kStreamOk_hist hsame hle hs') hws hst) hE)
          $$ [HU] with ⟨HΦc, %hfromE⟩
        · iframe HinvK Hlb HU
        imodintro
        (try wp_auto)
        all_goals (try (wp_if_destruct))
        all_goals (try (wp_apply (wp_putW c tbl x.Client' o)))
        all_goals (try (iexact Htbl))
        all_goals (try wp_auto)
        all_goals
          iapply (hfinW _ (fun _ => hE))
          iframe HΦc Htt
          isplitr
          · ileft; ipureintro; exact Or.inl hk5
          iright; iunfold k8s_correctness.wrawOk; iright; iexists rs
          isplitr
          · iExactEq Hrs; rfl
          ipureintro
          exact ⟨by rw [← hwr]; exact hdec, by rw [← hwr]; exact hfromE⟩
  -- a unary client's operation
  have hk5 : ¬ x.Kind' = W64 5 := Hif
  have Hgen : GenIn x := HgenA.resolve_right (fun h => hk5 h.1)
  have hfin : ∀ y : Output, contAt g0 x y Φt ∗ threadTok ∗
      (⌜plainOut y = otherL⌝ ∨ k8s_correctness.rawOk x y) ⊢ Φ #(boxOut y) := by
    intro y
    iintro ⟨H1, H2, H3⟩
    iapply hfinW y (fun h => absurd h hk5)
    iframe H1 H2
    isplitl [H3]
    · icases H3 with (%h | #h)
      · ileft; ipureintro; exact Or.inr h
      · iright; iexact h
    · ileft; ipureintro; exact hk5
  obtain ⟨hx, hkey, hpp⟩ := genIn_ok x Hgen
  have hkey' : prepareKeyM c.resourcePrefix (storeKeyL x.Key') false = some (storeKeyL x.Key') := by
    rw [hrp]; exact hkey
  have hpp' : c.pathPrefix ++ storeKeyL x.Key' = mkeyL x.Key' := by rw [hpfx]; exact hpp
  wp_apply (linkv.wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph)
    as %p %xs Hp
  (try wp_auto)
  have hQp : ∀ (R m : w64) (σ : KVState), (fun _ _ => plainQ c) R m σ ⊢ (⌜kvWf c σ⌝ : IProp GF) :=
    fun _ _ σ => by iintro %h; ipureintro; exact h.1
  have hQL0 : ∀ (R : w64) (σ : KVState), (fun (_ : w64) σ => plainL (GF := GF) c γ σ) R σ ⊢
      ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ valsOk σ⌝ := fun _ σ => plainL_pure c γ σ
  have hQLP0 : ∀ (R : w64) (σ σ' : KVState), (fun (_ : w64) σ => plainL (GF := GF) c γ σ) R σ ∗
      listP σ σ' ⊢ ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝ := fun _ σ σ' => plainLP_pure c γ σ σ'
  by_cases Hok : xs.head? = some (W64 4)
  · -- the prophecy says `EOther`: commit now
    rcases Hgen.2.1 with h0 | h1 | h2 | h3 | h4
    · -- a `Create`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h0]; decide
      have h4k : ¬ x.Kind' = W64 4 := by rw [h0]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0 x hx Hgen.2.2.1 hw Φt) $$ [HU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv HU
      imodintro
      have hau := client.bigAndL_of_sep c.K.kvs (pendTok γ n x)
        (fun sv : KVNames => kInv γ c g0 sv)
        (fun sv : KVNames => k8sAu1 sv c (createStep x) (fun _ => iprop(True)))
        (fun sv _ => by
          iintro ⟨Ht, #Hi⟩
          iapply pend_au1 γ c hcd g0 sv (sentV lD) (sentV lU) n x h0
          iframe Ht Hi)
      ihave Hau := hau $$ [Htok]
      · iframe Htok Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Hau] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_pos h0]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, -, %Hy, -⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        done_add
        have hconv : contAt (GF := GF) g0 x otherL Φt ⊢
            contAt g0 x ⟨W64 4, [], 0, [], [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, r⟩ Φt :=
          contAt_plain g0 x _ otherL Φt rfl
        ihave HΦc := hconv $$ HΦc
        iapply (hfin _)
        iframe HΦc Htt
        ileft; ipureintro; rfl
      · rw [callOut, if_neg h4k] at Hy
        obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _ (Or.inl h0))
    · -- a `Delete`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h1]; decide
      have h4k : ¬ x.Kind' = W64 4 := by rw [h1]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0 x hx Hgen.2.2.1 hw Φt) $$ [HU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv HU
      imodintro
      have hstep : ∀ ks, delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject') ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]; rfl
      ihave Haus := (BigSepL.bigSepL_mono (l := c.K.kvs) (Φ := fun _ (sv : KVNames) => kInv γ c g0 sv)
          (Ψ := fun _ (sv : KVNames) => k8sAuRW sv c (delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject')) (pendTok γ n x) (fun _ => iprop(True)))
          (fun {_ sv} _ => pend_rw γ c hcd g0 sv (sentV lD) (sentV lU) n x _ hstep)) $$ Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (pendTok γ n x) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, -, %Hy, -⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        done_add
        have hconv : contAt (GF := GF) g0 x otherL Φt ⊢
            contAt g0 x ⟨W64 4, [], 0, [], [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, r⟩ Φt :=
          contAt_plain g0 x _ otherL Φt rfl
        ihave HΦc := hconv $$ HΦc
        iapply (hfin _)
        iframe HΦc Htt
        ileft; ipureintro; rfl
      · rw [callOut, if_neg h4k] at Hy
        obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _ (Or.inr (Or.inl h1)))
    · -- a `GuaranteedUpdate`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h2]; decide
      have h4k : ¬ x.Kind' = W64 4 := by rw [h2]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0 x hx Hgen.2.2.1 hw Φt) $$ [HU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv HU
      imodintro
      have hstep : ∀ ks, updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x) ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]; rfl
      ihave Haus := (BigSepL.bigSepL_mono (l := c.K.kvs) (Φ := fun _ (sv : KVNames) => kInv γ c g0 sv)
          (Ψ := fun _ (sv : KVNames) => k8sAuRW sv c (updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x)) (pendTok γ n x) (fun _ => iprop(True)))
          (fun {_ sv} _ => pend_rw γ c hcd g0 sv (sentV lD) (sentV lU) n x _ hstep)) $$ Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (pendTok γ n x) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, -, %Hy, -⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        done_add
        have hconv : contAt (GF := GF) g0 x otherL Φt ⊢
            contAt g0 x ⟨W64 4, [], 0, [], [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, r⟩ Φt :=
          contAt_plain g0 x _ otherL Φt rfl
        ihave HΦc := hconv $$ HΦc
        iapply (hfin _)
        iframe HΦc Htt
        ileft; ipureintro; rfl
      · rw [callOut, if_neg h4k] at Hy
        obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _ (Or.inr (Or.inr (Or.inl h2))))
    · -- a `Get`: committed now, failed
      have hk : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
        rw [h3]; decide
      have hk0 : ¬ x.Kind' = W64 0 := fun h => hk (Or.inl h)
      have hk1 : ¬ x.Kind' = W64 1 := fun h => hk (Or.inr (Or.inl h))
      have hk2 : ¬ x.Kind' = W64 2 := fun h => hk (Or.inr (Or.inr h))
      have h4k : ¬ x.Kind' = W64 4 := by rw [h3]; decide
      have hw : isWriteL x = false := by simp only [isWriteL, h3]; decide
      iapply fupd_wp
      imod (read_err_commit γ c g0 s0 x hw hk5 Φt) $$ [HU] with HΦc
      · iframe Hinv HU
      imodintro
      ihave Hmk := plain_maker γ c g0 c.K.kvs $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Hmk] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg hk0, if_neg hk1, if_neg hk2]
        iexact Hmk
      icases Hy with (%Hy | ⟨%σ, -, %Hy, -⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        done_add
        have hconv : contAt (GF := GF) g0 x otherL Φt ⊢
            contAt g0 x ⟨W64 4, [], 0, [], [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, r⟩ Φt :=
          contAt_plain g0 x _ otherL Φt rfl
        ihave HΦc := hconv $$ HΦc
        iapply (hfin _)
        iframe HΦc Htt
        ileft; ipureintro; rfl
      · rw [callOut, if_neg h4k] at Hy
        obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        -- a `Get` never answers `EOther` (above the state's revision it answers `ETooLarge`)
        exact absurd Hok (kStep_get_ne4 _ _ x _ h3)
    · -- a list: committed now, failed
      have hw : isWriteL x = false := by simp only [isWriteL, h4]; decide
      iapply fupd_wp
      imod (read_err_commit γ c g0 s0 x hw hk5 Φt) $$ [HU] with HΦc
      · iframe Hinv HU
      imodintro
      ihave HmkQ := plainL_maker γ c g0 c.K.kvs $$ [Hinvs]
      · iexact Hinvs
      ihave #HmkP := plainL_makerP γ c g0 c.K.kvs $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt HmkQ] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_pos h4]
        iunfold listPre
        iframe HmkQ HmkP
      icases Hy with (%Hy | ⟨%σ, -, %Hy, -⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        done_add
        have hconv : contAt (GF := GF) g0 x otherL Φt ⊢
            contAt g0 x ⟨W64 4, [], 0, [], [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, r⟩ Φt :=
          contAt_plain g0 x _ otherL Φt rfl
        ihave HΦc := hconv $$ HΦc
        iapply (hfin _)
        iframe HΦc Htt
        ileft; ipureintro; rfl
      · rw [callOut, if_pos h4] at Hy
        obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        -- a list never answers `EOther`
        have h := lOut_ans x σ hx h4
        simp [ansOf, Hok] at h
  · -- the prophecy says the call answers
    rcases Hgen.2.1 with h0 | h1 | h2 | h3 | h4
    · -- a `Create`: committed at the write's firing
      have h4k : ¬ x.Kind' = W64 4 := by rw [h0]; decide
      have hau := client.bigAndL_of_sep c.K.kvs (linU γ g0 (boxIn x) Φt)
        (fun sv : KVNames => kInv γ c g0 sv)
        (fun sv : KVNames => k8sAu1 sv c (createStep x)
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2)))
        (fun sv _ => by
          iintro ⟨HU', #Hi⟩
          iapply create_au γ c hcd g0 sv (sentV lD) (sentV lU) x hx Hgen.2.2.1 h0 Φt
          iframe HU' Hi)
      ihave Hau := hau $$ [HU]
      · iframe Hinvs HU
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True)
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Hau] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_pos h0]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy, #Hraw⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HΦc
        iunfold callAt at HΦc
        isimp only [if_pos (Or.inl h0)] at HΦc
        rw [callOut, if_neg h4k] at Hy
        resolve3
        icases HΦc with ⟨HΦc, #Hans⟩
        ihave HΦc := contAt_plain g0 x y _ Φt (by rw [Hy, kStep_plain]) $$ HΦc
        ihave #Hans : ansOk c y $$ [Hans]
        · rw [ansOk_plain c y, Hy]; iexact Hans
        cache_tail
    · -- a `Delete`: committed where the store hands the call's token
      have h4k : ¬ x.Kind' = W64 4 := by rw [h1]; decide
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod inv_alloc callN ⊤ iprop((linU γ g0 (boxIn x) Φt ∗ £ 1) ∨
          dghostVar γt (DFrac.own 1) ()) $$ [HU Hlc1] with #Hci
      · inext
        ileft
        iframe Hlc1 HU
      ihave #Hc : rwCall γ g0 γt x Φt $$ []
      · iunfold rwCall; iexact Hci
      have hstep : ∀ ks, delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject') ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]; rfl
      ihave Haus := (BigSepL.bigSepL_impl (l := c.K.kvs) (Φ := fun _ (sv : KVNames) => kInv γ c g0 sv)
          (Ψ := fun _ (sv : KVNames) => k8sAuRW sv c (delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject')) (dghostVar γt (DFrac.own 1) ())
            (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2)))) $$ Hinvs
      ihave Haus := Haus $$ []
      · imodintro
        iintro %k %sv %_ #Hi
        iapply rw_au γ c hcd g0 sv (sentV lD) (sentV lU) x hx Hgen.2.2.1 (Or.inl h1) _ hstep γt Φt
        iframe Hi Hc
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (dghostVar γt (DFrac.own 1) ())
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy, #Hraw⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HΦc
        iunfold callAt at HΦc
        isimp only [if_pos (Or.inr (Or.inl h1))] at HΦc
        rw [callOut, if_neg h4k] at Hy
        resolve3
        icases HΦc with ⟨HΦc, #Hans⟩
        ihave HΦc := contAt_plain g0 x y _ Φt (by rw [Hy, kStep_plain]) $$ HΦc
        ihave #Hans : ansOk c y $$ [Hans]
        · rw [ansOk_plain c y, Hy]; iexact Hans
        cache_tail
    · -- a `GuaranteedUpdate`: committed where the store hands the call's token
      have h4k : ¬ x.Kind' = W64 4 := by rw [h2]; decide
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod inv_alloc callN ⊤ iprop((linU γ g0 (boxIn x) Φt ∗ £ 1) ∨
          dghostVar γt (DFrac.own 1) ()) $$ [HU Hlc1] with #Hci
      · inext
        ileft
        iframe Hlc1 HU
      ihave #Hc : rwCall γ g0 γt x Φt $$ []
      · iunfold rwCall; iexact Hci
      have hstep : ∀ ks, updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x) ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]; rfl
      ihave Haus := (BigSepL.bigSepL_impl (l := c.K.kvs) (Φ := fun _ (sv : KVNames) => kInv γ c g0 sv)
          (Ψ := fun _ (sv : KVNames) => k8sAuRW sv c (updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x)) (dghostVar γt (DFrac.own 1) ())
            (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2)))) $$ Hinvs
      ihave Haus := Haus $$ []
      · imodintro
        iintro %k %sv %_ #Hi
        iapply rw_au γ c hcd g0 sv (sentV lD) (sentV lU) x hx Hgen.2.2.1 (Or.inr h2) _ hstep γt Φt
        iframe Hi Hc
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (dghostVar γt (DFrac.own 1) ())
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy, #Hraw⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HΦc
        iunfold callAt at HΦc
        isimp only [if_pos (Or.inr (Or.inr h2))] at HΦc
        rw [callOut, if_neg h4k] at Hy
        resolve3
        icases HΦc with ⟨HΦc, #Hans⟩
        ihave HΦc := contAt_plain g0 x y _ Φt (by rw [Hy, kStep_plain]) $$ HΦc
        ihave #Hans : ansOk c y $$ [Hans]
        · rw [ansOk_plain c y, Hy]; iexact Hans
        cache_tail
    · -- a `Get`: committed at the first firing at the prophesied revision
      have hk : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
        rw [h3]; decide
      have hk0 : ¬ x.Kind' = W64 0 := fun h => hk (Or.inl h)
      have hk1 : ¬ x.Kind' = W64 1 := fun h => hk (Or.inr (Or.inl h))
      have hk2 : ¬ x.Kind' = W64 2 := fun h => hk (Or.inr (Or.inr h))
      have h4k : ¬ x.Kind' = W64 4 := by rw [h3]; decide
      imod dghostVar_alloc (GF := GF) (none : Option KVState) with ⟨%γc, Hγc⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod dghostVar_alloc (GF := GF) (none : Option w64) with ⟨%γp, Hγp⟩
      imod inv_alloc callN ⊤ iprop(
          (linU γ g0 (boxIn x) Φt ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
          (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
            dghostVar γp DFrac.discard (some R) ∗ ⌜σ.rev = uint.nat R⌝ ∗
            ghostMapElem γ.r σ.rev DFrac.discard σ ∗
            ((contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2) ∨ dghostVar γt (DFrac.own 1) ())))
          $$ [HU Hlc1 Hγc] with #Hci
      · inext
        ileft
        iframe Hlc1 Hγc HU
      ihave #Hc : getCall γ c g0 (sentV lD) (sentV lU) γc γt γp x Φt $$ []
      · iunfold getCall; iexact Hci
      ihave Hmk := get_maker γ c hcd g0 c.K.kvs (sentV lD) (sentV lU) γc γt γp x hx Hgen.2.2.1 h3 Φt $$ [Hγp]
      · iframe Hinvs Hc Hγp
      have hQr : ∀ (R m : w64) (σ : KVState),
          (fun (R : w64) (_ : w64) σ => readQ c γc R σ) R m σ ⊢ (⌜kvWf c σ⌝ : IProp GF) := by
        intro R m σ
        unfold readQ
        iintro ⟨%h, -⟩
        ipureintro; exact h.1
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun R _ σ => readQ c γc R σ) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse
          htb hnr hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQr hQL0 hQLP0) $$ [Htt Hmk] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg hk0, if_neg hk1, if_neg hk2]
        iexact Hmk
      icases Hy with (%Hy | ⟨%σ, HQc, %Hy, #Hraw⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HQc
        iunfold callAt at HQc
        isimp only [if_neg hk] at HQc
        icases HQc with #HQc
        iunfold readQ at HQc
        icases HQc with ⟨%Hwr, #Hbit⟩
        have hrev : σ.rev = uint.nat (W64 (σ.rev : Int)) := by
          have := Hwr.2
          simp only [W64, uint.nat, BitVec.toNat_ofInt]
          omega
        rw [callOut, if_neg h4k] at Hy
        resolve3
        ihave #Hv := Hbit $$ %hrev
        iapply fupd_wp
        imod (getCall_take γ c g0 (sentV lD) (sentV lU) γc γt γp x Φt σ) $$ [Htok Hlc2] with HΦc
        · iframe Hc Hv Htok Hlc2
        imodintro
        icases HΦc with ⟨HΦc, #Hans⟩
        ihave HΦc := contAt_plain g0 x y _ Φt (by rw [Hy, kStep_plain]) $$ HΦc
        ihave #Hans : ansOk c y $$ [Hans]
        · rw [ansOk_plain c y, Hy]; iexact Hans
        cache_tail
    · -- a list: committed at its first page's first firing where it may (`listCommitOk`: an
      -- `ETooLarge` answer if the prophecy says so, else the prophesied revision)
      generalize htl : decide (xs.head? = some (W64 6)) = tl
      imod dghostVar_alloc (GF := GF) (none : Option KVState) with ⟨%γc, Hγc⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod dghostVar_alloc (GF := GF) (none : Option w64) with ⟨%γp, Hγp⟩
      imod inv_alloc callN ⊤ iprop(
          (linU γ g0 (boxIn x) Φt ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
          (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
            dghostVar γp DFrac.discard (some R) ∗ ⌜listCommitOk x tl R σ⌝ ∗
            ghostMapElem γ.r σ.rev DFrac.discard σ ∗
            (contAt g0 x (lOut x σ) Φt ∨ dghostVar γt (DFrac.own 1) ())))
          $$ [HU Hlc1 Hγc] with #Hci
      · inext
        ileft
        iframe Hlc1 Hγc HU
      ihave #Hc : listCall γ g0 γc γt γp x tl Φt $$ []
      · iunfold listCall; iexact Hci
      ihave HmkQ := list_maker γ c g0 c.K.kvs γc γt γp x tl hx h4 Φt $$ [Hγp]
      · iframe Hinvs Hc Hγp
      ihave #HmkP := list_makerP γ c g0 c.K.kvs γc x tl $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (listQ c γ γc x tl) listP hc hrp hdi hvi hAs hse htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2.1 hQp (fun R σ => listQ_pure c γ γc x tl R σ)
          (fun R σ σ' => listQP_pure c γ γc x tl R σ σ')) $$ [Htt HmkQ] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_pos h4]
        iunfold listPre
        iframe HmkQ HmkP
      icases Hy with (%Hy | ⟨%σ, HQc, %Hy, #Hraw⟩)
      · obtain ⟨r, rfl⟩ := setRaw_of_plain Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_pos h4] at HQc
        icases HQc with ⟨%R, #HQc, %HRy⟩
        iunfold listQ at HQc
        icases HQc with ⟨%Hwr, -, #Hbit⟩
        have hrev : σ.rev = uint.nat (W64 (σ.rev : Int)) := by
          have := Hwr.2.2.2
          simp only [W64, uint.nat, BitVec.toNat_ofInt]
          omega
        rw [callOut, if_pos h4] at Hy
        have hN : y.Name' = [] := by
          rw [show y.Name' = (plainOut y).Name' from rfl, Hy]; exact lOut_name x σ
        resolve3
        have hcm : listCommitOk x tl R σ := by
          subst htl
          unfold listCommitOk
          by_cases h6 : xs.head? = some (W64 6)
          · simp only [h6, _root_.decide_true, ↓reduceIte]
            rw [Hxs] at h6
            simp only [List.head?_cons, Option.some.injEq] at h6
            exact lOut_tooLarge x σ hx h4 (by rw [← Hy]; exact h6)
          · simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
            rcases HRy with h | h
            · exact absurd (by
                rw [Hxs]; simp only [List.head?_cons]
                rw [show y.Err' = (plainOut y).Err' from rfl, h]; rfl) h6
            · rw [h]; exact hrev
        ihave ⟨%σ0, #Hv, %Hs0⟩ := Hbit $$ %hcm
        iapply fupd_wp
        imod (listCall_take γ g0 γc γt γp x tl Φt σ0) $$ [Htok Hlc2] with HΦc
        · iframe Hc Hv Htok Hlc2
        imodintro
        ihave HΦc : contAt g0 x y Φt $$ [HΦc]
        · iapply (contAt_plain g0 x y (lOut x σ0) Φt
            (by rw [lOut_plain, Hy]; first | rw [Hs0] | rw [← Hs0]))
          iexact HΦc
        list_tail

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
