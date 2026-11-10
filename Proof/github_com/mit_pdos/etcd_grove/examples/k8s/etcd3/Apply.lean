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
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link

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
/-- `Apply`'s end: an answer with a name becomes the client's cached object (`cache.put`, its
`cachedObjOk` from `ansOk`), then the continuation. -/
local macro "cache_tail" : tactic => `(tactic| (
  by_cases hE : y.Err' = W64 0
  · rw [decide_eq_true hE]
    wp_auto
    by_cases hN : y.Name' = []
    · rw [hN]
      wp_auto
      iapply (hfin y)
      iframe HΦc Htt
    · simp only [decide_eq_false hN, Bool.not_false]
      wp_auto
      iunfold ansOk at Hans
      isimp only [if_pos (show y.Err' = W64 0 ∧ y.Name' ≠ [] from ⟨hE, hN⟩), cachedOf] at Hans
      wp_apply (wp_objOf y) $$ []
      (try wp_auto)
      wp_apply (wp_put c tbl x.Client' (objOfL y)) $$ []
      · iframe #
      (try wp_auto)
      iapply (hfin y)
      iframe HΦc Htt
  · rw [decide_eq_false hE]
    wp_auto
    iapply (hfin y)
    iframe HΦc Htt))


set_option hygiene false in
/-- A list's end: its answer has no name (`lOut_name`), so nothing is cached. -/
local macro "list_tail" : tactic => `(tactic| (
  by_cases hE : y.Err' = W64 0
  · rw [decide_eq_true hE]
    wp_auto
    rw [hN]
    wp_auto
    iapply (hfin y)
    iframe HΦc Htt
  · rw [decide_eq_false hE]
    wp_auto
    iapply (hfin y)
    iframe HΦc Htt))

set_option maxHeartbeats 3200000 in
theorem Apply.wp_proof (wp_call : call.spec (GF := GF) (hG := hG))
    (wp_put : cache.put.spec (GF := GF) (hG := hG))
    (wp_objOf : objOf.spec (GF := GF) (hG := hG)) :
    Apply.spec (GF := GF) (hG := hG) := by
  intro _ _ _ γ sp tbl c g0 hc hpfx hrp hdi hvi hAs hse hpl htb hnr
  iintro #Hpkg #Hpe #Hst #Hinvs %hne #Htbl #Hrs
  have hcd : CfgD c := ⟨by rw [hc]; rfl, by simp only [StoreCfg.pfx, hpfx, hrp]; rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 ∈ c.ms := by
    cases h : c.ms with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, List.mem_cons_self⟩
  ihave #Hinv := (BigSepL.bigSepL_mem (Φ := fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv) hs0)
    $$ Hinvs
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave ⟨%lD, %lU, #HD, #HU, -, -⟩ := drvInit_sents $$ Hi
  iintro %i
  imodintro
  iintro %Φ ⟨Hin, Htt⟩ HAU
  iunfold kInOk at Hin
  icases Hin with ⟨%x, %Hin, #Hca⟩
  obtain ⟨rfl, Hgen⟩ := Hin
  obtain ⟨hx, hkey, hpp⟩ := genIn_ok x Hgen
  have hkey' : prepareKeyM c.resourcePrefix (storeKeyL x.Key') false = some (storeKeyL x.Key') := by
    rw [hrp]; exact hkey
  have hpp' : c.pathPrefix ++ storeKeyL x.Key' = mkeyL x.Key' := by rw [hpfx]; exact hpp
  -- the continuation, with the goroutine's token curried (`lintest`'s post gives it back)
  obtain ⟨Φt, hΦt⟩ : ∃ Φt : val → IProp GF, Φt = fun v => iprop(threadTok -∗ Φ v) := ⟨_, rfl⟩
  have hioOk : ∀ y : Output, ⊢ (k8setcd3S (GF := GF) g0).ioOk (boxIn x) (boxOut y) :=
    fun y => by simp only [k8setcd3S]; ipureintro; exact ⟨x, y, rfl, rfl⟩
  have hfin : ∀ y : Output, contAt g0 x y Φt ∗ threadTok ⊢ Φ #(boxOut y) := by
    intro y
    subst hΦt
    iintro ⟨HΦc, Htt⟩
    ihave HΦc := HΦc $$ []
    · iapply hioOk
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
    iintro Hio Htt
    iapply Hk
    iframe
  wp_apply (linkv.wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph)
    as %p %xs Hp
  (try wp_auto)
  have hQp : ∀ (R m : w64) (σ : KVState), (fun _ _ => plainQ c) R m σ ⊢ (⌜kvWf c σ⌝ : IProp GF) :=
    fun _ _ σ => by iintro %h; ipureintro; exact h.1
  have hQL0 : ∀ (R : w64) (σ : KVState), (fun (_ : w64) σ => plainL (GF := GF) c γ σ) R σ ⊢
      ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝ := fun _ σ => plainL_pure c γ σ
  have hQLP0 : ∀ (R : w64) (σ σ' : KVState), (fun (_ : w64) σ => plainL (GF := GF) c γ σ) R σ ∗
      listP σ σ' ⊢ ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝ := fun _ σ σ' => plainLP_pure c γ σ σ'
  by_cases Hok : xs.head? = some (W64 4)
  · -- the prophecy says `EOther`: commit now
    rcases Hgen.2.1 with h0 | h1 | h2 | h3 | h4
    · -- a `Create`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h0]; decide
      have h4k : ¬ x.Kind' = W64 4 := by rw [h0]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0.γr.kv x hx hw Φt) $$ [HU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv HU
      imodintro
      have hau := client.bigAndL_of_sep c.ms (pendTok γ n x)
        (fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv)
        (fun sv : client.SrvAt GF => k8sAu1 sv.γr.kv c (createStep x) (fun _ => iprop(True)))
        (fun sv _ => by
          iintro ⟨Ht, #Hi⟩
          iapply pend_au1 γ c hcd g0 sv.γr.kv (sentV lD) (sentV lU) n x h0
          iframe Ht Hi)
      ihave Hau := hau $$ [Htok]
      · iframe Htok Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Hau] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_pos h0]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply (hfin _)
        iframe HΦc Htt
      · rw [callOut, if_neg h4k] at Hy
        subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _ (Or.inl h0))
    · -- a `Delete`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h1]; decide
      have h4k : ¬ x.Kind' = W64 4 := by rw [h1]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0.γr.kv x hx hw Φt) $$ [HU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv HU
      imodintro
      have hstep : ∀ ks, delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject') ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]; rfl
      ihave Haus := (BigSepL.bigSepL_mono (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject')) (pendTok γ n x) (fun _ => iprop(True)))
          (fun {_ sv} _ => pend_rw γ c hcd g0 sv.γr.kv (sentV lD) (sentV lU) n x _ hstep)) $$ Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (pendTok γ n x) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply (hfin _)
        iframe HΦc Htt
      · rw [callOut, if_neg h4k] at Hy
        subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _ (Or.inr (Or.inl h1)))
    · -- a `GuaranteedUpdate`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h2]; decide
      have h4k : ¬ x.Kind' = W64 4 := by rw [h2]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0.γr.kv x hx hw Φt) $$ [HU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv HU
      imodintro
      have hstep : ∀ ks, updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x) ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]; rfl
      ihave Haus := (BigSepL.bigSepL_mono (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x)) (pendTok γ n x) (fun _ => iprop(True)))
          (fun {_ sv} _ => pend_rw γ c hcd g0 sv.γr.kv (sentV lD) (sentV lU) n x _ hstep)) $$ Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (pendTok γ n x) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply (hfin _)
        iframe HΦc Htt
      · rw [callOut, if_neg h4k] at Hy
        subst Hy
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
      imod (read_err_commit γ c g0 s0.γr.kv x hw Φt) $$ [HU] with HΦc
      · iframe Hinv HU
      imodintro
      ihave Hmk := plain_maker γ c g0 c.ms $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Hmk] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg hk0, if_neg hk1, if_neg hk2]
        iexact Hmk
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply (hfin _)
        iframe HΦc Htt
      · rw [callOut, if_neg h4k] at Hy
        subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        -- a `Get` never answers `EOther` (above the state's revision it answers `ETooLarge`)
        exact absurd Hok (kStep_get_ne4 _ _ x _ h3)
    · -- a list: committed now, failed
      have hw : isWriteL x = false := by simp only [isWriteL, h4]; decide
      iapply fupd_wp
      imod (read_err_commit γ c g0 s0.γr.kv x hw Φt) $$ [HU] with HΦc
      · iframe Hinv HU
      imodintro
      ihave HmkQ := plainL_maker γ c g0 c.ms $$ [Hinvs]
      · iexact Hinvs
      ihave #HmkP := plainL_makerP γ c g0 c.ms $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt HmkQ] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_pos h4]
        iunfold listPre
        iframe HmkQ HmkP
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply (hfin _)
        iframe HΦc Htt
      · rw [callOut, if_pos h4] at Hy
        subst Hy
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
      have hau := client.bigAndL_of_sep c.ms (linU γ g0 (boxIn x) Φt)
        (fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv)
        (fun sv : client.SrvAt GF => k8sAu1 sv.γr.kv c (createStep x)
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2)))
        (fun sv _ => by
          iintro ⟨HU', #Hi⟩
          iapply create_au γ c hcd g0 sv.γr.kv (sentV lD) (sentV lU) x hx h0 Φt
          iframe HU' Hi)
      ihave Hau := hau $$ [HU]
      · iframe Hinvs HU
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True)
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Hau] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_pos h0]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HΦc
        iunfold callAt at HΦc
        isimp only [if_pos (Or.inl h0)] at HΦc
        rw [callOut, if_neg h4k] at Hy
        resolve3
        rw [← Hy]
        icases HΦc with ⟨HΦc, #Hans⟩
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
      ihave Haus := (BigSepL.bigSepL_impl (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (preD x) (rejD (sentV lD) x.HasReject' x.Reject')) (dghostVar γt (DFrac.own 1) ())
            (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2)))) $$ Hinvs
      ihave Haus := Haus $$ []
      · imodintro
        iintro %k %sv %_ #Hi
        iapply rw_au γ c hcd g0 sv.γr.kv (sentV lD) (sentV lU) x hx (Or.inl h1) _ hstep γt Φt
        iframe Hi Hc
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (dghostVar γt (DFrac.own 1) ())
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HΦc
        iunfold callAt at HΦc
        isimp only [if_pos (Or.inr (Or.inl h1))] at HΦc
        rw [callOut, if_neg h4k] at Hy
        resolve3
        rw [← Hy]
        icases HΦc with ⟨HΦc, #Hans⟩
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
      ihave Haus := (BigSepL.bigSepL_impl (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD (sentV lU) x)) (dghostVar γt (DFrac.own 1) ())
            (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2)))) $$ Hinvs
      ihave Haus := Haus $$ []
      · imodintro
        iintro %k %sv %_ #Hi
        iapply rw_au γ c hcd g0 sv.γr.kv (sentV lD) (sentV lU) x hx (Or.inr h2) _ hstep γt Φt
        iframe Hi Hc
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (dghostVar γt (DFrac.own 1) ())
          (fun σ => iprop(contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φt ∗ ansOk c (kStep (sentV lD) (sentV lU) x (c.abs σ)).2))
          (fun _ _ => plainQ c) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp hQL0 hQLP0) $$ [Htt Htok Haus] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · isimp only [if_neg h4k] at HΦc
        iunfold callAt at HΦc
        isimp only [if_pos (Or.inr (Or.inr h2))] at HΦc
        rw [callOut, if_neg h4k] at Hy
        resolve3
        rw [← Hy]
        icases HΦc with ⟨HΦc, #Hans⟩
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
      ihave Hmk := get_maker γ c hcd g0 c.ms (sentV lD) (sentV lU) γc γt γp x hx h3 Φt $$ [Hγp]
      · iframe Hinvs Hc Hγp
      have hQr : ∀ (R m : w64) (σ : KVState),
          (fun (R : w64) (_ : w64) σ => readQ c γc R σ) R m σ ⊢ (⌜kvWf c σ⌝ : IProp GF) := by
        intro R m σ
        unfold readQ
        iintro ⟨%h, -⟩
        ipureintro; exact h.1
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun R _ σ => readQ c γc R σ) (fun _ σ => plainL c γ σ) listP hc hrp hdi hvi hAs hse
          hpl htb hnr hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQr hQL0 hQLP0) $$ [Htt Hmk] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_neg h4k]
        iunfold callPre
        isimp only [if_neg hk0, if_neg hk1, if_neg hk2]
        iexact Hmk
      icases Hy with (%Hy | ⟨%σ, HQc, %Hy⟩)
      · subst Hy
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
        rw [← Hy]
        icases HΦc with ⟨HΦc, #Hans⟩
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
      ihave HmkQ := list_maker γ c g0 c.ms γc γt γp x tl hx h4 Φt $$ [Hγp]
      · iframe Hinvs Hc Hγp
      ihave #HmkP := list_makerP γ c g0 c.ms γc x tl $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) (listQ c γ γc x tl) listP hc hrp hdi hvi hAs hse hpl htb hnr
          hkey' hpp' hx Hgen.2.2.1 Hgen.2.2.2 hQp (fun R σ => listQ_pure c γ γc x tl R σ)
          (fun R σ σ' => listQP_pure c γ γc x tl R σ σ')) $$ [Htt HmkQ] as %y ⟨Htt, Hy⟩
      · iframe Htt
        iframe #
        isimp only [if_pos h4]
        iunfold listPre
        iframe HmkQ HmkP
      icases Hy with (%Hy | ⟨%σ, HQc, %Hy⟩)
      · subst Hy
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
        have hN : y.Name' = [] := by rw [Hy]; exact lOut_name x σ
        resolve3
        have hcm : listCommitOk x tl R σ := by
          subst htl
          unfold listCommitOk
          by_cases h6 : xs.head? = some (W64 6)
          · simp only [h6, decide_true, ↓reduceIte]
            rw [Hxs] at h6
            simp only [List.head?_cons, Option.some.injEq] at h6
            exact lOut_tooLarge x σ hx h4 (by rw [← Hy]; exact h6)
          · simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
            rcases HRy with h | h
            · exact absurd (by rw [Hxs, h]; rfl) h6
            · rw [h]; exact hrev
        ihave ⟨%σ0, #Hv, %Hs0⟩ := Hbit $$ %hcm
        iapply fupd_wp
        imod (listCall_take γ g0 γc γt γp x tl Φt σ0) $$ [Htok Hlc2] with HΦc
        · iframe Hc Hv Htok Hlc2
        imodintro
        ihave HΦc : contAt g0 x y Φt $$ [HΦc]
        · rw [Hy, ← Hs0]; iexact HΦc
        list_tail

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
