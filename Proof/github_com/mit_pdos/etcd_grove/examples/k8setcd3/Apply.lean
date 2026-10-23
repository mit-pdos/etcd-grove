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
  the reply (`getCall_take`). An `EOther` output contradicts the prophecy.
- `EOther`: commit now, a write pending (`write_err_commit`; the store's updates are its late
  effect, `pend_au1`, `pend_rw`), a read failed (`read_err_commit`, plain reads); any other
  output contradicts the prophecy (`kStep_err`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.call
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Proph
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
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

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

set_option maxHeartbeats 3200000 in
theorem Apply.wp_proof (wp_call : call.spec (GF := GF) (hG := hG)) :
    Apply.spec (GF := GF) (hG := hG) := by
  intro _ _ _ γ sp c g0 hc hpfx hrp hAs
  iintro #Hpkg #Hpe #Hst #Hinvs %hne
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 ∈ c.ms := by
    cases h : c.ms with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, List.mem_cons_self⟩
  ihave #Hinv := (BigSepL.bigSepL_mem (Φ := fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv) hs0)
    $$ Hinvs
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, ⟨%lD, #HD, -⟩, ⟨%lU, #HU, -⟩⟩
  iintro %i
  imodintro
  iintro %Φ %Hin HAU
  obtain ⟨x, rfl, Hgen⟩ := Hin
  obtain ⟨hx, hkey, hpp⟩ := genIn_ok x Hgen
  have hkey' : prepareKeyM c.resourcePrefix (storeKeyL x.Key') false = some (storeKeyL x.Key') := by
    rw [hrp]; exact hkey
  have hpp' : c.pathPrefix ++ storeKeyL x.Key' = mkeyL x.Key' := by rw [hpfx]; exact hpp
  wp_func_call
  wp_call
  wp_auto_lc 2
  wp_apply (linkv.wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph)
    as %p %xs Hp
  (try wp_auto)
  have hQp : ∀ (R m : w64) (σ : KVState), (fun _ _ => plainQ c) R m σ ⊢ (⌜kvWf c σ⌝ : IProp GF) :=
    fun _ _ σ => by iintro %h; ipureintro; exact h.1
  have hioOk : ∀ y : Output, ⊢ (k8setcd3S (GF := GF) g0).ioOk (boxIn x) (boxOut y) :=
    fun y => by simp only [k8setcd3S]; ipureintro; exact ⟨x, y, rfl, rfl⟩
  by_cases Hok : xs.head? = some (W64 4)
  · -- the prophecy says `EOther`: commit now
    rcases Hgen.2 with h0 | h1 | h2 | h3
    · -- a `Create`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h0]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0.γr.kv x hx hw Φ) $$ [HAU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      have hau := client.bigAndL_of_sep c.ms (pendTok γ n x)
        (fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv)
        (fun sv : client.SrvAt GF => k8sAu1 sv.γr.kv c (createStep x) (fun _ => iprop(True)))
        (fun sv _ => by
          iintro ⟨Ht, #Hi⟩
          iapply pend_au1 γ c g0 sv.γr.kv (sentV lD) (sentV lU) n x h0
          iframe Ht Hi)
      ihave Hau := hau $$ [Htok]
      · iframe Htok Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Hau] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_pos h0]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply HΦc
        iapply hioOk
      · subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _)
    · -- a `Delete`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h1]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0.γr.kv x hx hw Φ) $$ [HAU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      have hstep : ∀ ks, delStep (mkeyL x.Key') (rejD (sentV lD) x.Reject') ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]; rfl
      ihave Haus := (BigSepL.bigSepL_mono (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (rejD (sentV lD) x.Reject')) (pendTok γ n x) (fun _ => iprop(True)))
          (fun {_ sv} _ => pend_rw γ c g0 sv.γr.kv (sentV lD) (sentV lU) n x _ hstep)) $$ Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (pendTok γ n x) (fun _ => iprop(True))
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Htok Haus] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply HΦc
        iapply hioOk
      · subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _)
    · -- a `GuaranteedUpdate`: committed now, pending; the store's firing is its late effect
      have hw : isWriteL x = true := by simp only [isWriteL, h2]; decide
      iapply fupd_wp
      imod (write_err_commit γ c g0 s0.γr.kv x hx hw Φ) $$ [HAU] with ⟨%n, HΦc, Htok⟩
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      have hstep : ∀ ks, updStep (mkeyL x.Key') dzero (updD (sentV lU) x) ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]; rfl
      ihave Haus := (BigSepL.bigSepL_mono (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (updStep (mkeyL x.Key') dzero (updD (sentV lU) x)) (pendTok γ n x) (fun _ => iprop(True)))
          (fun {_ sv} _ => pend_rw γ c g0 sv.γr.kv (sentV lD) (sentV lU) n x _ hstep)) $$ Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (pendTok γ n x) (fun _ => iprop(True))
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Htok Haus] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply HΦc
        iapply hioOk
      · subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _)
    · -- a `Get`: committed now, failed
      have hk : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
        rw [h3]; decide
      have hk0 : ¬ x.Kind' = W64 0 := fun h => hk (Or.inl h)
      have hk1 : ¬ x.Kind' = W64 1 := fun h => hk (Or.inr (Or.inl h))
      have hk2 : ¬ x.Kind' = W64 2 := fun h => hk (Or.inr (Or.inr h))
      have hw : isWriteL x = false := by simp only [isWriteL, h3]; decide
      iapply fupd_wp
      imod (read_err_commit γ c g0 s0.γr.kv x hw Φ) $$ [HAU] with HΦc
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      ihave Hmk := plain_maker γ c g0 c.ms $$ [Hinvs]
      · iexact Hinvs
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Hmk] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_neg hk0, if_neg hk1, if_neg hk2]
        iexact Hmk
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        resolve3
        iapply HΦc
        iapply hioOk
      · subst Hy
        resolve3
        rw [Hxs] at Hok
        simp only [List.head?_cons, Option.some.injEq] at Hok
        exact absurd Hok (kStep_err _ _ _ _)
  · -- the prophecy says the call answers
    rcases Hgen.2 with h0 | h1 | h2 | h3
    · -- a `Create`: committed at the write's firing
      have hau := client.bigAndL_of_sep c.ms (linU γ g0 (boxIn x) Φ)
        (fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv)
        (fun sv : client.SrvAt GF => k8sAu1 sv.γr.kv c (createStep x)
          (fun σ => contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ))
        (fun sv _ => by
          iintro ⟨HU', #Hi⟩
          iapply create_au γ c g0 sv.γr.kv (sentV lD) (sentV lU) x hx h0 Φ
          iframe HU' Hi)
      ihave Hau := hau $$ [HAU]
      · iframe Hinvs; iunfold linU; iexact HAU
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True)
          (fun σ => contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ)
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Hau] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_pos h0]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · iunfold callAt at HΦc
        isimp only [if_pos (Or.inl h0)] at HΦc
        resolve3
        rw [← Hy]
        iapply HΦc
        iapply hioOk
    · -- a `Delete`: committed where the store hands the call's token
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod inv_alloc callN ⊤ iprop((linU γ g0 (boxIn x) Φ ∗ £ 1) ∨
          dghostVar γt (DFrac.own 1) ()) $$ [HAU Hlc1] with #Hci
      · inext
        ileft
        iframe Hlc1
        iunfold linU
        iexact HAU
      ihave #Hc : rwCall γ g0 γt x Φ $$ []
      · iunfold rwCall; iexact Hci
      have hstep : ∀ ks, delStep (mkeyL x.Key') (rejD (sentV lD) x.Reject') ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]; rfl
      ihave Haus := (BigSepL.bigSepL_impl (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (rejD (sentV lD) x.Reject')) (dghostVar γt (DFrac.own 1) ())
            (fun σ => contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ))) $$ Hinvs
      ihave Haus := Haus $$ []
      · imodintro
        iintro %k %sv %_ #Hi
        iapply rw_au γ c g0 sv.γr.kv (sentV lD) (sentV lU) x hx _ hstep γt Φ
        iframe Hi Hc
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (dghostVar γt (DFrac.own 1) ())
          (fun σ => contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ)
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Htok Haus] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h1]; decide), if_pos h1]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · iunfold callAt at HΦc
        isimp only [if_pos (Or.inr (Or.inl h1))] at HΦc
        resolve3
        rw [← Hy]
        iapply HΦc
        iapply hioOk
    · -- a `GuaranteedUpdate`: committed where the store hands the call's token
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod inv_alloc callN ⊤ iprop((linU γ g0 (boxIn x) Φ ∗ £ 1) ∨
          dghostVar γt (DFrac.own 1) ()) $$ [HAU Hlc1] with #Hci
      · inext
        ileft
        iframe Hlc1
        iunfold linU
        iexact HAU
      ihave #Hc : rwCall γ g0 γt x Φ $$ []
      · iunfold rwCall; iexact Hci
      have hstep : ∀ ks, updStep (mkeyL x.Key') dzero (updD (sentV lU) x) ks = (kStep (sentV lD) (sentV lU) x ks).1 := by
        intro ks; rw [kStep, if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]; rfl
      ihave Haus := (BigSepL.bigSepL_impl (l := c.ms) (Φ := fun _ (sv : client.SrvAt GF) => kInv γ c g0 sv.γr.kv)
          (Ψ := fun _ (sv : client.SrvAt GF) => k8sAuRW sv.γr.kv c (updStep (mkeyL x.Key') dzero (updD (sentV lU) x)) (dghostVar γt (DFrac.own 1) ())
            (fun σ => contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ))) $$ Hinvs
      ihave Haus := Haus $$ []
      · imodintro
        iintro %k %sv %_ #Hi
        iapply rw_au γ c g0 sv.γr.kv (sentV lD) (sentV lU) x hx _ hstep γt Φ
        iframe Hi Hc
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x (dghostVar γt (DFrac.own 1) ())
          (fun σ => contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ)
          (fun _ _ => plainQ c) hc hAs hkey' hpp' hx hQp) $$ [Htok Haus] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_neg (show ¬ x.Kind' = W64 0 by rw [h2]; decide), if_neg (show ¬ x.Kind' = W64 1 by rw [h2]; decide), if_pos h2]
        iframe Htok Haus
      icases Hy with (%Hy | ⟨%σ, HΦc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · iunfold callAt at HΦc
        isimp only [if_pos (Or.inr (Or.inr h2))] at HΦc
        resolve3
        rw [← Hy]
        iapply HΦc
        iapply hioOk
    · -- a `Get`: committed at the first firing at the prophesied revision
      have hk : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
        rw [h3]; decide
      have hk0 : ¬ x.Kind' = W64 0 := fun h => hk (Or.inl h)
      have hk1 : ¬ x.Kind' = W64 1 := fun h => hk (Or.inr (Or.inl h))
      have hk2 : ¬ x.Kind' = W64 2 := fun h => hk (Or.inr (Or.inr h))
      imod dghostVar_alloc (GF := GF) (none : Option KVState) with ⟨%γc, Hγc⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod dghostVar_alloc (GF := GF) (none : Option w64) with ⟨%γp, Hγp⟩
      imod inv_alloc callN ⊤ iprop(
          (linU γ g0 (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
          (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
            dghostVar γp DFrac.discard (some R) ∗ ⌜σ.rev = uint.nat R⌝ ∗
            ghostMapElem γ.r σ.rev DFrac.discard σ ∗
            (contAt g0 x (kStep (sentV lD) (sentV lU) x (c.abs σ)).2 Φ ∨ dghostVar γt (DFrac.own 1) ())))
          $$ [HAU Hlc1 Hγc] with #Hci
      · inext
        ileft
        iframe Hlc1 Hγc
        iunfold linU
        iexact HAU
      ihave #Hc : getCall γ c g0 (sentV lD) (sentV lU) γc γt γp x Φ $$ []
      · iunfold getCall; iexact Hci
      ihave Hmk := get_maker γ c g0 c.ms (sentV lD) (sentV lU) γc γt γp x hx h3 Φ $$ [Hγp]
      · iframe Hinvs Hc Hγp
      have hQr : ∀ (R m : w64) (σ : KVState),
          (fun (R : w64) (_ : w64) σ => readQ c γc R σ) R m σ ⊢ (⌜kvWf c σ⌝ : IProp GF) := by
        intro R m σ
        unfold readQ
        iintro ⟨%h, -⟩
        ipureintro; exact h.1
      wp_apply (wp_call sp c (sentV lD) (sentV lU) x iprop(True) (fun _ => iprop(True))
          (fun R _ σ => readQ c γc R σ) hc hAs hkey' hpp' hx hQr) $$ [Hmk] as %y Hy
      · iframe #
        iunfold callPre
        isimp only [if_neg hk0, if_neg hk1, if_neg hk2]
        iexact Hmk
      icases Hy with (%Hy | ⟨%σ, HQc, %Hy⟩)
      · subst Hy
        resolve3
        exact absurd (by rw [Hxs]; rfl) Hok
      · iunfold callAt at HQc
        isimp only [if_neg hk] at HQc
        icases HQc with #HQc
        iunfold readQ at HQc
        icases HQc with ⟨%Hwr, #Hbit⟩
        have hrev : σ.rev = uint.nat (W64 (σ.rev : Int)) := by
          have := Hwr.2
          simp only [W64, uint.nat, BitVec.toNat_ofInt]
          omega
        ihave #Hv := Hbit $$ %hrev
        iapply fupd_wp
        imod (getCall_take γ c g0 (sentV lD) (sentV lU) γc γt γp x Φ σ) $$ [Htok Hlc2] with HΦc
        · iframe Hc Hv Htok Hlc2
        imodintro
        resolve3
        rw [← Hy]
        iapply HΦc
        iapply hioOk

end proof

end k8setcd3
end EtcdGrove
end Perennial
