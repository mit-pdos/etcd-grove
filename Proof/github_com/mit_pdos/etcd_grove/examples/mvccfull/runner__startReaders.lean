/- Lean-first (no Rocq counterpart). The proof of `runner.startReaders`: Draft, to come.

The outline: `readStop.Store(0)` in its invariant (`rdShared`); `x.ms` is `[mp0, mp1]`
(`runnerMs`); for each member and each of the `max 0 cfg.Readers` iterations, the join's `Add(1)`
(`sync.tokJoin.WaitGroup.wp_Add`, the writer's thread token deposited) with `P' :=` the reader's
part less its handles, then `go` (the fresh token back to the writer); the goroutine's loop
(`readStop.Load`, `readOne`, `reads.Add(1)` in `rdShared`'s invariants, `time.Sleep`) keeps its
`rdOwn`, and its `Done` (`wp_Done`) gives the part back. The parts are `rdStock`'s split at `q / n`
(`rdStock_split`, `n > 0`; at `n = 0` the stock stays in the adder's wand). Perennial's results
(`Int64.Load/Store/Add`, `time.Sleep`, the join's `Add`/`Done`) are used directly. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__readOne
public import Perennial.Spec.time.Sleep
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.startReaders.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_readOne : runner.readOne.spec (GF := GF) (hG := hG)) :
    runner.startReaders.spec (GF := GF) (hG := hG) := by
  intro x cfg wr ks h γ mp0 mp1 e0 e1 q hmix
  haveI : Persistent (runnerKeys (GF := GF) x ks) := by unfold runnerKeys; infer_instance
  haveI : Persistent (runnerH (GF := GF) x h) := by unfold runnerH; infer_instance
  haveI : Persistent (runnerCfg (GF := GF) x cfg wr) := by
    unfold runnerCfg runnerRangeMix; infer_instance
  haveI : Persistent (runnerMs (GF := GF) x mp0 mp1) := by unfold runnerMs; infer_instance
  haveI : Persistent (rdShared (GF := GF) x) := by unfold rdShared ctrInv; infer_instance
  haveI : ∀ i mp m ι kv, Persistent (isInc (GF := GF) ks γ.h i mp m ι kv) := by
    intro i mp m ι kv; haveI := hpers.1 kv ι.kv; unfold isInc; infer_instance
  wp_start as ⟨#HK, #HH, #HC, #HM, #HS, #H0, #H1, Hst, Had, Htok⟩
  ihave #HS' := HS
  iunfold rdShared at HS'
  iunfold ctrInv at HS'
  icases HS' with ⟨#Hstop, #Hreads⟩
  ihave #HM' := HM
  iunfold runnerMs at HM'
  icases HM' with ⟨%msl, #Hmsl, #Hms⟩
  ihave #HC' := HC
  iunfold runnerCfg at HC'
  icases HC' with ⟨#HRM, #Hwr⟩
  ihave #HRM' := HRM
  iunfold runnerRangeMix at HRM'
  icases HRM' with ⟨#Hcfg, %wrr, #Hwrr⟩
  ihave #Hcf := typedPointsto_split _ _ _ $$ Hcfg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  ihave #Hmx := typedPointsto_split _ _ _ $$ Mix
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmx
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Store (rF go!"readStop" x) (W64 0) $$ [] [-]
  · iPkgInit
  iinv Hstop with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "stop") from
    Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hcl with -
  imod Hclose $$ [Hv] with -
  · inext; iexists (W64 0); iexact Hv
  imodintro
  wp_auto
  ipersist x
  -- the readers' parts, at the share `q / n` each
  generalize hR : (sint.Z cfg.Readers').toNat = R
  ihave ⟨Hrps, Hfin⟩ : (([∗list] _u ∈ List.replicate (2 * R) (),
      rdOwn ks h γ mp0 mp1 e0 e1 (q / sync.posToQpZ ((2 * R : Nat) : Int))) ∗
      (([∗list] _u ∈ List.replicate (2 * R) (),
        rdOwn ks h γ mp0 mp1 e0 e1 (q / sync.posToQpZ ((2 * R : Nat) : Int))) -∗
        rdStock h γ mp0 mp1 e0 e1 (2 * R) q)) $$ [Hst]
  · rcases Nat.eq_zero_or_pos (2 * R) with hn | hn
    · rw [hn, List.replicate_zero]
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      · iintro -; iexact Hst
    · ihave Hw := rdStock_split hpers hsplit ks h γ mp0 mp1 e0 e1 (2 * R) q hn $$ [$H0 $H1]
      ihave Hw2 := rdStock_split hpers hsplit ks h γ mp0 mp1 e0 e1 (2 * R) q hn $$ [$H0 $H1]
      iunfold wandIff at Hw
      iunfold wandIff at Hw2
      icases Hw with ⟨Hf, -⟩
      icases Hw2 with ⟨-, Hb⟩
      isplitl [Hst Hf]
      · iapply Hf $$ Hst
      · iexact Hb
  generalize hRp : rdOwn (GF := GF) ks h γ mp0 mp1 e0 e1 (q / sync.posToQpZ ((2 * R : Nat) : Int)) = Rp
  ihave Had : sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) 0
      iprop([∗list] _u ∈ List.replicate 0 (), Rp) $$ [Had]
  · iapply sync.tokJoin.ownAdder_wand $$ [] Had
    iintro -; rw [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  ihave %Hlen := ownSlice_len $$ Hms
  ihave HI : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ 2⌝ ∗
      "Had" ∷ sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) (sint.nat iv * R)
        iprop([∗list] _u ∈ List.replicate (sint.nat iv * R) (), Rp) ∗
      "Hrps" ∷ ([∗list] _u ∈ List.replicate (2 * R - sint.nat iv * R) (), Rp) ∗
      "Htok" ∷ threadTok : IProp GF) $$ [i Had Hrps Htok]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, Nat.zero_mul, Nat.sub_zero]
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hiv : sint.Z iv < 2 := by simp at Hlen; word
    try wp_auto
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    obtain ⟨mval, hmval⟩ : ∃ mval, [mp0, mp1][(sint.Z iv).toNat]? = some mval := by
      refine ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    wp_apply wp_load_slice_index msl (sint.Z iv) [mp0, mp1] DFrac.discard mval Hi.1 $$ [Hms] as -
    · iframe #; ipureintro; exact hmval
    try wp_auto
    ipersist m
    ihave HJ : (∃ jv : w64, "j" ∷ j_ptr ↦ jv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ max 0 (sint.Z cfg.Readers')⌝ ∗
        "Had" ∷ sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x)
          (sint.nat iv * R + sint.nat jv)
          iprop([∗list] _u ∈ List.replicate (sint.nat iv * R + sint.nat jv) (), Rp) ∗
        "Hrps" ∷ ([∗list] _u ∈ List.replicate (2 * R - (sint.nat iv * R + sint.nat jv)) (), Rp) ∗
        "Htok" ∷ threadTok : IProp GF) $$ [j Had Hrps Htok]
    · iexists W64 0
      rw [show sint.nat (W64 0) = 0 from rfl, Nat.add_zero]
      iframe
      ipureintro; constructor <;> word
    wp_for HJ
    have hivn : sint.nat iv = (sint.Z iv).toNat := rfl
    wp_if_destruct
    · -- a reader: `Add(1)`, the goroutine
      have hjn : sint.nat jv = (sint.Z jv).toNat := rfl
      have hk : sint.nat iv * R + sint.nat jv + 1 ≤ 2 * R := by
        have h1 : sint.nat iv ≤ 1 := by omega
        have h2 : sint.nat jv + 1 ≤ R := by omega
        calc sint.nat iv * R + sint.nat jv + 1 ≤ 1 * R + R := by
              have := Nat.mul_le_mul_right R h1; omega
          _ = 2 * R := by omega
      rw [show 2 * R - (sint.nat iv * R + sint.nat jv) =
        (2 * R - (sint.nat iv * R + sint.nat jv + 1)) + 1 by omega, List.replicate_succ]
      icases BigSepL.bigSepL_cons.1 $$ Hrps with ⟨Hrp, Hrps⟩
      wp_apply (sync.tokJoin.WaitGroup.wp_Add Rp rdWgN iprop(False) (rF go!"readWg" x) _ _)
        $$ [Had Htok] as ⟨Had, Hdone⟩
      · iframe
      try wp_auto
      wp_apply wp_fork_tok_self $$ [Hrp Hdone] as Htok
      · -- the reader goroutine
        wp_auto
        ihave HG : (∃ nv : w64, "n" ∷ n_ptr ↦ nv ∗ "Hrp" ∷ Rp : IProp GF) $$ [n Hrp]
        · iexists _; iframe
        wp_for HG
        wp_if_destruct
        · wp_apply_core sync.atomic.Int64.wp_Load (rF go!"readStop" x) (DFrac.own 1) $$ [] [-]
          · iPkgInit
          iinv Hstop with ⟨%v, >Hv⟩ Hclose
          iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "stop") from
            Std.LawfulSet.empty_subset)
          iintro Hcl
          inext
          iexists v
          iframe Hv
          iintro Hv
          imod Hcl with -
          imod Hclose $$ [Hv] with -
          · inext; iexists v; iexact Hv
          imodintro
          wp_auto
          by_cases hv : v = W64 0
          · subst hv
            simp only [decide_true, ↓reduceIte]
            wp_auto
            subst hRp
            wp_apply (wp_readOne x cfg wr ks h γ mp0 mp1 e0 e1 _ (sint.nat iv) mval hmix hmval)
              $$ [Hrp] as Hrp
            · iframe; iframe #
            try wp_auto
            wp_apply_core sync.atomic.Int64.wp_Add (rF go!"reads" x) (W64 1) $$ [] [-]
            · iPkgInit
            iinv Hreads with ⟨%v, >Hv⟩ Hclose
            iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "reads") from
              Std.LawfulSet.empty_subset)
            iintro Hcl
            inext
            iexists v
            iframe Hv
            iintro Hv
            imod Hcl with -
            imod Hclose $$ [Hv] with -
            · inext; iexists _; iexact Hv
            imodintro
            wp_auto
            wp_apply wp_Sleep
            wp_for_post
            iframe
            iexists _
            iframe
          · simp only [hv, decide_false]
            cleanup_bool_decide
            try wp_auto
            wp_apply (sync.tokJoin.WaitGroup.wp_Done rdWgN iprop(False) (rF go!"readWg" x) _) $$ [Hdone Hrp]
              as Htok
            · iframe
            try wp_auto
            iframe
        · try cleanup_bool_decide
          try wp_auto
          wp_apply (sync.tokJoin.WaitGroup.wp_Done rdWgN iprop(False) (rF go!"readWg" x) _) $$ [Hdone Hrp]
            as Htok
          · iframe
          try wp_auto
          iframe
      wp_for_post
      iframe HΦ Hfin i
      iexists (jv + W64 1)
      have hj1 : sint.nat (jv + W64 1) = sint.nat jv + 1 := by word
      rw [hj1]
      iframe
      isplitr
      · ipureintro; constructor <;> word
      iapply sync.tokJoin.ownAdder_wand $$ [] Had
      iintro ⟨Hs, Hr⟩
      rw [show sint.nat iv * R + (sint.nat jv + 1) = (sint.nat iv * R + sint.nat jv) + 1 by omega,
        List.replicate_succ]
      iapply BigSepL.bigSepL_cons.2
      iframe
    · -- the member's readers started
      have hjR : sint.nat jv = R := by
        have hjn : sint.nat jv = (sint.Z jv).toNat := rfl
        omega
      wp_for_post
      iframe HΦ Hfin
      iexists (iv + W64 1)
      have hi1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
      rw [hi1, show (sint.nat iv + 1) * R = sint.nat iv * R + sint.nat jv by
        rw [hjR, Nat.succ_mul]]
      iframe
      ipureintro; constructor <;> word
  · -- both members' readers started
    have hiv : sint.nat iv = 2 := by
      have : sint.nat iv = (sint.Z iv).toNat := rfl
      have : sint.nat msl.len = (sint.Z msl.len).toNat := rfl
      simp at Hlen; omega
    rw [hiv, Nat.sub_self]
    try wp_auto
    iapply HΦ
    iframe Htok
    iapply sync.tokJoin.ownAdder_wand $$ [Hfin] Had
    iexact Hfin

end proof

end mvccfull
end EtcdGrove
end Perennial
