/- Lean-first (no Rocq counterpart). The proof of `runner.write`: proved.

The outline: the loop's invariant is `writerOwn` (with `nv ≤ 3 · |ops|`; `writerOwn` itself keeps
`|ops| ≤ Ops`, which `restore` needs at every iteration); `pick` of `Mix.Step`; the leader's step,
only under the loop guard `l.ops < x.cfg.Ops` (case 0; `l.ops = |ops|`, so the longer log is still
at most `Ops`): `gen` at `runM ks ops |ops|` (`writerCtrs`' `nextLease`), the op appended to `x.log`
(`logOk` extended by `opValid`; every `memW` and `histW` restated at the longer log, `runM_prefix`),
`apply` leading; the follower's: `apply` with the lower bound from `histW`;
`restore`; `restart` of either; `checkLeases` of both; then the follower's loop.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__write
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restore
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restart
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteLoopLemmas

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
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.write.wp_proof
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_gen : runner.gen.spec (GF := GF) (hG := hG))
    (wp_apply : runner.apply.spec (GF := GF) (hG := hG))
    (wp_restore : runner.restore.spec (GF := GF) (hG := hG))
    (wp_restart : runner.restart.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.write.spec (GF := GF) (hG := hG) := by
  intro hT hR x ks cfg wr h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs hnv hopen hclose hckpt hlim hbl
  wp_start as ⟨#Hctx, #Hks, #Henv, Htok, Hown⟩
  haveI : Persistent (runnerMs (GF := GF) x mp0 mp1) := by unfold runnerMs; infer_instance
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hrn, #Hcfg, %Hmix, #Hrds, #Hpb, #Hps, #Hpl, #Hpt, %Hkl, #Hlg, ⟨%wo, #Hwo⟩,
    ⟨%wc, #Hwc⟩, ⟨%ws, #Hws⟩, #Hcrv, #Hccp, #Hcrs, #Hcrt, %Hops⟩
  ihave #Hrn2 := Hrn
  iunfold rnCtx at Hrn2
  icases Hrn2 with ⟨#Hpkg, #Hpm, -, -, -, -, #Hcfgx, -⟩
  ihave #Hms : runnerMs x mp0 mp1 $$ [Hown]
  · iunfold writerOwn at Hown; icases Hown with ⟨#H, -⟩; iexact H
  ihave #Hms2 := Hms
  iunfold runnerMs at Hms2
  icases Hms2 with ⟨%msl, #Hmsx, #Hmsl⟩
  ihave %Hmsll := ownSlice_len $$ Hmsl
  obtain ⟨Hmsl1, Hmsl2⟩ := Hmsll
  have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z msl.len := by
    simp only [List.length_cons, List.length_nil] at Hmsl1
    have : sint.nat msl.len = (sint.Z msl.len).toNat := rfl
    constructor <;> word
  have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z msl.len := by
    simp only [List.length_cons, List.length_nil] at Hmsl1
    have : sint.nat msl.len = (sint.Z msl.len).toNat := rfl
    constructor <;> word
  icases ownSlice_elem_acc (sint.Z (W64 0)) mp0 msl DFrac.discard [mp0, mp1] (by word) (by simp)
    $$ Hmsl with ⟨#He0, -⟩
  icases ownSlice_elem_acc (sint.Z (W64 1)) mp1 msl DFrac.discard [mp0, mp1] (by word) (by simp)
    $$ Hmsl with ⟨#He1, -⟩
  wp_auto
  rw [ite_eq_left hb0]
  wp_auto
  rw [ite_eq_left hb1]
  wp_auto
  have hOps0 := Hops
  icases typedPointsto_split _ _ _ $$ Hcfgx with #Hcfgf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfgf
  icases typedPointsto_split _ _ _ $$ Mix with #HMixf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed HMixf
  ihave HI : (∃ (opsA : List OpM) (vA0 vA1 : MemS) (nvA nbA : Nat) (qA qsA : Qp),
      "Hown" ∷ writerOwn x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA ∗
      "Htok" ∷ threadTok ∗
      "%Hi" ∷ ⌜ops <+: opsA ∧ nvA + 3 * ((sint.Z cfg.Ops').toNat - opsA.length) ≤
        nv + 3 * (sint.Z cfg.Ops').toNat⌝ : IProp GF) $$ [Hown Htok]
  · iexists ops, v0, v1, nv, nb, q, qs
    iframe
    ipureintro; exact ⟨List.prefix_refl _, by omega⟩
  have hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
  wp_for HI
  icases writerOwn_ops x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA $$ Hown
    with ⟨%HopsA, Hops0f, Hops1f, Hback⟩
  wp_auto
  ihave Hown := Hback $$ Hops0f Hops1f
  have hOpsZ : sint.Z (W64 (vA0.ops : Int)) = (vA0.ops : Int) := by
    have : vA0.ops < 2 ^ 38 := by omega
    word
  by_cases hc : (vA0.ops : Int) < sint.Z cfg.Ops'
  · -- an iteration
    have hc' : sint.Z (W64 (vA0.ops : Int)) < sint.Z cfg.Ops' := by rw [hOpsZ]; exact hc
    simp only [hc', decide_true, ↓reduceIte]
    wp_auto
    wp_apply wp_pick cfg.Mix'.Step' ws DFrac.discard (W64 6) $$ [$Hpkg $Hws] as %sw ⟨-, %Hsw⟩
    have hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
    by_cases h0 : sw = W64 0
    · simp only [h0, _root_.decide_true]
      (try wp_auto)
      sorry
    rw [decide_eq_false h0]
    (try wp_auto)
    by_cases h1 : sw = W64 1
    · -- the follower's step
      simp only [h1, _root_.decide_true]
      (try wp_auto)
      icases writerOwn_ops x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA $$ Hown
        with ⟨-, Hops0f, Hops1f, Hback⟩
      wp_auto
      ihave Hown := Hback $$ Hops0f Hops1f
      have hv0Z : sint.Z (W64 (vA0.ops : Int)) = (vA0.ops : Int) := hOpsZ
      have hv1Z' : sint.Z (W64 (vA1.ops : Int)) = (vA1.ops : Int) := by
        have : vA1.ops < 2 ^ 38 := by omega
        word
      by_cases hlt : vA1.ops < vA0.ops
      · have hlt' : sint.Z (W64 (vA1.ops : Int)) < sint.Z (W64 (vA0.ops : Int)) := by
          rw [hv0Z, hv1Z']; exact_mod_cast hlt
        simp only [hlt', decide_true]
        (try wp_auto)
        icases writerOwn_follower x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA hlt $$ Hown
          with ⟨%gsl, %ps, %pp, %o, %qwf, %nwf, %kf, Hlogf, Hlps, %Hf, #Hop, Hm1, Hrd, #Hlbf, Hbackf⟩
        obtain ⟨hpp, hoo, hlok, hnw1, hk1, hl1, hlO⟩ := Hf
        iunfold memW at Hm1
        icases Hm1 with ⟨Ho1, Hh1, Hc1⟩
        ihave %Hpsl := ownSlice_len $$ Hlps
        have hv1Z : sint.Z (W64 (vA1.ops : Int)) = (vA1.ops : Int) := by
          have : vA1.ops < 2 ^ 38 := by omega
          word
        have hbi : 0 ≤ sint.Z (W64 (vA1.ops : Int)) ∧ sint.Z (W64 (vA1.ops : Int)) < sint.Z gsl.len := by
          have : sint.nat gsl.len = (sint.Z gsl.len).toNat := rfl
          have := (List.getElem?_eq_some_iff.1 hpp).1
          rw [hv1Z]; constructor <;> omega
        (try wp_auto)
        rw [ite_eq_left hbi]
        icases ownSlice_elem_acc (sint.Z (W64 (vA1.ops : Int))) pp gsl (DFrac.own 1) ps (by omega)
          (by rw [hv1Z]; simpa using hpp) $$ Hlps with ⟨Hel, Hpsb⟩
        (try wp_auto)
        ihave Hlps := Hpsb $$ %pp Hel
        have hset : ps.set (sint.Z (W64 (vA1.ops : Int))).toNat pp = ps := by
          obtain ⟨hlt2, heq2⟩ := List.getElem?_eq_some_iff.1 hpp
          rw [hv1Z]; simp only [Int.toNat_natCast]; rw [← heq2]; exact List.set_getElem_self hlt2
        rw [hset]
        ihave Hm1 : memW ks γ.h opsA 1 mp1 γ.m1 f1 vA1 qwf nwf kf $$ [Ho1 Hh1 Hc1]
        · iunfold memW; iframe
        ihave Hlbf' : leadPre γ.h ks opsA vA1.ops false $$ []
        · unfold leadPre; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hlbf
        wp_apply (wp_apply x ks cfg wr h γ.h opsA 1 mp1 γ.m1 f1 vA1 qwf nwf kf pp o false hoo hlok hnw1
            (fun _ => by omega) (by omega)) $$ [$Hctx $Hrd $Hop $Hm1 $Hlbf']
          as ⟨Hrd, -, %vB1, %kB, %HvB, Hm1⟩
        ihave Hown := Hbackf $$ %vB1 %kB Hlogf Hlps Hm1 Hrd %HvB
        (try wp_auto)
        wp_for_post
        iframe
        iexists opsA, vA0, vB1, nvA, nbA, qA, qsA
        iframe
        ipureintro; exact Hi
      · have hlt' : ¬ sint.Z (W64 (vA1.ops : Int)) < sint.Z (W64 (vA0.ops : Int)) := by
          rw [hv0Z, hv1Z']; exact_mod_cast hlt
        simp only [hlt', decide_false]
        (try wp_auto)
        wp_for_post
        iframe
        iexists opsA, vA0, vA1, nvA, nbA, qA, qsA
        iframe
        ipureintro; exact Hi
    rw [decide_eq_false h1]
    (try wp_auto)
    by_cases h2 : sw = W64 2
    · -- a snapshot installed on the follower
      simp only [h2, _root_.decide_true]
      (try wp_auto)
      icases writerOwn_ops x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA $$ Hown
        with ⟨-, Hops0f, Hops1f, Hback⟩
      wp_auto
      ihave Hown := Hback $$ Hops0f Hops1f
      have hv0Z : sint.Z (W64 (vA0.ops : Int)) = (vA0.ops : Int) := hOpsZ
      have hv1Z' : sint.Z (W64 (vA1.ops : Int)) = (vA1.ops : Int) := by
        have : vA1.ops < 2 ^ 38 := by omega
        word
      by_cases hlt : vA1.ops < vA0.ops
      · have hlt' : sint.Z (W64 (vA1.ops : Int)) < sint.Z (W64 (vA0.ops : Int)) := by
          rw [hv0Z, hv1Z']; exact_mod_cast hlt
        simp only [hlt', decide_true]
        (try wp_auto)
        wp_apply (wp_restore x ks cfg wr h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA hlt
            hopen hclose hckpt hlim hbl) $$ [$Hctx $Hks $Henv $Htok $Hown]
          as ⟨Htok, %vB1, %HvB, Hown⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists opsA, vA0, vB1, nvA, nbA + 1, qA, qsA
        iframe
        ipureintro; exact Hi
      · have hlt' : ¬ sint.Z (W64 (vA1.ops : Int)) < sint.Z (W64 (vA0.ops : Int)) := by
          rw [hv0Z, hv1Z']; exact_mod_cast hlt
        simp only [hlt', decide_false]
        (try wp_auto)
        wp_for_post
        iframe
        iexists opsA, vA0, vA1, nvA, nbA, qA, qsA
        iframe
        ipureintro; exact Hi
    rw [decide_eq_false h2]
    (try wp_auto)
    by_cases h3 : sw = W64 3
    · -- the leader's restart
      simp only [h3, _root_.decide_true]
      (try wp_auto)
      wp_apply (wp_restart x ks cfg wr h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA 0 mp0 rfl
          hopen hclose hckpt hlim hbl) $$ [$Hctx $Hks $Henv $Htok $Hown]
        as ⟨Htok, %vB0, %vB1, %qB, %qsB, %HvB, Hown⟩
      wp_for_post
      iframe
      iexists opsA, vB0, vB1, nvA, nbA, qB, qsB
      iframe
      ipureintro; exact Hi
    rw [decide_eq_false h3]
    (try wp_auto)
    by_cases h4 : sw = W64 4
    · -- the follower's restart
      simp only [h4, _root_.decide_true]
      (try wp_auto)
      wp_apply (wp_restart x ks cfg wr h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA 1 mp1 rfl
          hopen hclose hckpt hlim hbl) $$ [$Hctx $Hks $Henv $Htok $Hown]
        as ⟨Htok, %vB0, %vB1, %qB, %qsB, %HvB, Hown⟩
      wp_for_post
      iframe
      iexists opsA, vB0, vB1, nvA, nbA, qB, qsB
      iframe
      ipureintro; exact Hi
    rw [decide_eq_false h4]
    (try wp_auto)
    -- both members' leases checked
    icases writerOwn_check0 x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA $$ Hown
      with ⟨%qwc, %nwc, %kc, Hc, Hrd, #Hlbc, %Hlok, Hback⟩
    wp_apply (wp_checkLeases x ks cfg wr h γ.h opsA 0 mp0 γ.m0 f0 vA0 qwc nwc kc Hlok)
      $$ [$Hctx $Hrd $Hlbc $Hc] as ⟨Hrd, Hc⟩
    ihave Hown := Hback $$ Hc Hrd
    (try wp_auto)
    icases writerOwn_check1 x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA $$ Hown
      with ⟨%qwc, %nwc, %kc, Hc, Hrd, #Hlbc, %Hlok, Hback⟩
    wp_apply (wp_checkLeases x ks cfg wr h γ.h opsA 1 mp1 γ.m1 f1 vA1 qwc nwc kc Hlok)
      $$ [$Hctx $Hrd $Hlbc $Hc] as ⟨Hrd, Hc⟩
    ihave Hown := Hback $$ Hc Hrd
    (try wp_auto)
    wp_for_post
    iframe
    iexists opsA, vA0, vA1, nvA, nbA, qA, qsA
    iframe
    ipureintro; exact Hi
  · -- the follower's catch-up
    have hc' : ¬ sint.Z (W64 (vA0.ops : Int)) < sint.Z cfg.Ops' := by rw [hOpsZ]; exact hc
    simp only [hc', decide_false]
    have hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
    rw [decide_eq_false hft]
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.decide_true]
    wp_auto
    have hA0 : vA0.ops = (sint.Z cfg.Ops').toNat := by omega
    ihave HJ : (∃ (vA1 : MemS) (qA qsA : Qp),
        "Hown" ∷ writerOwn x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA ∗
        "Htok" ∷ threadTok : IProp GF) $$ [Hown Htok]
    · iexists vA1, qA, qsA; iframe
    wp_for HJ
    icases writerOwn_ops x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA $$ Hown
      with ⟨%HopsB, Hops0f, Hops1f, Hback⟩
    wp_auto
    ihave Hown := Hback $$ Hops0f Hops1f
    have hv1Z' : sint.Z (W64 (vA1.ops : Int)) = (vA1.ops : Int) := by
      have : vA1.ops < 2 ^ 38 := by omega
      word
    by_cases hlt : vA1.ops < vA0.ops
    · have hlt' : sint.Z (W64 (vA1.ops : Int)) < sint.Z (W64 (vA0.ops : Int)) := by
        rw [hOpsZ, hv1Z']; exact_mod_cast hlt
      simp only [hlt', decide_true, ↓reduceIte]
      (try wp_auto)
      icases writerOwn_follower x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA hlt $$ Hown
        with ⟨%gsl, %ps, %pp, %o, %qwf, %nwf, %kf, Hlogf, Hlps, %Hf, #Hop, Hm1, Hrd, #Hlbf, Hbackf⟩
      obtain ⟨hpp, hoo, hlok, hnw1, hk1, hl1, hlO⟩ := Hf
      iunfold memW at Hm1
      icases Hm1 with ⟨Ho1, Hh1, Hc1⟩
      ihave %Hpsl := ownSlice_len $$ Hlps
      have hv1Z : sint.Z (W64 (vA1.ops : Int)) = (vA1.ops : Int) := by
        have : vA1.ops < 2 ^ 38 := by omega
        word
      have hbi : 0 ≤ sint.Z (W64 (vA1.ops : Int)) ∧ sint.Z (W64 (vA1.ops : Int)) < sint.Z gsl.len := by
        have : sint.nat gsl.len = (sint.Z gsl.len).toNat := rfl
        have := (List.getElem?_eq_some_iff.1 hpp).1
        rw [hv1Z]; constructor <;> omega
      (try wp_auto)
      rw [ite_eq_left hbi]
      icases ownSlice_elem_acc (sint.Z (W64 (vA1.ops : Int))) pp gsl (DFrac.own 1) ps (by omega)
        (by rw [hv1Z]; simpa using hpp) $$ Hlps with ⟨Hel, Hpsb⟩
      (try wp_auto)
      ihave Hlps := Hpsb $$ %pp Hel
      have hset : ps.set (sint.Z (W64 (vA1.ops : Int))).toNat pp = ps := by
        obtain ⟨hlt2, heq2⟩ := List.getElem?_eq_some_iff.1 hpp
        rw [hv1Z]; simp only [Int.toNat_natCast]; rw [← heq2]; exact List.set_getElem_self hlt2
      rw [hset]
      ihave Hm1 : memW ks γ.h opsA 1 mp1 γ.m1 f1 vA1 qwf nwf kf $$ [Ho1 Hh1 Hc1]
      · iunfold memW; iframe
      ihave Hlbf' : leadPre γ.h ks opsA vA1.ops false $$ []
      · unfold leadPre; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hlbf
      wp_apply (wp_apply x ks cfg wr h γ.h opsA 1 mp1 γ.m1 f1 vA1 qwf nwf kf pp o false hoo hlok hnw1
          (fun _ => by omega) (by omega)) $$ [$Hctx $Hrd $Hop $Hm1 $Hlbf']
        as ⟨Hrd, -, %vB1, %kB, %HvB, Hm1⟩
      ihave Hown := Hbackf $$ %vB1 %kB Hlogf Hlps Hm1 Hrd %HvB
      (try wp_auto)
      wp_for_post
      iframe
      iexists vB1, qA, qsA
      iframe
    · have hlt' : ¬ sint.Z (W64 (vA1.ops : Int)) < sint.Z (W64 (vA0.ops : Int)) := by
        rw [hOpsZ, hv1Z']; exact_mod_cast hlt
      simp only [hlt', decide_false]
      rw [decide_eq_false hft]
      simp only [Bool.false_eq_true, ↓reduceIte, _root_.decide_true]
      (try wp_auto)
      iapply HΦ
      iframe Htok
      iexists opsA, vA0, vA1, nvA, nbA, qA, qsA
      iframe Hown
      ipureintro; exact ⟨Hi.1, by omega, by omega⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
