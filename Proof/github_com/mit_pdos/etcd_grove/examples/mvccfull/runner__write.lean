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
  icases Hrn2 with ⟨#Hpkg, #Hpm, #Hrk, -, -, -, #Hcfgx, -⟩
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
  ihave %Hsorted : ⌜ks.Pairwise go.GoStringLt⌝ $$ []
  · iunfold runnerKeys at Hrk; icases Hrk with ⟨%keys, -, -, %H, -⟩; ipureintro; exact H
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
    simp only [hc', _root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply wp_pick cfg.Mix'.Step' ws DFrac.discard (W64 6) $$ [$Hpkg $Hws] as %sw ⟨-, %Hsw⟩
    have hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
    by_cases h0 : sw = W64 0
    · -- the leader's step: a new operation, appended to the log, applied
      simp only [h0, _root_.decide_true]
      (try wp_auto)
      have hlt : opsA.length < (sint.Z cfg.Ops').toNat := by omega
      icases writerOwn_leader x ks cfg h γ mp0 mp1 f0 f1 opsA vA0 vA1 nvA nbA qA qsA hlt $$ Hown
        with ⟨%qwl, %nwl, %kl, Hlog, Hctrs, HhW, Hrd, Hm0, %Hl, Hbackl⟩
      obtain ⟨hnw, hkl, hv0, hv1⟩ := Hl
      iunfold memW at Hm0
      icases Hm0 with ⟨Ho0, Hh0, Hc0⟩
      iunfold memCore at Hc0
      icases Hc0 with ⟨Hid, Hhook, Hhok, Hpath, Hbe, Hle, Hkvf, Hrevf, Hcmpf,
        ⟨%lsl, Hlsl, Hlsv, Hlcap⟩, %Hvle, HincW, Hopen, Hmb, Hhis, Hrds, Hbk, HlW, %HU⟩
      iunfold writerCtrs at Hctrs
      icases Hctrs with ⟨%nl, Hnl, Hvals, Hbuilds, %Hnl⟩
      iunfold logOwn at Hlog
      icases Hlog with ⟨%gsl, %ps, Hlx, Hlps, Hlcap2, %Hlp, #Hopis⟩
      have hreach := (logOk_hist ks Hsorted opsA Hlp.2 vA0.ops vA0.ops (Nat.le_refl _) (by omega)).2.2
      obtain ⟨-, hcr1, hcr2⟩ := reach_bounds _ hreach
      rw [σOf_rev] at hcr2
      have hhl := runM_hs_len ks opsA vA0.ops
      have hrev2 : (runM ks opsA vA0.ops).rev + 2 < 2 ^ 63 := by
        unfold MSt.rev; omega
      have hnl1 : sint.Z nl + 1 < 2 ^ 63 := by have := Hnl.2.2; omega
      have hgr : ∀ id ∈ (runM ks opsA vA0.ops).granted, sint.Z id ≤ sint.Z nl := by
        rw [hv0]; exact Hnl.2.1
      have hnvZ : sint.Z (W64 (nvA : Int)) = (nvA : Int) := by
        have : nvA < 2 ^ 62 := by omega
        word
      wp_apply (wp_gen x ks cfg wr h γ.h mp0 (runM ks opsA vA0.ops) lsl nl (W64 (nvA : Int))
          Hnl.1 hnl1 hgr (by rw [hnvZ]; omega) (by rw [hnvZ]; omega) hrev2 hcr1 hcr2
          (by unfold MSt.rev; omega))
        $$ [$Hctx $Hrevf $Hcmpf $Hlsl $Hlsv $Hnl $Hvals]
        as %pp ⟨Hrevf, Hcmpf, Hlsl, Hlsv, %o, %nl', %nv', #Hop, Hnl, Hvals, %Hg⟩
      obtain ⟨hvalid, hnl', hnv1, hnv2⟩ := Hg
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, Hocap⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hlps $Hlcap2 $Hosl] as %gsl' ⟨Hlps, Hlcap2, -⟩
      (try wp_auto)
      -- the log at `opsA ++ [o]`
      have hlok' : logOk ks (opsA ++ [o]) := logOk_snoc ks opsA o Hlp.2 (by rw [← hv0]; exact hvalid)
      have hrs : runM ks (opsA ++ [o]) vA0.ops = runM ks opsA vA0.ops :=
        runM_snoc ks opsA o vA0.ops (by omega)
      ihave Hm0 : memW ks γ.h (opsA ++ [o]) 0 mp0 γ.m0 f0 vA0 qwl nwl kl $$
          [Ho0 Hh0 Hid Hhook Hhok Hpath Hbe Hle Hkvf Hrevf Hcmpf Hlsl Hlsv Hlcap HincW Hopen Hmb
            Hhis Hrds Hbk HlW]
      · iapply memW_snoc ks γ.h opsA o 0 mp0 γ.m0 f0 vA0 qwl nwl kl (by omega)
        iunfold memW; iframe Ho0 Hh0
        iunfold memCore
        dsimp only
        iframe Hid Hhook Hhok Hpath Hbe Hle Hkvf Hrevf Hcmpf HincW Hopen Hmb Hhis Hrds Hbk HlW
        isplitl [Hlsl Hlsv Hlcap]
        · iexists lsl; iframe
        ipureintro; exact ⟨Hvle, HU⟩
      ihave Hlead : leadPre γ.h ks (opsA ++ [o]) vA0.ops true $$ [HhW]
      · unfold leadPre histAt compsAt; simp only [↓reduceIte]; rw [hrs, hv0]; iexact HhW
      have hoo : (opsA ++ [o])[vA0.ops]? = some o := by rw [hv0]; simp
      wp_apply (wp_apply x ks cfg wr h γ.h (opsA ++ [o]) 0 mp0 γ.m0 f0 vA0 qwl nwl kl pp o true
          hoo hlok' hnw (fun _ => by omega) (by simp; omega)) $$ [$Hctx $Hrd $Hop $Hm0 $Hlead]
        as ⟨Hrd, Hpost, %vB0, %kB, %HvB, Hm0⟩
      ihave HhW : histW γ.h (histAt ks (opsA ++ [o]) (opsA.length + 1))
          (compsAt ks (opsA ++ [o]) (opsA.length + 1)) $$ [Hpost]
      · irevert Hpost
        unfold leadPost; simp only [↓reduceIte]; rw [← hv0]
        iintro H; iexact H
      ihave Hlog : logOwn x ks (opsA ++ [o]) $$ [Hlx Hlps Hlcap2]
      · iunfold logOwn; iexists gsl', ps ++ [pp]; iframe
        isplitr
        · ipureintro; exact ⟨by simp [Hlp.1], hlok'⟩
        rw [List.zip_append (by rw [Hlp.1])]
        iapply BigSepL.bigSepL_append.2
        iframe #
        simp only [List.zip_cons_cons, List.zip_nil_right]
        iapply BigSepL.bigSepL_singleton.2
        iexact Hop
      -- the counters
      have hnv'0 : 0 ≤ sint.Z nv' := by omega
      have hnvw : W64 (((sint.Z nv').toNat : Nat) : Int) = nv' := by
        have : (((sint.Z nv').toNat : Nat) : Int) = sint.Z nv' := by omega
        rw [this]; word
      have hgra : grantedAfter ks (opsA ++ [o]) (opsA ++ [o]).length =
          (if o.kind = kGrant then (runM ks opsA vA0.ops).granted ++ [o.id]
            else (runM ks opsA vA0.ops).granted) := by
        unfold grantedAfter
        rw [show (opsA ++ [o]).length = vA0.ops + 1 by simp; omega,
          runM_succ ks (opsA ++ [o]) vA0.ops o hoo, hrs]
        rfl
      ihave Hctrs : writerCtrs x ks (opsA ++ [o]) (sint.Z nv').toNat nbA $$ [Hnl Hvals Hbuilds]
      · iunfold writerCtrs; iexists nl'; rw [hnvw]; iframe
        ipureintro
        rw [hgra]
        have hl1 : (((opsA ++ [o]).length : Nat) : Int) = (opsA.length : Int) + 1 := by simp
        rw [hl1]
        by_cases hk : o.kind = kGrant
        · rw [if_pos hk] at hnl'
          obtain ⟨hid, rfl⟩ := hnl'
          have hnl1' : sint.Z (nl + W64 1) = sint.Z nl + 1 := by word
          refine ⟨by omega, fun id hid' => ?_, by have := Hnl.2.2; omega⟩
          rw [if_pos hk] at hid'
          rcases List.mem_append.1 hid' with h1 | h1
          · have := hgr id h1; omega
          · simp at h1; subst h1; rw [hid]; exact Int.le_refl _
        · rw [if_neg hk] at hnl'
          subst hnl'
          refine ⟨Hnl.1, fun id hid => ?_, by have := Hnl.2.2; omega⟩
          rw [if_neg hk] at hid; exact hgr id hid
      ihave Hown := Hbackl $$ %o %vB0 %kB %((sint.Z nv').toNat) Hlog Hctrs HhW Hrd Hm0 %HvB
      (try wp_auto)
      wp_for_post
      iframe
      iexists opsA ++ [o], vB0, vA1, (sint.Z nv').toNat, nbA, qA, qsA
      iframe
      ipureintro
      refine ⟨Hi.1.trans (List.prefix_append _ _), ?_⟩
      simp only [List.length_append, List.length_singleton]
      have : ((sint.Z nv').toNat : Int) ≤ (nvA : Int) + 3 := by rw [hnvZ] at hnv2; omega
      omega
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
        simp only [hlt', _root_.decide_true]
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
        simp only [hlt', _root_.decide_true]
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
      simp only [hlt', _root_.decide_true, ↓reduceIte]
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
