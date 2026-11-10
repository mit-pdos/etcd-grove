/- Lean-first (no Rocq counterpart). The proof of `stream.watch`: Draft, to come (`sorry`).

The callees in call order: `genKey`, `genEnd` `choose`, `pick` (the
start's weights), `context.TODO`, `Watch` (through `shapes.law`), `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__watch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WatchLemmas
public import Perennial.Spec.sync.atomic.Int64__Add

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

theorem stream.watch.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (wp_runner_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_runner_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_pick : EtcdGrove.mvccfull.pick.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    stream.watch.spec (GF := GF) (hG := hG) := by
  intro T q C
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  haveI := streamCtx_persistent hpers T
  haveI : ∀ kv γ, Persistent (isMvcc (GF := GF) kv γ) := hpers.1
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  wp_start as ⟨#Hctx0, Hro⟩
  ihave Hctx := Hctx0
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, #Hstop⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfg, #Hwa, #Hwst, #Cev, #Cpr, #Ccp, #Ccn⟩
  iunfold regOwn at Hro
  icases Hro with ⟨Hrd, Hcl, Hcn⟩
  icases (epRd_split T.ep q).1 $$ Hrd with ⟨Hrdr, Hlive, Hkvf⟩
  iunfold epLive at Hlive
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Add (mF go!"regs" T.ep.mp) (W64 1) $$ [] [-]
  · iPkgInit
  iunfold ctrInv at Hregs
  iinv Hregs with ⟨%a, >Ha⟩ Hclose
  all_goals (try exact (fun _ _ => CoPset.mem_full))
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "regs") from
    Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iexists a
  iframe
  iintro Ha
  imod Hcl2 with -
  imod Hclose $$ [Ha] with -
  · inext; iexists _; iframe
  imodintro
  ihave #Hcf := typedPointsto_split _ _ _ $$ Hcfg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  ihave #Hmx := typedPointsto_split _ _ _ $$ Mix
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmx
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iunfold regOwn
    iframe
    iapply (epRd_split T.ep q).2
    iframe
  wp_apply (wp_runner_genKey T.ep.x T.ep.ks) $$ [$Hkeys] as %ksl ⟨%kk, Hksl, %Hkk⟩
  imod ownSlice_persist _ _ _ $$ Hksl with #Hksl
  (try wp_auto)
  wp_apply (wp_runner_genEnd T.ep.x T.ep.ks) $$ [$Hkeys] as %esl ⟨%e0, Hesl, %He0⟩
  imod ownSlice_persist _ _ _ $$ Hesl with #Hesl
  (try wp_auto)
  wp_apply wp_choose as %flt %Hflt
  (try wp_auto)
  generalize «$r0_ptr» = wpl at *
  -- the end, `nil` when it would make the range empty
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ w_ptr ↦ wpl ∗
      ∃ (endk : GoSlice) (e : GoString), wpl ↦ (watcher.mk ksl endk flt 0 0 0 0 false false false) ∗ endk ↦*□ e ∗ ⌜e = [] ∨ go.GoStringLt kk e⌝))) $$ [w «$r0»]
  · wp_if_destruct
    · (try wp_auto)
      wp_apply wp_bytes_to_string esl e0 DFrac.discard $$ [$Hesl] as -
      (try wp_auto)
      wp_apply wp_bytes_to_string ksl kk DFrac.discard $$ [$Hksl] as -
      (try wp_auto)
      wp_if_destruct
      · ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
        · iapply ownSlice_nil
        iframe
        iexists []
        iframe
        iframe #
        ipureintro; left; rfl
      · iframe
        iexists e0
        iframe
        iframe #
        ipureintro; right
        by_cases hlt : go.GoStringLt kk e0
        · exact hlt
        · exfalso; apply Hif
          by_cases h2 : go.GoStringLt e0 kk
          · exact Or.inr h2
          · exact Or.inl (go.goStringLt_eq_of_not_lt h2 hlt)
    · ihave %Hel := ownSlice_len $$ Hesl
      have he0 : e0 = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := Hel.1; have h0 : sint.Z (W64 0) = 0 := rfl; word
      iframe
      iexists e0
      iframe
      iframe #
      ipureintro; left; exact he0
  iintro %v ⟨%hv, w, %endk, %e, «$r0», #Hend, %Hend⟩
  subst hv
  wp_auto
  icases Hwst with ⟨%wst, #Hwst⟩
  wp_apply (wp_pick _ wst DFrac.discard (W64 3)) $$ [$Hwst] as %sw ⟨-, %Hsw⟩
  (try wp_auto)
  -- the start revision
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ w_ptr ↦ wpl ∗ s_ptr ↦ T.s ∗
      incLive T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q ∗
      ∃ st : w64, wpl ↦ (watcher.mk ksl endk flt st 0 0 0 false false false) ∗
        ⌜0 ≤ sint.Z st ∧ sint.Z st < 2 ^ 62 + 3 ∧ (st ≠ W64 0 → 1 ≤ sint.Z st)⌝))) $$ [w s Hlive «$r0»]
  · wp_if_destruct
    · -- from any revision up to two past `revHi`
      (try wp_auto)
      imod monoNatLbOwn_0 (GF := GF) T.ep.m.rev with #H0
      wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revHi" T.ep.mp) (DFrac.own 1) $$ [] [-]
      · iPkgInit
      imod revHi_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q 0 $$ [$Hlive $H0]
        with ⟨%vh, Hvh, %Hvhb, Hcl⟩
      imodintro
      inext
      iexists vh
      iframe Hvh
      iintro Hvh
      imod Hcl $$ Hvh with Hlive
      imodintro
      (try wp_auto)
      wp_apply wp_choose as %c %Hc
      (try wp_auto)
      iframe
      ipureintro
      have h2 : sint.Z (vh + W64 2) = sint.Z vh + 2 := by word
      have hc := Hc.2.1 (by rw [h2]; omega)
      rw [h2] at hc
      (try refine ⟨rfl, ?_⟩); refine ⟨by word, by word, fun _ => by word⟩
    · wp_if_destruct
      · -- from the compaction floor (at least `1`)
        (try wp_auto)
        wp_apply_core sync.atomic.Int64.wp_Load (mF go!"cmpLo" T.ep.mp) (DFrac.own 1) $$ [] [-]
        · iPkgInit
        imod cmpLo_acc_lt hpers hreach T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q $$ Hlive
          with ⟨%vc, Hvc, %Hvcb, Hcl⟩
        imodintro
        inext
        iexists vc
        iframe Hvc
        iintro Hvc
        imod Hcl $$ Hvc with Hlive
        imodintro
        wp_auto
        wp_if_destruct
        · iframe
          ipureintro; (try refine ⟨rfl, ?_⟩); exact ⟨by decide, by decide, fun _ => by decide⟩
        · iframe
          ipureintro
          (try refine ⟨rfl, ?_⟩); refine ⟨by word, by word, fun _ => by word⟩
      · iframe
        ipureintro; (try refine ⟨rfl, ?_⟩); exact ⟨by decide, by decide, fun h => absurd rfl h⟩
  iintro %v ⟨%hv, w, s, Hlive, %st, «$r0», %Hst⟩
  subst hv
  wp_auto
  -- the filters
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ w_ptr ↦ wpl ∗
      wpl ↦ (watcher.mk ksl endk flt st 0 0 0 false false false) ∗
      ∃ fcs : GoSlice, fcs_ptr ↦ fcs ∗ filtersImpl (GF := GF) fcs (filterFs flt)))) $$ [w «$r0» fcs]
  · wp_if_destruct
    · (try wp_auto)
      wp_apply wp_slice_literal
      rw [recv_eq_func_mk]
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      (try wp_auto)
      ihave Hnil : (slice.nil ↦* ([] : List GoFunc) : IProp GF) $$ []
      · iapply ownSlice_nil
      ihave Hnilc : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      wp_apply +noauto wp_slice_append $$ [$Hnil $Hnilc $Hosl] as %fsl ⟨Hfsl, -, -⟩
      imod ownSlice_persist _ _ _ $$ Hfsl with #Hfsl
      (try wp_auto)
      generalize hf : (func.mk BAnon (BNamed "e") _ : GoFunc) = f at *
      iframe
      isplitr
      · ipureintro; rfl
      iunfold filtersImpl
      rw [show filterFs (W64 1) = [fun ev => !ev.del] from by simp [filterFs]]
      iexists [f]
      simp only [List.nil_append]
      iframe #
      isplitr
      · ipureintro; rfl
      simp only [List.zip_cons_cons, List.zip_nil_left]
      iapply BigSepL.bigSepL_singleton.2
      · iunfold filterSpec
        iintro !> %e %ev %Φ' !> Hev HΦ'
        rw [← hf, ← recv_eq_func_mk]
        iunfold evIs at Hev
        icases Hev with ⟨%pp, %qq, %st', %uf, %sc, %Hnn, #Hept, -, -⟩
        iStructNamedSuffix Hept "E"
        wp_auto
        iapply HΦ'
        ipureintro
        unfold evType
        cases ev.del <;> rfl
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_apply wp_slice_literal
        rw [recv_eq_func_mk]
        (try wp_auto)
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        (try wp_auto)
        ihave Hnil : (slice.nil ↦* ([] : List GoFunc) : IProp GF) $$ []
        · iapply ownSlice_nil
        ihave Hnilc : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
        · iapply ownSliceCap_nil
        wp_apply +noauto wp_slice_append $$ [$Hnil $Hnilc $Hosl] as %fsl ⟨Hfsl, -, -⟩
        imod ownSlice_persist _ _ _ $$ Hfsl with #Hfsl
        (try wp_auto)
        generalize hf : (func.mk BAnon (BNamed "e") _ : GoFunc) = f at *
        iframe
        isplitr
        · ipureintro; rfl
        iunfold filtersImpl
        rw [show filterFs (W64 2) = [fun ev => ev.del] from by simp [filterFs]]
        iexists [f]
        simp only [List.nil_append]
        iframe #
        isplitr
        · ipureintro; rfl
        simp only [List.zip_cons_cons, List.zip_nil_left]
        iapply BigSepL.bigSepL_singleton.2
        · iunfold filterSpec
          iintro !> %e %ev %Φ' !> Hev HΦ'
          rw [← hf, ← recv_eq_func_mk]
          iunfold evIs at Hev
          icases Hev with ⟨%pp, %qq, %st', %uf, %sc, %Hnn, #Hept, -, -⟩
          iStructNamedSuffix Hept "E"
          wp_auto
          iapply HΦ'
          ipureintro
          unfold evType
          cases ev.del <;> rfl
      · iframe
        iunfold filtersImpl
        rw [show filterFs flt = [] from by unfold filterFs; rw [if_neg ‹¬flt = W64 1›, if_neg Hif]]
        rw [show (zero_val GoSlice) = slice.nil from rfl]
        iexists []
        ihave #Hnil : (slice.nil ↦*□ ([] : List GoFunc) : IProp GF) $$ []
        · iapply ownSlice_nil
        iframe #
        isplitr
        · ipureintro; rfl
        simp only [List.zip_nil_left]
        iapply BigSepL.bigSepL_nil.2; itrivial
  iintro %v ⟨%hv, w, «$r0», %fcsl, fcs, #Hflts⟩
  subst hv
  wp_auto
  ihave %Hsh := hsh.2.2.2 T.ws T.ep.ι.kv T.σs.ws $$ Hws
  obtain ⟨tyW, vW, hwsv, hWatch, -, -, -, -, -, -⟩ := Hsh
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold smuInv at HL
  icases HL with ⟨%rs, %W, %Hl, %P, HB⟩
  iunfold smuBody at HB
  icases HB with ⟨Hwm, ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩, Hevl, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revLo" T.ep.mp) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  imod revLo_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q $$ Hlive
    with ⟨%lo, Hlo, Hcl2⟩
  imodintro
  inext
  iexists lo
  iframe Hlo
  iintro Hlo
  imod Hcl2 $$ Hlo with ⟨Hlive, %nn, #Hnn, %Hlon⟩
  imodintro
  (try wp_auto)
  wp_apply wp_ctxTODO
  (try wp_auto)
  iunfold incLive at Hlive
  icases Hlive with ⟨-, Hret⟩
  have hkne : kk ≠ [] := Hkne kk Hkk
  rw [hwsv]
  (try wp_auto)
  wp_apply (hWatch T.ep.ι.kv T.σs.ws todoCtxVal
      { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }
      ksl endk fcsl kk e (filterFs flt) st (regQ' T q W wpl kk e endk st flt nn))
    $$ [Hrdr Hret Hcl Hreg] as %id %err ⟨Hrdr, Hres⟩
  · ihave #Hws2 : isMvccWatchStream (interface.mkOk tyW vW) T.ep.ι.kv T.σs.ws $$ []
    · rw [← hwsv]; iexact Hws
    iframe #
    iframe Hrdr
    isplitl []
    · ileft; ipureintro; rfl
    isplitl []
    · ipureintro; exact Hst.1
    iright
    iapply (register_au' hpers hreach T q W wpl kk e endk st flt nn hkne)
    iframe
    iframe #
  trace_state
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
