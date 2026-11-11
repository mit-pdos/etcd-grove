/- Lean-first (no Rocq counterpart). The proof of `stream.watch` (proved).

The callees in call order: the `regs` counter (`ctrInv`), `genKey`, `genEnd`, `choose`, `pick`
(the start's weights; `revHi_acc` or `WatchLemmas.cmpLo_acc_lt` for the start's bound), the filter
closures (each its `filterSpec`, over mvcc's `evIs`), `s.mu`, `revLo_acc`, `context.TODO`, `Watch`
(through `shapes.law`) with `WatchLemmas.register_au'`'s update, `revHi_acc` at the registered
state's revision, `check`s, the watcher's position (floating in `[revLo + 1, revHi + 1]`, or at its
start, nothing received: `recvEvs_fresh'`), the map and the order slice, `s.mu`'s release with the
new entry (`watcherOwn'`, its fragment in `regLock`).
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
  icases Hres with (⟨%Hc, -⟩ | ⟨-, %σ, %S, HQ, Herr⟩)
  · exfalso
    rcases Hend with h | h
    · exact Hc.1 h
    · exact Hc.2.1 h
  iunfold regQ' at HQ
  icases HQ with ⟨Hret, Hcl, %HQ, #Lrev, %k, #Hk, Hreg⟩
  obtain ⟨hSo, hWid, hid1, hnσ, hlog2, hlogM⟩ := HQ
  rw [hSo]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herr with %Herr
  subst Herr
  ihave Hlive : incLive (GF := GF) T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q $$ [Hret]
  · iunfold incLive; iframe; iframe #
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revHi" T.ep.mp) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  imod revHi_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q _ $$ [$Hlive $Lrev]
    with ⟨%hi, Hvh, %Hhib, Hcl2⟩
  imodintro
  inext
  iexists hi
  iframe Hvh
  iintro Hvh
  imod Hcl2 $$ Hvh with Hlive
  imodintro
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; rfl
  (try wp_auto)
  wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    watcher.ty.PointerType T.wm (GMap.fmap Reg.wp W) id (DFrac.own 1)) $$ [$Hwm] as Hwm
  rw [hWid]
  simp only [Option.map_none, Option.getD_none]
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  -- the watcher's position: floating from `0`, or at its start
  have hfresh : recvEvs rs id = [] := recvEvs_fresh' Hknown.1 hWid hid1
  have hrevσ : (σ.rev : Int) = σ.log.length - 1 := by unfold MvccState.rev; omega
  have hx1 : 1 ≤ watchLo σ st ∧ watchLo σ st < 2 ^ 63 - 1 ∧
      (st ≠ W64 0 → watchLo σ st = sint.nat st) := by
    unfold watchLo
    by_cases h0 : st = W64 0
    · rw [if_pos h0]; exact ⟨by omega, by omega, fun h => absurd h0 h⟩
    · rw [if_neg h0]
      have := Hst.2.2 h0
      have : sint.nat st = (sint.Z st).toNat := rfl
      exact ⟨by omega, by have := Hst.2.1; omega, fun _ => rfl⟩
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ w_ptr ↦ wpl ∗
      ∃ wv : watcher, wpl ↦ wv ∗ ⌜wv.key' = ksl ∧ wv.end' = endk ∧
        watcherOk Hl rs id (regOf wpl kk e endk st flt (watchLo σ st) k) wv⌝))) $$ [w «$r0» lo hi]
  · wp_if_destruct
    · -- floating in `[revLo + 1, revHi + 1]`
      have hlo1 : sint.Z (lo + W64 1) = sint.Z lo + 1 := by
        have : sint.Z lo ≤ nn := Hlon.2; have : (nn : Int) ≤ σ.rev := by exact_mod_cast hnσ
        word
      have hhi1 : sint.Z (hi + W64 1) = sint.Z hi + 1 := by have := Hhib.2; word
      have hwl : watchLo σ (W64 0) = σ.log.length := by unfold watchLo; rw [if_pos rfl]
      iframe
      ipureintro
      refine ⟨rfl, rfl, ?_⟩
      unfold watcherOk
      refine ⟨rfl, hkne, rfl, rfl, ?_, ?_, hx1.1, hx1.2.1, hx1.2.2, ?_, rfl, ?_, ?_, ?_⟩
      · simp only [regOf]; word
      · simp only [regOf]; word
      · intro h; exact absurd rfl h
      · intro h; cases h
      · intro h; cases h
      rw [hfresh]
      simp only [List.length_nil]
      have hl1 : 1 ≤ sint.Z lo := Hlon.1
      have hhM := Hhib.2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only; omega
      · simp only; decide
      · simp only; omega
      · simp only; omega
      simp only
      rw [if_pos (by omega)]
      refine ⟨by first | trivial | rfl, by first | trivial | rfl, ?_, ?_⟩
      · simp only [regOf]; rw [hwl, hlo1]
        have : sint.Z lo ≤ nn := Hlon.2; have : (nn : Int) ≤ σ.rev := by exact_mod_cast hnσ
        omega
      · simp only [regOf]; rw [hwl, hhi1]; have := Hhib.1; omega
    · -- at its start
      iframe
      ipureintro
      have hlo := hx1.2.2 Hif
      refine ⟨rfl, rfl, ?_⟩
      unfold watcherOk
      refine ⟨rfl, hkne, rfl, rfl, Hst.1, ?_, hx1.1, hx1.2.1, hx1.2.2, fun _ => rfl, rfl, ?_, ?_, ?_⟩
      · have := Hst.2.1; simp only [regOf]; omega
      · intro h; cases h
      · intro h; cases h
      rw [hfresh]
      simp only [List.length_nil]
      have hs2 := Hst.2.1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only; exact Hst.1
      · simp only; decide
      · simp only; decide
      · simp only; omega
      simp only
      rw [if_neg (by decide)]
      simp only [regOf, Reg.mt]
      rw [hlo]
      exact ⟨posOk_start _ _ _, Or.inr ⟨by first | trivial | rfl, by first | trivial | rfl,
        by first | trivial | rfl⟩⟩
  iintro %v ⟨%hv, w, %wv, «$r0», %Hwv⟩
  subst hv
  (try wp_auto)
  obtain ⟨hwk, hwe, Hok⟩ := Hwv
  wp_apply wp_mapInsert $$ [$Hwm] as Hwm
  rw [show <[id := wpl]> (GMap.fmap Reg.wp W) =
      GMap.fmap Reg.wp (<[id := regOf wpl kk e endk st flt (watchLo σ st) k]> W) by
    rw [GMap.fmap_insert]; rfl]
  (try wp_auto)
  wp_apply wp_slice_literal
  (try wp_auto)
  isplitr
  · ipureintro; rfl
  iintro %isl ⟨Hisl, -⟩
  (try wp_auto)
  wp_apply +noauto wp_slice_append $$ [$Hids $Hcap $Hisl] as %osl' ⟨Hids, Hcap, -⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T)
    $$ [$Hmu $Hlocked Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats «$r0»]
  · iunfold smuInv
    iexists rs, <[id := regOf wpl kk e endk st flt (watchLo σ st) k]> W, Hl, P
    iunfold smuBody
    iframe
    iframe #
    isplitr
    · ipureintro
      have hnin : id ∉ ids := fun h => by have := (Hids.2 id).1 h; rw [hWid] at this; cases this
      refine ⟨List.nodup_append.2 ⟨Hids.1, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩, fun id' => ?_⟩
      · intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; exact fun h => hnin (h ▸ ha)
      · rw [List.mem_append, List.mem_singleton, Hids.2 id']
        by_cases he : id' = id
        · subst he; rw [GMap.lookup_insert]; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]; simp [he]
    isplitr
    · ipureintro; exact ⟨rcvKnown'_insert Hknown.1 _ _, Hknown.2⟩
    iapply BigSepM.bigSepM_insert hWid
    iframe
    iunfold watcherOwn'
    iexists wv
    simp only [regOf]
    rw [hwk, hwe]
    iframe
    iframe #
    ipureintro; exact Hok
  (try wp_auto)
  iapply HΦ
  iunfold regOwn
  iframe
  iapply (epRd_split T.ep q).2
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
