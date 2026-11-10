/- Lean-first (no Rocq counterpart). The proof of `stream.receive`: Draft, to come (`sorry`).

The callees in call order: `check`, `stream.covered`, `stream.expect`, `checkKV`, `choose`,
`context.TODO`, `Range` (through `shapes.law`), `checkStoreRange`; the facts from `recv_facts`
(`persistent`, `mvccState_reachable`, `wsRecv_ok`). The first check, `resp.Revision ≤ m.revHi`:
`readQ`'s `monoNatLbOwn m.nrev |σ.notifiedLog|` and `nrevHi_acc` at the load (`Int64.Load`) give
`|σ.notifiedLog| ≤ revHi + 1`, with clause 1's `r.rev < |σ.notifiedLog|`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkStoreRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__covered
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RecvLemmas

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

theorem stream.receive.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_stream_covered : stream.covered.spec (GF := GF) (hG := hG))
    (wp_stream_expect : stream.expect.spec (GF := GF) (hG := hG))
    (wp_checkKV : checkKV.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_runner_checkStoreRange : runner.checkStoreRange.spec (GF := GF) (hG := hG)) :
    stream.receive.spec (GF := GF) (hG := hG) := by
  intro T q rs r resp W Hl P
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  haveI := streamCtx_persistent hpers T
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  wp_start as ⟨#Hctx0, HB, Hhalf, Hwr, Hresp, Hrdr, Hlive, Hhr⟩
  ihave Hctx := Hctx0
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, #Hstop⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfg, #Hwa, #Hwst, #Cev, #Cpr, #Ccp, #Ccn⟩
  ihave #HhF : rF go!"h" T.ep.x ↦□ T.ep.h $$ []
  · iunfold runnerH at HrH; iexact HrH
  iunfold wrespIs at Hresp
  icases Hresp with ⟨%Hfl, %ps, #Hps, %Hpsl, #Hevs⟩
  iunfold smuBody at HB
  icases HB with ⟨Hwm, Hord, Hevl, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  ihave %Hrs := ghostVar_agree T.σs.rcv _ _ _ _ $$ Hrcv0 Hhalf
  imod recv_facts' hpers hreach hrok T q (rs ++ [r]) W $$ [$Hlive $Hinv $Hws $Hwr $Hreg]
    with ⟨Hlive, Hwr, Hreg, %σ, %S, %C, #Hq, %Hfacts⟩
  obtain ⟨Hro, Honce, HregOk, hwf, hnl⟩ := Hfacts
  iunfold readQ at Hq
  icases Hq with ⟨%Hlw, #Hlbw, #Lrev, #Lcrev, #Lnrev, %HqF⟩
  obtain ⟨Hh, Hreach, Hloglen⟩ := HqF
  -- the longer of the two lower bounds of the history
  ihave %Hcmp := mono_list_lb_valid T.ep.γh.l Hl Hlw $$ Hlb Hlbw
  obtain ⟨Hlx, hpx, hpwx, hx⟩ : ∃ Hlx, Hl <+: Hlx ∧ Hlw <+: Hlx ∧ (Hlx = Hlw ∨ Hlx = Hl) := by
    rcases Hcmp with hc | hc
    · exact ⟨Hlw, hc, List.prefix_refl _, Or.inl rfl⟩
    · exact ⟨Hl, List.prefix_refl _, hc, Or.inr rfl⟩
  ihave #Hlbx : monoListLbOwn T.ep.γh.l Hlx $$ []
  · rcases hx with rfl | rfl
    · iexact Hlbw
    · iexact Hlb
  have Hhx := histOkM_prefix Hh hpwx
  have hNL : σ.notifiedLog.length ≤ Hlx.length := Hhx.1
  imod ghostVar_update_halves (rs ++ [r]) T.σs.rcv _ _ $$ Hrcv0 Hhalf with ⟨Hrcv0, Hhalf⟩
  -- the response's facts
  have hrmem : r ∈ rs ++ [r] := by simp
  obtain ⟨hid, hevle, hcr0, hcrne, hm1, hpos⟩ := Hro.1 r hrmem
  have hlog2 : 2 ≤ σ.log.length := (reach_bounds σ Hreach).1
  have hnlog : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  ihave %Hpsn := ownSlice_len $$ Hps
  iunfold epLive at Hlive
  have hrevle : ∀ v : w64, (σ.notifiedLog.length : Int) ≤ sint.Z v + 1 →
      sint.Z r.rev ≤ sint.Z v := by
    intro v hv
    by_cases hc : r.compactRev = W64 0
    · have h1 := hcr0 hc
      have : sint.nat r.rev = (sint.Z r.rev).toNat := rfl
      omega
    · rw [(hcrne hc).2.2.1]; have : sint.Z (W64 0) = 0 := rfl; omega
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revHi" T.ep.mp) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  imod nrevHi_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q _ $$ [$Hlive $Lnrev]
    with ⟨%vh, Hvh, %Hvhb, Hcl⟩
  imodintro
  inext
  iexists vh
  iframe
  iintro Hvh
  imod Hcl $$ Hvh with Hlive
  imodintro
  wp_auto
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; rw [Hfl.2.1]; exact hrevle vh Hvhb.1
  (try wp_auto)
  -- the response is a registered watcher's, or the stream's
  have hknown' : rcvKnown' (rs ++ [r]) W := by
    intro r' hr' hne
    rcases List.mem_append.1 hr' with hr' | hr'
    · exact Hknown.1 r' hr' hne
    · rw [List.mem_singleton] at hr'; subst hr'; exact HregOk.1 _ _ (Option.get_mem (hid hne))
  have hlen0 : resp.Events'.len = W64 0 ↔ r.evs = [] := by
    rw [← List.length_eq_zero_iff, ← Hpsl, Hpsn.1]
    constructor
    · intro h; rw [h]; rfl
    · intro h; have := Hpsn.2; word
  have hrS : r.id ≠ W64 (-1) → ∃ wi x, S.ws !! r.id = some wi ∧ W !! r.id = some x ∧
      wi.rg = ⟨x.key, if x.endNil then none else some x.e, x.start, r.id⟩ ∧
      wi.fs = filterFs x.filter ∧ wi.lo = x.lo ∧ wi.k = x.k ∧
      (r.id ∉ C → wi.live = true) ∧ (r.id ∈ C → x.cm = true) := by
    intro hne
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (HregOk.1 _ _ (Option.get_mem (hid hne)))
    obtain ⟨wi, hwi, h⟩ := HregOk.2 _ _ hx
    exact ⟨wi, x, hwi, hx, h⟩
  icases wats_regs Hl rs T.σs.ws W $$ Hwats with ⟨Hwats, %HWr⟩
  have hjr : (rs ++ [r])[rs.length]? = some r := by simp
  -- a progress response's revision is not negative
  have hrev0 : r.evs = [] → r.compactRev = W64 0 → 0 ≤ sint.Z r.rev := by
    intro he hc
    by_cases hne : r.id = W64 (-1)
    · have := (hm1 hne).2.2; omega
    · obtain ⟨wi, x, hwi, hx, -, -, hlo, -⟩ := hrS hne
      have h4 := Hro.2.2.2.1 rs.length r r.id wi hjr he hc hwi (Or.inl rfl)
      have := (HWr _ _ hx).2.1
      omega
  -- the eventless revision
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ s_ptr ↦ T.s ∗ resp_ptr ↦ resp ∗
      ∃ P' : w64, sF go!"eventless" T.s ↦ P' ∗ ⌜eventlessOk (rs ++ [r]) P'⌝))) $$ [s resp Hevl]
  · by_cases hpe : r.evs = [] ∧ r.compactRev = W64 0
    · have hP : sint.Z P ≤ sint.Z r.rev := by
        rcases Hknown.2.2 with hP0 | ⟨i, y, hy, hye, hyc, hyr⟩
        · rw [hP0]; have := hrev0 hpe.1 hpe.2; exact this
        · have hi : i < rs.length := (List.getElem?_eq_some_iff.1 hy).1
          rw [← hyr]
          exact Hro.2.2.2.2 i rs.length y r hi (by rw [List.getElem?_append_left hi]; exact hy) hjr
            hye hpe.1 hpe.2
      rw [decide_eq_true (hlen0.2 hpe.1)]
      wp_auto
      rw [Hfl.2.2, decide_eq_true hpe.2]
      wp_auto
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]; rw [Hfl.2.1]; exact hP
      (try wp_auto)
      wp_apply_core sync.atomic.Int64.wp_Add (rF go!"progress" T.ep.x) (W64 1) $$ [] [-]
      · iPkgInit
      iunfold ctrInv at Cpr
      iinv Cpr with ⟨%a, >Ha⟩ Hclose
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "progress") from
        Std.LawfulSet.empty_subset)
      iintro Hcl
      inext
      iexists a
      iframe
      iintro Ha
      imod Hcl with -
      imod Hclose $$ [Ha] with -
      · inext; iexists _; iframe
      imodintro
      (try wp_auto)
      iframe
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨by rw [Hfl.2.1]; exact hrev0 hpe.1 hpe.2, Or.inr ⟨rs.length, r, hjr, hpe.1, hpe.2, ?_⟩⟩
      exact Hfl.2.1.symm
    · have hc : ¬ (resp.Events'.len = W64 0 ∧ resp.CompactRevision' = W64 0) := by
        rw [hlen0, Hfl.2.2]; exact hpe
      by_cases hl : resp.Events'.len = W64 0
      · rw [decide_eq_true hl]
        wp_auto
        have hc2 : resp.CompactRevision' ≠ W64 0 := fun h => hc ⟨hl, h⟩
        rw [decide_eq_false hc2]
        wp_auto
        iframe
        isplitr
        · ipureintro; rfl
        ipureintro
        exact eventlessOk_snoc r Hknown.2
      · rw [decide_eq_false hl]
        wp_auto
        iframe
        isplitr
        · ipureintro; rfl
        ipureintro
        exact eventlessOk_snoc r Hknown.2
  iintro %v ⟨%hv, s, resp, %P', Hevl, %HevOk⟩
  subst hv
  wp_auto
  have hnl1 : σ.notifiedLog.length ≤ σ.log.length + 1 := by
    unfold MvccState.notifiedLog; split <;> simp
  icases Hord with ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩
  rw [Hfl.1]
  by_cases hm : r.id = W64 (-1)
  · -- the stream's progress
    rw [decide_eq_true hm]
    obtain ⟨he, hc, hr1⟩ := hm1 hm
    wp_auto
    rw [decide_eq_true (hlen0.2 he)]
    wp_auto
    rw [Hfl.2.2, decide_eq_true hc]
    wp_auto
    wp_apply wp_check
    · ipureintro; simp only [decide_eq_true_eq]; rw [Hfl.2.1]; exact hr1
    (try wp_auto)
    have hrl : sint.nat r.rev < σ.notifiedLog.length := hcr0 hc
    have hrZ : sint.Z r.rev < Hlx.length := by
      have : sint.nat r.rev = (sint.Z r.rev).toNat := rfl; omega
    have hrM : sint.Z r.rev < 2 ^ 63 - 1 := by
      have : sint.nat r.rev = (sint.Z r.rev).toNat := rfl; omega
    have hsame : ∀ id, recvEvs (rs ++ [r]) id = recvEvs rs id :=
      fun id => recvEvs_snoc_ne _ _ _ (Or.inr he)
    ihave %Hlen := ownSlice_len $$ Hids
    ihave HI : (∃ (j : w64) (v0 : w64),
        "i" ∷ i_ptr ↦ j ∗ "id" ∷ id_ptr ↦ v0 ∗ "Hids" ∷ osl ↦* ids ∗
        "Hwm" ∷ T.wm ↦$ GMap.fmap Reg.wp W ∗ "Hhr" ∷ histRd T.ep.h T.ep.γh ∗
        "Hwats" ∷ ([∗map] id ↦ x ∈ W, watcherOwn' Hl rs T.σs.ws id x) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ : IProp GF) $$ [i id Hids Hwm Hwats Hhr]
    · iexists W64 0, _
      iframe
      ipureintro; constructor <;> word
    wp_for HI
    by_cases Hlt : sint.Z j < sint.Z osl.len
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hjl : sint.nat j < ids.length := by rw [Hlen.1]; word
      list_elem ids (sint.nat j) as wid
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨Hj.1, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index osl (sint.Z j) ids (DFrac.own 1) wid Hj.1 $$ [Hids] as Hids
      · iframe; ipureintro; exact Hwid_lookup
      (try wp_auto)
      obtain ⟨x, hx⟩ : ∃ x, W !! wid = some x := by
        have := (Hids.2 wid).1 (List.mem_of_getElem? Hwid_lookup)
        exact Option.isSome_iff_exists.1 this
      wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
        watcher.ty.PointerType T.wm (GMap.fmap Reg.wp W) wid (DFrac.own 1)) $$ [$Hwm] as Hwm
      rw [hx]
      simp only [Option.map_some, Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc
        (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs T.σs.ws id x) (m := W) hx)
        $$ Hwats with ⟨Hw, Hwats⟩
      iunfold watcherOwn' at Hw
      icases Hw with ⟨%wv, Hp, #Hk, #He, Hlbk, %Hok⟩
      (try wp_auto)
      have Hpos := Hok.2.2.2.2.2.2.2.2.2.2.2.2.2
      have Hposx := wPosOk'_prefix hpx _ _ _ _ Hpos
      have hr0 : 0 ≤ sint.Z wv.rev' := Hpos.1
      have hi0 : 0 ≤ sint.Z wv.index' := Hpos.2.1
      have hcov : wv.stamped' = true → wv.cancelled' = false →
          expNext Hlx (matchesM wv.filter' (decide (wv.end' = slice.nil)) x.key x.e)
            (sint.nat wv.rev') (sint.nat wv.index') (sint.Z r.rev) = none := by
        intro hst hcn
        obtain ⟨hen, hkk, hfl, -, -, -, hlo1, -, -, -, hcm, hstk, -, -⟩ := Hok
        obtain ⟨wi, hwi, hrg, hfs, hlo, hk, hlive, hcmC⟩ := HregOk.2 wid x hx
        have hnC : wid ∉ C := fun hC => by have := hcmC hC; rw [← hcm, hcn] at this; cases this
        have hprog := recv_prog' T.ep.ks σ S (rs ++ [r]) Hlx Hro Hhx Honce hwf hnl rs.length r hjr he
          hc wid x wi hwi hrg hfs hlo wv.end' hen hkk hlo1
          (Or.inr ⟨hm, hlive hnC, by rw [hk]; exact hstk hst⟩)
        rw [List.take_of_length_le (by simp), hsame] at hprog
        rw [hfl, ← Reg.mt_eq x wv.end' hen]
        refine covered_none Hlx x.mt x.lo wv _ (sint.Z r.rev) hlo1 Hposx ?_
        rw [show (sint.Z r.rev).toNat = sint.nat r.rev from rfl, hprog, List.length_map]; exact Nat.le_refl _
      cases hst : wv.stamped'
      · (try rw [hst])
        (try wp_auto)
        ihave Hwats := Hwats $$ [Hp Hlbk]
        · iunfold watcherOwn'
          iexists wv
          iframe
          iframe #
          ipureintro; exact Hok
        wp_for_post
        iframe
        iexists j + W64 1, wid
        iframe
        ipureintro; constructor <;> word
      · (try rw [hst])
        (try wp_auto)
        cases hcn : wv.cancelled'
        · (try rw [hcn])
          (try wp_auto)
          rw [Hfl.2.1]
          wp_apply (wp_stream_covered T.s T.ep.x T.ep.h T.ep.γh Hlx x.wp wv x.key x.e r.rev _
              (DFrac.own 1) DFrac.discard DFrac.discard hr0 hi0 hrZ hrM (hcov hst hcn))
            $$ [Hp Hhr] as ⟨Hp, -, -, Hhr⟩
          · iframe Hp Hhr
            iframe #
          (try wp_auto)
          ihave Hwats := Hwats $$ [Hp Hlbk]
          · iunfold watcherOwn'
            iexists wv
            iframe
            iframe #
            ipureintro; exact Hok
          wp_for_post
          iframe
          iexists j + W64 1, wid
          iframe
          ipureintro; constructor <;> word
        · (try rw [hcn])
          (try wp_auto)
          ihave Hwats := Hwats $$ [Hp Hlbk]
          · iunfold watcherOwn'
            iexists wv
            iframe
            iframe #
            ipureintro; exact Hok
          wp_for_post
          iframe
          iexists j + W64 1, wid
          iframe
          ipureintro; constructor <;> word
    · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      ihave Hwats := wats_frame' hpx rs r T.σs.ws W hsame $$ Hwats
      iapply HΦ
      iexists Hlx, P'
      iunfold smuBody
      iframe
      iframe #
      ipureintro; exact ⟨Hids, hknown', HevOk⟩
  · rw [decide_eq_false hm]
    wp_auto
    obtain ⟨wi, x, hwi, hx, hrg, hfs, hlo, hk, hlive, hcmC⟩ := hrS hm
    have hsame : ∀ id, id ≠ r.id → recvEvs (rs ++ [r]) id = recvEvs rs id :=
      fun id hne => recvEvs_snoc_ne _ _ _ (Or.inl (Ne.symm hne))
    rw [Hfl.1]
    wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
      watcher.ty.PointerType T.wm (GMap.fmap Reg.wp W) r.id (DFrac.own 1)) $$ [$Hwm] as Hwm
    rw [hx]
    simp only [Option.map_some, Option.getD_some]
    icases (wats_take' hpx rs r T.σs.ws W r.id x hx hsame) $$ Hwats with ⟨Hwo, Hback⟩
    iunfold watcherOwn' at Hwo
    icases Hwo with ⟨%wv, Hwp, #Hk, #He, Hlbk, %Hok⟩
    icases (typedPointsto_not_null_dup _ _ _) $$ Hwp with ⟨Hwp, %Hwpn⟩
    have Hok0 := Hok
    obtain ⟨hen, hkk, hfl, hstart, hst0, hstM, hlo1, hloM, hstlo, hstfl, hcm, hstk, hcpk, Hpos⟩ := Hok
    have Hposx := wPosOk'_prefix hpx _ _ _ _ Hpos
    (try wp_auto)
    rw [decide_eq_false Hwpn]
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; rfl
    (try wp_auto)
    rw [Hfl.2.2]
    by_cases hc : r.compactRev = W64 0
    · rw [decide_eq_true hc]
      (try wp_auto)
      have hrl : sint.nat r.rev < σ.notifiedLog.length := hcr0 hc
      have hrZ : sint.Z r.rev < Hlx.length := by
        have : sint.nat r.rev = (sint.Z r.rev).toNat := rfl; omega
      have hrM : sint.Z r.rev < 2 ^ 63 - 1 := by
        have : sint.nat r.rev = (sint.Z r.rev).toNat := rfl; omega
      by_cases he : r.evs = []
      · -- the watcher's progress
        rw [decide_eq_true (hlen0.2 he)]
        have hr0 := hrev0 he hc
        have h4 := Hro.2.2.2.1 rs.length r r.id wi hjr he hc hwi (Or.inl rfl)
        rw [hlo] at h4
        have hstle : sint.Z wv.start' ≤ sint.Z r.rev + 1 := by
          rw [hstart]
          by_cases h0 : x.start = W64 0
          · rw [h0]; have : sint.Z (W64 0) = 0 := rfl; omega
          · have := hstlo h0
            have : sint.nat x.start = (sint.Z x.start).toNat := rfl
            omega
        have hflle : 0 < sint.Z wv.floatLo' → sint.Z wv.floatLo' ≤ sint.Z r.rev + 1 := by
          intro hf
          have h5 := Hpos.2.2.2.2
          rw [if_pos hf] at h5
          omega
        (try wp_auto)
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ w_ptr ↦ x.wp ∗ x.wp ↦ wv ∗
            ∃ lw : w64, lower_ptr ↦ lw ∗ ⌜sint.Z lw ≤ sint.Z r.rev + 1⌝))) $$ [lower Hwp w]
        · wp_if_destruct
          · iframe
            ipureintro; exact hflle (by have := hst0; rw [← hstart] at this; omega)
          · iframe
            ipureintro; exact hstle
        iintro %v ⟨%hv, w, Hwp, %lw, lower, %Hlw⟩
        subst hv
        wp_auto
        wp_apply wp_check
        · ipureintro; simp only [decide_eq_true_eq]; rw [Hfl.2.1]; word
        (try wp_auto)
        have hsr : recvEvs (rs ++ [r]) r.id = recvEvs rs r.id := recvEvs_snoc_ne _ _ _ (Or.inr he)
        have hprog := recv_prog' T.ep.ks σ S (rs ++ [r]) Hlx Hro Hhx Honce hwf hnl rs.length r hjr he
          hc r.id x wi hwi hrg hfs hlo wv.end' hen hkk hlo1 (Or.inl rfl)
        rw [List.take_of_length_le (by simp), hsr] at hprog
        have hnone : expNext Hlx (matchesM wv.filter' (decide (wv.end' = slice.nil)) x.key x.e)
            (sint.nat wv.rev') (sint.nat wv.index') (sint.Z r.rev) = none := by
          rw [hfl, ← Reg.mt_eq x wv.end' hen]
          refine covered_none Hlx x.mt x.lo wv _ (sint.Z r.rev) hlo1 Hposx ?_
          rw [show (sint.Z r.rev).toNat = sint.nat r.rev from rfl, hprog, List.length_map]
          exact Nat.le_refl _
        rw [Hfl.2.1]
        wp_apply (wp_stream_covered T.s T.ep.x T.ep.h T.ep.γh Hlx x.wp wv x.key x.e r.rev _
            (DFrac.own 1) DFrac.discard DFrac.discard Hposx.1 Hposx.2.1 hrZ hrM hnone)
          $$ [Hwp Hhr] as ⟨Hwp, -, -, Hhr⟩
        · iframe Hwp Hhr
          iframe #
        (try wp_auto)
        ihave Hwats := Hback $$ [Hwp Hlbk]
        · iunfold watcherOwn'
          iexists wv
          iframe
          iframe #
          ipureintro; exact watcherOk_frame hpx rs r r.id x wv hsr Hok0
        iapply HΦ
        iexists Hlx, P'
        iunfold smuBody
        iframe
        iframe #
        ipureintro; exact ⟨Hids, hknown', HevOk⟩
      · sorry
    · -- a compaction response
      rw [decide_eq_false hc]
      obtain ⟨he, -, hr0, hcp, hcle⟩ := hcrne hc
      (try wp_auto)
      rw [decide_eq_true (hlen0.2 he)]
      (try wp_auto)
      rw [Hfl.2.1, hr0]
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; rfl
      (try wp_auto)
      rw [Hfl.2.2]
      (try wp_auto)
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z r.compactRev from hcp)]
      (try wp_auto)
      wp_apply_core sync.atomic.Int64.wp_Load (mF go!"cmpHi" T.ep.mp) (DFrac.own 1) $$ [] [-]
      · iPkgInit
      imod cmpHi_acc T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv q _ $$ [$Hlive $Lcrev]
        with ⟨%vc, Hvc, %Hvcb, Hcl⟩
      imodintro
      inext
      iexists vc
      iframe
      iintro Hvc
      imod Hcl $$ Hvc with Hlive
      imodintro
      (try wp_auto)
      wp_apply wp_check
      · ipureintro
        have := Int.self_le_toNat (σ.crev + 1)
        simp only [decide_eq_true_eq]
        rw [Hfl.2.2]
        omega
      (try wp_auto)
      wp_apply_core sync.atomic.Int64.wp_Add (rF go!"compacted" T.ep.x) (W64 1) $$ [] [-]
      · iPkgInit
      iunfold ctrInv at Ccp
      iinv Ccp with ⟨%a, >Ha⟩ Hclose
      all_goals (try exact (fun _ _ => CoPset.mem_full))
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "compacted") from
        Std.LawfulSet.empty_subset)
      iintro Hcl
      inext
      iexists a
      iframe
      iintro Ha
      imod Hcl with -
      imod Hclose $$ [Ha] with -
      · inext; iexists _; iframe
      imodintro
      (try wp_auto)
      ihave Hwats := Hback $$ [Hwp Hlbk]
      · iunfold watcherOwn'
        iexists { wv with compacted' := true }
        iframe
        iframe #
        ipureintro
        refine ⟨hen, hkk, hfl, hstart, hst0, hstM, hlo1, hloM, hstlo, hstfl, hcm, ?_, ?_, ?_⟩
        · intro h; have := hstk h; simp; omega
        · intro _; exact ⟨r, by simp, rfl, hc⟩
        · rw [recvEvs_snoc_ne _ _ _ (Or.inr he)]; exact Hposx
      iapply HΦ
      iexists Hlx, P'
      iunfold smuBody
      iframe
      iframe #
      ipureintro; exact ⟨Hids, hknown', HevOk⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
