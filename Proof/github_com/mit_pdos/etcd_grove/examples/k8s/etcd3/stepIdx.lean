/-
Lean-first (no Rocq counterpart).

The proof of `stepIdx`: not a watch, `step`; a watch, the memo's verdict for its key (a hit: the
entry's `wentry`, on the same history, `HWf_eq`) or `watchOkIdx`'s (a miss: stored, `wentries_insert`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.stepIdx
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.step
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOkIdx
public import Perennial.Spec.sync.Mutex__Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- The end of a watch: `nil`, or `[c]`, by `watchOkL`'s verdict on `g`. -/
local macro "stepIdx_tail" : tactic => `(tactic| (
  cases hq : watchOkL x y g.st
  · try wp_auto
    rw [show stepL g x (plainOut y) = [] by
      rw [stepL, if_pos hW, show watchOkL x (plainOut y) g.st = watchOkL x y g.st from rfl, hq]; rfl]
    ihave Hn := ownSlice_nil (V := mcfg) (GF := GF) (DFrac.own 1)
    iapply HΦ
    isplitl [Hn]
    · iexact Hn
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
      iempintro
  · try wp_auto
    wp_apply wp_slice_literal (l := [c])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl1, _⟩
    wp_auto
    iapply HΦ
    rw [show stepL g x (plainOut y) = [g] by
      rw [stepL, if_pos hW, show watchOkL x (plainOut y) g.st = watchOkL x y g.st from rfl, hq]; rfl]
    iframe
    iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
    iexact Hc))

theorem stepIdx.wp_proof (wp_step : step.spec (GF := GF) (hG := hG))
    (wp_watchOkIdx : watchOkIdx.spec (GF := GF) (hG := hG)) :
    stepIdx.spec (GF := GF) (hG := hG) := by
  intro memo c g x y
  wp_start as ⟨#Hm, #Hc, %Hb⟩
  wp_auto
  by_cases hW : x.Kind' = W64 5
  case neg =>
    rw [show decide (x.Kind' = W64 5) = false by simpa using hW]
    try wp_auto
    wp_apply wp_step c g x y $$ [$Hc]
    · ipureintro; exact ⟨Hb.1, Hb.2.1, Hb.2.2.1, Hb.2.2.2.1⟩
    iintro %r %cs Hr
    try wp_auto
    iapply HΦ
    iexact Hr
  rw [show decide (x.Kind' = W64 5) = true by simpa using hW]
  try wp_auto
  obtain ⟨hrv, hmin⟩ := Hb.2.2.2.1 hW
  have hwf := Hb.2.2.2.2 hW
  ihave #Hm' : memoOwn (GF := GF) memo $$ [Hm]
  · iexact Hm
  iunfold memoOwn at Hm'
  icases Hm' with ⟨#Hsync, #Hmu⟩
  wp_apply (sync.Mutex.wp_Lock _ (wmemoInv memo)) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  iunfold wmemoInv at HR
  icases HR with ⟨%mm, %M, Hmf, HM, #HE⟩
  try wp_auto
  have hlen : g.st.hist.length < 2 ^ 63 := by
    have := hwf.1; rw [this]; word
  have hlen64 : g.st.hist.length < 2 ^ 64 := by omega
  wp_apply (wp_map_lookup2 (K := wkey) (V := Bool) wkey.ty go.bool mm M
    { hist' := c.hist', in' := x, evs' := y.WEvents', fail' := y.WFailed' } (DFrac.own 1))
    $$ [$HM] as HM
  cases hMk : M !! ({ hist' := c.hist', in' := x, evs' := y.WEvents', fail' := y.WFailed' } : wkey) with
  | some v =>
    -- a hit: the entry is `watchOkL`'s verdict on `g`'s history
    ihave #Hv := BigSepM.bigSepM_lookup (Φ := fun k v => wentry (GF := GF) k v) (m := M) hMk $$ [HE]
    · iexact HE
    iunfold wentry at Hv
    icases Hv with ⟨%H, #Hh, %Hok⟩
    ihave #Hc' : cfgOwn (GF := GF) c g $$ [Hc]
    · iexact Hc
    iunfold cfgOwn at Hc'
    icases Hc' with ⟨-, #Hch, -, -⟩
    icases histOwn_agree_len _ _ _ (by have := Hok.1.1; word) hlen64 $$ Hh Hch with %Hhist
    have hH : H = g.st := HWf_eq Hok.1 hwf Hhist
    have hv : v = watchOkL x y g.st := by rw [← hH]; exact Hok.2 y rfl rfl
    subst hv
    simp only [Option.getD_some, Option.isSome_some]
    try wp_auto
    wp_apply (sync.Mutex.wp_Unlock _ (wmemoInv memo)) $$ [Hlocked Hmf HM]
    · iframe #
      iframe Hlocked
      inext
      iunfold wmemoInv
      iexists mm, M
      iframe
      iframe #
    try wp_auto
    stepIdx_tail
  | none =>
    -- a miss: `watchOkIdx`'s verdict, stored
    simp only [Option.getD_none, Option.isSome_none]
    try wp_auto
    wp_apply (sync.Mutex.wp_Unlock _ (wmemoInv memo)) $$ [Hlocked Hmf HM]
    · iframe #
      iframe Hlocked
      inext
      iunfold wmemoInv
      iexists mm, M
      iframe
      iframe #
    try wp_auto
    wp_apply wp_watchOkIdx x y c g hlen hrv hmin $$ []
    · iframe #
    try wp_auto
    wp_apply (sync.Mutex.wp_Lock _ (wmemoInv memo)) $$ [] as ⟨Hlocked, HR⟩
    · iframe #
    iunfold wmemoInv at HR
    icases HR with ⟨%mm2, %M2, Hmf, HM, #HE2⟩
    try wp_auto
    wp_apply (wp_mapInsert wkey.ty mm2 M2
      ({ hist' := c.hist', in' := x, evs' := y.WEvents', fail' := y.WFailed' } : wkey)
      (watchOkL x y g.st)) $$ [$HM] as HM
    try wp_auto
    ihave #Hc' : cfgOwn (GF := GF) c g $$ [Hc]
    · iexact Hc
    iunfold cfgOwn at Hc'
    icases Hc' with ⟨-, #Hch, -, -⟩
    ihave #Hent : wentry (GF := GF)
        ({ hist' := c.hist', in' := x, evs' := y.WEvents', fail' := y.WFailed' } : wkey)
        (watchOkL x y g.st) $$ []
    · iunfold wentry
      iexists g.st
      iframe #
      ipureintro
      exact ⟨hwf, fun y' he hf => watchOkL_out x y y' g.st he.symm hf.symm⟩
    ihave #HE3 := wentries_insert (GF := GF) M2
      ({ hist' := c.hist', in' := x, evs' := y.WEvents', fail' := y.WFailed' } : wkey)
      (watchOkL x y g.st) $$ Hent HE2
    wp_apply (sync.Mutex.wp_Unlock _ (wmemoInv memo)) $$ [Hlocked Hmf HM]
    · iframe #
      iframe Hlocked
      inext
      iunfold wmemoInv
      iexists mm2, _
      iframe
      iexact HE3
    try wp_auto
    stepIdx_tail

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
