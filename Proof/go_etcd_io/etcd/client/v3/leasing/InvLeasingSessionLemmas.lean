/-
Lemmas for the session monitor (`monitorSession`, `kv.go`): the cache's reset (a fresh entries
map, every entry frozen) and the session monitor's halves of the `session` and `sessionc` fields
joined with the lock's (`leasingXBody`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## The reset -/

section pure
variable [ext : FfiSyntax]

/-- **The session monitor's reset** of the cache (`lkv.leases.entries = make(map...)`): the
entries map becomes the fresh map `m`, empty, and every entry is frozen (a `Get` that found one
may still read it). Nothing else changes. -/
def LeaseCacheSt.reset (m : GoMap) (st : LeaseCacheSt) : LeaseCacheSt :=
  { st with emap := m, entries := ∅, frozen := st.entries.toList ++ st.frozen }

theorem reset_wf {st : LeaseCacheSt} (hwf : LeaseCacheWf st) (m : GoMap) :
    LeaseCacheWf (st.reset m) where
  li_inj k1 k2 e1 e2 h1 _ _ := by simp [LeaseCacheSt.reset] at h1
  li_not_frozen k e h := by simp [LeaseCacheSt.reset] at h
  installed k li h := by
    right
    rcases hwf.installed k li h with ⟨e, he, hl⟩ | ⟨e, he, hl⟩
    · exact ⟨e, List.mem_append_left _ ((GMap.mem_toList _ _ _).2 he), hl⟩
    · exact ⟨e, List.mem_append_right _ he, hl⟩
  entries_installed k e h := by simp [LeaseCacheSt.reset] at h
  li_ne k e h := by simp [LeaseCacheSt.reset] at h
  empty_if_nil _ := rfl

end pure

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- The reset keeps every entry's facts (now a frozen entry's). -/
theorem lcFacts_reset (pfx : GoString) (st : LeaseCacheSt) (m : GoMap) :
    lcFacts (GF := GF) pfx st ⊢ lcFacts pfx (st.reset m) := by
  unfold lcFacts
  iintro ⟨Hm, Hf⟩
  simp only [LeaseCacheSt.reset]
  isplitl []
  · iapply BigSepM.bigSepM_empty.2; itrivial
  ihave Hm' := (BigSepM.bigSepM_toList (Φ := fun k e => entryFacts (GF := GF) pfx k e)).1 $$ Hm
  iapply BigSepL.bigSepL_append.2
  iframe Hf
  iexact Hm'

/-- **The reset's resources**: the entries field, and the way back for the fresh empty map `m`
(the entries' resources made read-only for the frozen list; the old map's dropped). -/
theorem lcOwn_reset (lc : Loc) (st : LeaseCacheSt) :
    lcOwn (GF := GF) lc st (DFrac.own 1) ⊢
      structFieldRef leaseCache go!"entries" lc ↦ st.emap ∗
      (∀ m : GoMap, structFieldRef leaseCache go!"entries" lc ↦ m -∗
        m ↦$ (∅ : GMap GoString Loc) ==∗ lcOwn lc (st.reset m) (DFrac.own 1)) := by
  unfold lcOwn
  iintro ⟨H1, -, H3, H4, H5, #H6, Hents, #H8⟩
  iframe H1
  iintro %m H1 Hm
  ihave %Hnn := ownMap_not_nil m _ _ $$ Hm
  ihave Hl := (BigSepM.bigSepM_toList (Φ := fun _ e => entryOwn (GF := GF) e (DFrac.own 1))).1
    $$ Hents
  imod (dfractional_big_sepL (l := st.entries.toList)
      (Ψ := fun _ kv dq => entryOwn (GF := GF) kv.2 dq)).dfractional_persist (DFrac.own 1)
    $$ Hl with #Hl
  imodintro
  simp only [LeaseCacheSt.reset]
  isplitl [H1]
  · iexact H1
  isplitl [Hm]
  · unfold emapOwn
    simp only [Hnn, ↓reduceIte, LeaseCacheSt.lis, GMap.fmap_empty]
    iexact Hm
  isplitl [H3]
  · iexact H3
  isplitl [H4]
  · iexact H4
  isplitl [H5]
  · iexact H5
  isplitl []
  · iexact H6
  isplitl []
  · iapply BigSepM.bigSepM_empty.2; itrivial
  iapply BigSepL.bigSepL_append.2
  iframe #

/-- The reset makes the map: its readiness is `1`. -/
theorem reset_readyN (st : LeaseCacheSt) (m : GoMap) (h : m ≠ map.nil) :
    (st.reset m).readyN = 1 := by
  simp [LeaseCacheSt.readyN, LeaseCacheSt.reset, h]

theorem readyN_le (st : LeaseCacheSt) : st.readyN ≤ 1 := by
  unfold LeaseCacheSt.readyN; split <;> omega

/-! ## The session monitor's halves -/

/-- Two halves of a points-to make the whole, with agreement. -/
theorem loc_halves (l : Loc) (v w : Loc) :
    typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
      typedPointsto l w (DFrac.own (1 : Qp).half) ⊢ ⌜v = w⌝ ∗ typedPointsto l w (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hc
  obtain ⟨-, rfl⟩ := Hc
  isplitr
  · ipureintro; rfl
  have hf := (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf
  iapply hf.2
  iframe

theorem chan_halves (l : Loc) (v w : GoChan) :
    typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
      typedPointsto l w (DFrac.own (1 : Qp).half) ⊢ ⌜v = w⌝ ∗ typedPointsto l w (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hc
  obtain ⟨-, rfl⟩ := Hc
  isplitr
  · ipureintro; rfl
  have hf := (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf
  iapply hf.2
  iframe

theorem loc_split (l : Loc) (v : Loc) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  have hf := (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf
  exact hf.1

theorem chan_split (l : Loc) (v : GoChan) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  have hf := (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf
  exact hf.1

/-- **The session monitor under the whole lock**: the KV's part for `st` and the monitor's halves
(`s`, `sc`) give the two fields whole, and the way back for new values `s'` (a session counter not
going down), `sc'` and a new state `st'` of the log (a step `st → st'`, which may repeat `st`),
the monitor keeping its halves, with `sessN s'` as a lower bound of the session counter. -/
theorem leasingX_monitor_open (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt) (s : Loc)
    (sc : GoChan) :
    leasingX (GF := GF) lkv γ st 1 ∗
      structFieldRef leasingKV go!"session" lkv ↦{DFrac.own (1 : Qp).half} s ∗
      structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own (1 : Qp).half} sc ⊢
    structFieldRef leasingKV go!"session" lkv ↦ s ∗
      structFieldRef leasingKV go!"sessionc" lkv ↦ sc ∗
      (∀ (s' : Loc) (sc' : GoChan) (st' : LeaseCacheSt), ⌜sessN s ≤ sessN s'⌝ -∗
        □ sessionOk γ s' -∗ □ sessioncOk γ sc' -∗
        structFieldRef leasingKV go!"session" lkv ↦ s' -∗
        structFieldRef leasingKV go!"sessionc" lkv ↦ sc' ==∗
        leasingX lkv γ st' 1 ∗
          structFieldRef leasingKV go!"session" lkv ↦{DFrac.own (1 : Qp).half} s' ∗
          structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own (1 : Qp).half} sc' ∗
          leasingStep γ st st' ∗ monoNatLbOwn γ.sess (sessN s')) := by
  unfold leasingX leasingXBody
  iintro ⟨⟨%x, Hs, Hsc, Hl, %Hlast, Hn, #Hso, #Hsco⟩, Hs2, Hsc2⟩
  obtain ⟨xs, xsc, xl⟩ := x
  simp only at Hlast
  icases loc_halves _ xs s $$ [$Hs $Hs2] with ⟨%h1, Hs⟩
  icases chan_halves _ xsc sc $$ [$Hsc $Hsc2] with ⟨%h2, Hsc⟩
  subst h1 h2
  iframe Hs Hsc
  iintro %s' %sc' %st' %Hle #Hso' #Hsco' Hs Hsc
  imod monoListAuthOwn_update_app (γ := γ.log) [st'] $$ Hl with ⟨Hl, #Hlb⟩
  imod mono_nat_own_update (sessN s') Hle $$ Hn with ⟨Hn, #Hnlb⟩
  have hne : xl ≠ [] := by intro h; rw [h] at Hlast; simp at Hlast
  have hi2 : (xl ++ [st'])[xl.length - 1 + 1]? = some st' := by
    have := List.length_pos_iff.mpr hne
    rw [show xl.length - 1 + 1 = xl.length by omega]; simp
  have hi1' : (xl ++ [st'])[xl.length - 1]? = some st := by
    rw [List.getElem?_append_left (by have := List.length_pos_iff.mpr hne; omega),
      ← List.getLast?_eq_getElem?]
    exact Hlast
  ihave #H1 := monoListIdxOwn_get (xl.length - 1) st hi1' $$ Hlb
  ihave #H2 := monoListIdxOwn_get (xl.length - 1 + 1) st' hi2 $$ Hlb
  icases loc_split _ s' $$ Hs with ⟨Hs, Hs2⟩
  icases chan_split _ sc' $$ Hsc with ⟨Hsc, Hsc2⟩
  imodintro
  iframe Hs2 Hsc2 Hnlb
  isplitl [Hs Hsc Hl Hn]
  · iexists (s', sc', xl ++ [st'])
    iframe
    iframe #
    ipureintro; simp
  · unfold leasingStep
    iexists _
    iframe #

end lemmas

end EtcdGrove
end Perennial
