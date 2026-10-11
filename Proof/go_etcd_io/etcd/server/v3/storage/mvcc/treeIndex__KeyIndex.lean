/-
Proof of `Spec/.../mvcc/treeIndex__KeyIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__KeyIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__keyIndex
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.KeyIndex.wp_proof
    (hKI : mvcc.treeIndex.keyIndex.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.KeyIndex.spec (GF := GF) (hG := hG) := by
  intro ti γ kn keyi k
  wp_start as ⟨#Hti, Hrd, Hkn, #Hkey⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxReader at Hrd
  icases Hrd with ⟨%t', #Htree', Hrd⟩
  icombine Htree Htree' gives %Ht'
  subst Ht'
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `ti.RLock()`: the promoted method
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RLock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog, %pend, %L, HP⟩
  iNamedSuffix HP "L"
  (try wp_auto)
  -- `ti.keyIndex(keyi)`
  ihave #Hitem : mvcc.kiItemIs (GF := GF) keyi (keyi, k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iexact Hkey
  wp_apply (hKI ti t L sync.rfrac keyi k) $$ [$HtreeL] as %p ⟨HtreeL, %Hp⟩
  · iframe #
  -- what the reader knows, under the lock
  icases mvcc.idxKnows_facts γ kn kn.log rfl ilog pend sync.rfrac $$ Hkn HhistL HnevL
    with ⟨%Hfacts, Hkn, HnevL⟩
  icases mvcc.idxKnows_writer_events γ kn ilog pend sync.rfrac $$ Hkn HhistL HnevL
    with ⟨%Hwev, Hkn, HnevL⟩
  obtain ⟨Hcmp, Hcnt', -, -, -⟩ := Hfacts
  have HlenL := HwfL.2.1
  obtain ⟨rest, hrest⟩ := mvcc.reader_prefix kn.log ilog pend Hcmp Hcnt' (by omega)
  icases mvcc.ownTree_sorted t L sync.rfrac $$ HtreeL with ⟨HtreeL, %Hsorted⟩
  have Hidx := mvcc.idxGet_entries L Hsorted k
  rw [HLL] at Hidx
  have Hnone := mvcc.idxGet_indexOf_eq_none_iff (mvcc.evsOf (ilog ++ [pend])) k
  -- the pointer: the found entry's, with its key; or `nil`
  ihave Hres : (⌜p = null⌝ ∨ ⌜p ≠ null⌝ ∗ mvcc.kiKey p k) ∗
      ⌜mvcc.kiOfKey (mvcc.evsOf kn.log) k ≠ mvcc.kiEmpty → p ≠ null⌝ ∗
      ⌜∀ ilog' pend', kn = .writer ilog' pend' → p ≠ null →
        mvcc.kiOfKey (mvcc.evsOf (ilog' ++ [pend'])) k ≠ mvcc.kiEmpty⌝ ∗
      mvcc.ownTree t L sync.rfrac $$ [HtreeL]
  · cases hf : L.find? (fun z => decide (z.2.1 = k)) with
    | none =>
      rw [hf] at Hp Hidx
      simp only [Option.map_none, Option.getD_none] at Hp Hidx
      iframe HtreeL
      isplitl []
      · ileft; ipureintro; exact Hp
      isplitl []
      · ipureintro
        intro hne
        exfalso
        have := mvcc.kiOfKey_ne_mono _ rest k hne
        rw [← hrest] at this
        exact this (Hnone.1 Hidx)
      ipureintro
      intro _ _ _ hp
      exact absurd Hp hp
    | some z =>
      rw [hf] at Hp Hidx
      simp only [Option.map_some, Option.getD_some] at Hp Hidx
      subst Hp
      obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
      icases mvcc.ownTree_entry t L sync.rfrac z (List.mem_of_getElem? hi) $$ HtreeL
        with ⟨HtreeL, %Hzn, #Hzk⟩
      iframe HtreeL
      isplitl []
      · iright
        isplitl []
        · ipureintro; exact Hzn
        rw [← hk]
        iexact Hzk
      isplitl []
      · ipureintro; intro _; exact Hzn
      ipureintro
      intro ilog' pend' hkn _
      rw [← Hwev ilog' pend' hkn]
      intro he
      rw [← Hnone] at he
      rw [he] at Hidx
      cases Hidx
  icases Hres with ⟨Hres, %Hc1, %Hc2, HtreeL⟩
  -- the deferred `ti.RUnlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
  wp_call
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL] as Hrd
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog, pend, L
    simp only [named]
    iframe HnevL HtreeL
    iframe #
    ipureintro
    exact ⟨HLL, HwfL⟩
  (try wp_auto)
  iapply HΦ
  iframe Hkn Hres
  isplitl [Hrd]
  · iunfold mvcc.idxReader
    iexists t
    iframe Hrd
    iexact Htree
  isplitl []
  · ipureintro; exact Hc1
  ipureintro; exact Hc2

end proof

end EtcdGrove
end Perennial
