/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5b).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Keep
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Ascend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__keep
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactMaps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BtreeAscend

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.Keep.wp_proof
    (h0 : btree.BTree.Ascend.spec (GF := GF) (hG := hG))
    (h1 : mvcc.keyIndex.keep.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Keep.spec (GF := GF) (hG := hG) := by
  have h0 : btree.BTree.Ascend.modelSpec (GF := GF) (hG := hG) := btree.BTree.Ascend.modelSpec_of h0
  intro ti γ kn rev q c
  wp_start as ⟨#Hti, Hrd, Hkn, Hcu, %Hcb⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxReader at Hrd
  icases Hrd with ⟨%t', #Htree', Hrd⟩
  icombine Htree Htree' gives %Ht'
  subst Ht'
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  wp_apply (wp_map_make1 (K := Revision) (V := Unit)) as %m Hm
  (try wp_auto)
  -- `ti.RLock()`: the promoted method
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RLock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog, %pend, %L, %cmax, HP⟩
  iNamedSuffix HP "L"
  ihave %Hcle := mvcc.crevUB_lb γ q c cmax Hcb.1 HLL.2 $$ Hcu HcrevL
  have HbL := HwfL.logB
  have Hsrt := HLL.1.1
  have Hcm : cmax < 2 ^ 63 := by
    have hr : sint.Z rev < 2 ^ 63 := by word
    omega
  (try wp_auto)
  iunfold mvcc.ownTree at HtreeL
  icases HtreeL with ⟨%Hsorted, Ht, Hkis⟩
  -- the iteration: `keyi.keep(rev, available)` for every key index
  wp_apply (h0 mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess (mvcc.itemsOfEntries L)
    (DFrac.own sync.rfrac) _
    (fun i => iprop(available_ptr ↦ m ∗ rev_ptr ↦ rev ∗
      ownMap m (DFrac.own 1) (mvcc.keepFold ∅ rev (L.take i)) ∗
      [∗list] z ∈ L, mvcc.ownEntry z sync.rfrac)) iprop(False))
    $$ [Ht available rev Hm Hkis] as ⟨Ht, Hpost⟩
  · isplitr
    · ipureintro; exact mvcc.kiItemLess_swo
    iframe Ht available rev Hkis
    isplitl [Hm]
    · rw [List.take_zero, show mvcc.keepFold ∅ rev [] = ∅ from rfl]; iexact Hm
    unfold btIterSpec
    iintro %i %p %v %Hv
    wp_start_folded as ⟨⟨Hav, Hrev, Hm, Hkis⟩, #Hitv⟩
    unfold mvcc.itemsOfEntries at Hv
    rw [List.getElem?_map] at Hv
    cases hz : L[i]? with
    | none => rw [hz] at Hv; simp at Hv
    | some z =>
    rw [hz] at Hv
    simp only [Option.map_some, Option.some.injEq] at Hv
    subst Hv
    iunfold mvcc.kiItemIs at Hitv
    icases Hitv with ⟨%Hpz, -⟩
    simp only at Hpz
    subst Hpz
    icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z sync.rfrac) hz |>.1 $$ Hkis
      with ⟨Hz, Hback⟩
    iunfold mvcc.ownEntry at Hz
    icases Hz with ⟨%Hzn, %gs, Hzki⟩
    have Hget : mvcc.idxGet (mvcc.idxOfEntries L) z.2.1 = some z.2.2 :=
      mvcc.idxGet_of_mem _ Hsrt (z.2.1, z.2.2)
        (by unfold mvcc.idxOfEntries; exact List.mem_map.2 ⟨z, List.mem_of_getElem? hz, rfl⟩)
    have Hok : mvcc.gensOk z.2.2 := mvcc.IdxCRep.gensOk HbL HLL.1 Hcm Hget
    wp_auto
    wp_apply (h1 z.1 gs z.2.2 (DFrac.own sync.rfrac) rev m _ Hok) $$ [Hzki Hm] as ⟨Hzki, Hm⟩
    · iframe Hzki Hm
    iapply HΦ
    simp only [↓reduceIte]
    iframe Hav Hrev
    have Htake : L.take (i + 1) = L.take i ++ [z] := by
      rw [List.take_add_one, hz]; rfl
    rw [Htake, mvcc.keepFold_append]
    iframe Hm
    ihave Hz : iprop(mvcc.ownEntry z sync.rfrac) $$ [Hzki]
    · iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hzn
      iexists gs
      iexact Hzki
    ihave Hkis := Hback $$ %z Hz
    rw [mvcc.set_same hz]
    iexact Hkis
  icases Hpost with (%Hf | ⟨Hav, Hrev, Hm, Hkis⟩)
  · exact Hf.elim
  rw [show (mvcc.itemsOfEntries L).length = L.length by unfold mvcc.itemsOfEntries; simp,
    List.take_length]
  -- the answer is the certified log's
  icases mvcc.idxKnows_facts γ kn kn.log rfl ilog pend sync.rfrac $$ Hkn HhistL HnevL
    with ⟨%Hfacts, Hkn, HnevL⟩
  obtain ⟨Hcmp, Hcnt', Hwf0, Hlen0, Hcs0⟩ := Hfacts
  have Hkeep : mvcc.keepOfIs (mvcc.keepFold ∅ rev L) kn.log rev := by
    intro r
    rw [mvcc.keepFold_spec (ilog ++ [pend]) HbL HLL.1 rev (by omega) r]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← mvcc.reader_keep kn.log ilog pend Hcmp Hcnt' (by have := HwfL.2.1; omega) ⟨Hlen0, Hcs0⟩ k rev
        (by omega) (by omega)]; exact hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [mvcc.reader_keep kn.log ilog pend Hcmp Hcnt' (by have := HwfL.2.1; omega) ⟨Hlen0, Hcs0⟩ k rev
        (by omega) (by omega)]; exact hk⟩
  -- the deferred `ti.RUnlock()`
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
  wp_call
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL Ht Hkis HcmpL] as Hrd
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog, pend, L, cmax
    simp only [named]
    iframe HnevL HcmpL
    iframe #
    isplitl [Ht Hkis]
    · iunfold mvcc.ownTree; iframe Ht Hkis; ipureintro; exact Hsorted
    ipureintro
    exact ⟨HLL, HwfL⟩
  (try wp_auto)
  iapply HΦ
  iframe Hkn Hcu
  isplitl [Hrd]
  · iunfold mvcc.idxReader
    iexists t
    iframe Hrd
    iexact Htree
  iexists _
  iframe Hm
  ipureintro; exact Hkeep

end proof

end EtcdGrove
end Perennial
