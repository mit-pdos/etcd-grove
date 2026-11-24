/-
Proof of `membership.NewClusterFromURLsMap.spec` (claim #34, stage 2, 2026-11-25): `NewCluster`, then
the range over the URLs map (in Go's unspecified order; the invariant: the members so far are the
`memOfList` of the keys seen, their ids fresh and not `0` by the premises, so neither error return is
reached), then `genID`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewClusterFromURLsMap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewCluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__genID
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.BuildLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.NewClusterFromURLsMap.wp_proof
    (hNC : membership.NewCluster.spec (GF := GF) (hG := hG))
    (hNM : membership.NewMember.spec (GF := GF) (hG := hG))
    (hGen : membership.RaftCluster.genID.spec (GF := GF) (hG := hG)) :
    membership.NewClusterFromURLsMap.spec (GF := GF) (hG := hG) := by
  intro lg token mp m urls opts f ml Hfips Hplain Hnd Hnz Hsz Hulen
  -- the entries' members
  let fm : GoString → apply.MemberM := fun k => membership.memberOfURLs k (urls k) token
  have hfm : ∀ k, (fm k).id = (membership.memberOfURLs k (urls k) token).id := fun _ => rfl
  wp_start as ⟨#Hlg, #Hm, #Hurls, #Hopts, #Hf⟩
  try wp_auto
  wp_apply hNC lg opts f ml $$ [] as %c ⟨%Hcnn, Hcl⟩
  · iframe #
  try wp_auto
  iunfold membership.clusterOwned at Hcl
  icases Hcl with ⟨%lgc, %rp, %dp, Hclg, #Hlgc, Hlid, Hcid, Hbe, Hmu, Hver, Hmem, Hrf, Hrm, Hdg,
    Hdgv, Hml, Hvc⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun keys i => iprop(
      ∃ (ms : GMap w64 Loc) (nm : GoString) (us : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i ∧ i.toNat ≤ keys.length ∧ GMap.size ms ≤ i.toNat⌝ ∗
      "Hmem" ∷ membership.memAt c 1 ms (membership.memOfList ((keys.take i.toNat).map fm)) ∗
      "name" ∷ name_ptr ↦ nm ∗ "urls" ∷ urls_ptr ↦ us ∗ "c" ∷ c_ptr ↦ c ∗
      "token" ∷ token_ptr ↦ token)) _ _ _ mp m DFrac.discard) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  have hperm : keys.Perm m.domList := membership.keys_perm_domList m keys Hkset Hknodup
  have hndk : ((keys.map fm).map (·.id)).Nodup := by
    rw [List.map_map]; exact (hperm.map _).nodup_iff.2 Hnd
  have hndk' : (keys.map (fun k => (fm k).id)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hndk
  isplitl [Hmem name urls c token]
  · iexists ∅, _, _
    iframe name urls c token
    isplitr
    · ipureintro
      refine ⟨by omega, by simp, by simp [GMap.map_size_empty]⟩
    rw [show membership.memOfList ((keys.take (Int.toNat 0)).map fm) = (∅ : GMap w64 apply.MemberM) from rfl]
    iexact Hmem
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    obtain ⟨Hi0, Hil, Hszi⟩ := Hi
    have hkdom : key ∈ m.domList := (GMap.mem_dom_list m key).2 (by rw [Hvv]; rfl)
    ihave #Hvu : (vv ↦*□ urls key : IProp GF) $$ [Hurls]
    · iapply (BigSepM.bigSepM_lookup (Φ := fun k sl => (sl ↦*□ urls k : IProp GF)) Hvv) $$ Hurls
    (try wp_auto)
    wp_apply hNM key vv (urls key) token Hfips (Hplain key (by rw [Hvv]; rfl))
      (Hulen key (by rw [Hvv]; rfl)) $$ [] as %mm Hmm
    · iframe #
    (try wp_auto)
    iunfold membership.memAt at Hmem
    icases Hmem with ⟨%mpm, Hmf, Hmap, %Hdom, Hmems⟩
    iunfold membership.memberAt at Hmm
    icases Hmm with ⟨%Hmnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, #Hcus⟩
    (try wp_auto)
    -- the lookup of the new id: absent (the ids are distinct)
    have hfresh : (fm key).id ∉ ((keys.take i.toNat).map fm).map (·.id) := by
      rw [List.map_map]
      exact membership.loop_fresh keys (fun k => (fm k).id) i.toNat key hndk' Hkey
    have hndp : (((keys.take i.toNat).map fm).map (·.id)).Nodup := by
      rw [List.map_map, List.map_take]
      exact hndk'.sublist (List.take_sublist _ _)
    have habs : (ms !! (fm key).id) = none := by
      cases h : ms !! (fm key).id with
      | none => rfl
      | some _ =>
        have h1 := Hdom.1 (fm key).id
        rw [h] at h1
        have h2 := (membership.memOfList_isSome _ hndp (fm key).id).1 (by simpa using h1.symm)
        exact absurd h2 hfresh
    rw [show membership.memberIDOf ((urls key).map membership.urlStrOf) token = (fm key).id from rfl]
    wp_apply (wp_map_lookup2 (K := w64) (V := Loc) _ _ mpm ms (fm key).id (DFrac.own 1)) $$ [Hmap]
      as Hmap
    · iframe
    simp only [habs, Option.isSome_none, decide_false, Option.getD_none]
    (try wp_auto)
    -- the id is not `0`
    have hnz : (fm key).id ≠ W64 0 := by
      intro h
      apply Hnz
      rw [List.mem_map]
      exact ⟨key, hkdom, h⟩
    try rw [show membership.memberIDOf ((urls key).map membership.urlStrOf) token = (fm key).id from rfl]
    try simp only [hnz, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    (try wp_auto)
    try rw [show membership.memberIDOf ((urls key).map membership.urlStrOf) token = (fm key).id from rfl]
    wp_apply (wp_mapInsert (K := w64) (V := Loc) _ mpm ms (fm key).id mm) $$ [Hmap] as Hmap
    · iframe
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by omega
    iexists GMap.insert (fm key).id mm ms, key, vv
    iframe name urls c token
    isplitr
    · ipureintro
      refine ⟨by omega, ?_, ?_⟩
      · have := (List.getElem?_eq_some_iff.1 Hkey).1; omega
      · rw [GMap.map_size_insert, habs]; simp; omega
    rw [hi1, membership.take_succ_map keys fm i.toNat key Hkey, membership.memOfList_append]
    iunfold membership.memAt
    iexists mpm
    iframe Hmf Hmap
    isplitr
    · ipureintro; exact membership.memDom_insert _ _ _ _ _ Hdom
    iapply membership.memMembers_insert $$ [Hmems Hid Hpu Hil Hnm Hcu Hpus]
    iframe Hmems
    iunfold membership.memberAt
    isplitr
    · ipureintro; exact Hmnn
    iexists pu, cu
    iframe
  iintro HP Hmap
  iNamed HP
  obtain ⟨Hi0, Hil, Hszi⟩ := Hi
  have htake : keys.take (GMap.size m : Int).toNat = keys := by
    rw [List.take_of_length_le]; omega
  rw [htake]
  have hmemeq : membership.memOfList (keys.map fm) = membership.memOfList (m.domList.map fm) :=
    membership.memOfList_perm _ _ (hperm.map fm) hndk
  rw [hmemeq]
  have hndL : ((m.domList.map fm).map (·.id)).Nodup := by rw [List.map_map]; exact Hnd
  (try wp_auto)
  wp_apply (hGen c 1 ms (membership.memOfList (m.domList.map fm)) (W64 0) Hfips
      (membership.memIdsOk_memOfList _ hndL) (by omega)) $$ [Hmu Hmem Hcid]
    as ⟨Hmu, Hmem, %ids, %Hids, Hcid⟩
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; exact Hcnn
  iexists ms, ids
  isplitr
  · ipureintro; exact Hids
  iunfold membership.clusterOwned
  iexists lgc, rp, dp
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
