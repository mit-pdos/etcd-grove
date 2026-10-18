/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Members.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).

Under the cluster's mutex, the members map's range clones each member into the result's slice
(the loop's invariant: the clones so far, owned, with their ids); `sort.Sort` over `MembersByID`
(a `sorterSpec` of the (pointer, id) list, ordered by id) permutes them.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member__Clone
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID__Len
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID__Less
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID__Swap
public import Spec.sort.Sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The order of `MembersByID` (ids, unsigned) is a strict weak order. -/
theorem membership.idLt_swo :
    slices.StrictWeakOrder (fun a b : Loc × w64 => decide (uint.Z a.2 < uint.Z b.2) = true) := by
  simp only [decide_eq_true_eq]
  exact {
    strict_weak_order_irrefl := fun _ => Int.lt_irrefl _
    strict_weak_order_trans := fun _ _ _ h1 h2 => Int.lt_trans h1 h2
    strict_weak_order_equiv := {
      refl := fun _ => ⟨Int.lt_irrefl _, Int.lt_irrefl _⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h1 h2 => ⟨by omega, by omega⟩ } }

/-- What `MembersByID`, a sorter over the slice `sl`, holds: the pointers of `l`, the members
(owned) with their ids. -/
def membership.sorterR (sl : GoSlice) (l : List (Loc × w64)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ [∗list] p ∈ l, membership.memberIs p.1 p.2)

/-- `MembersByID` over the slice `sl` sorts the (pointer, id) list of its members. -/
theorem membership.sorter_byID
    (hLen : membership.MembersByID.Len.spec (GF := GF) (hG := hG))
    (hLess : membership.MembersByID.Less.spec (GF := GF) (hG := hG))
    (hSwap : membership.MembersByID.Swap.spec (GF := GF) (hG := hG)) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ⊢
      sorterSpec (interface.mk go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty #sl)
        (membership.sorterR sl) (fun a b => decide (uint.Z a.2 < uint.Z b.2)) := by
  iintro #Hpkg
  unfold sorterSpec membership.sorterR
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ ⟨Hs, Hk⟩ HΦ
    wp_apply (hLen sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Hk⟩ HΦ
    wp_apply (hLess sl l (DFrac.own 1) i j a b) $$ [$Hs $Hk] as ⟨Hs, Hk⟩
    · ipureintro; exact Hij
    iapply HΦ
    iframe
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Hk⟩ HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) :=
    slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  iapply (BigSepL.bigSepL_perm (PROP := IProp GF)
    (Φ := fun (x : Loc × w64) => membership.memberIs (GF := GF) x.1 x.2) hp).1
  iexact Hk

theorem membership.RaftCluster.Members.wp_proof
    (hClone : membership.Member.Clone.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».spec (GF := GF) (hG := hG))
    (hLen : membership.MembersByID.Len.spec (GF := GF) (hG := hG))
    (hLess : membership.MembersByID.Less.spec (GF := GF) (hG := hG))
    (hSwap : membership.MembersByID.Swap.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.Members.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hrc
  iunfold membership.isRaftCluster at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, #Hloc⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(
      ∃ (sl' : GoSlice) (cl : List (Loc × w64)) (x : Loc),
      "%Hi" ∷ ⌜0 ≤ i ∧ cl.length = i.toNat⌝ ∗
      "ms" ∷ ms_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* cl.map Prod.fst ∗
      "Hcap" ∷ ownSliceCap Loc sl' (DFrac.own 1) ∗
      "Hcl" ∷ ([∗list] p ∈ cl, membership.memberIs p.1 p.2) ∗
      "Hmems" ∷ ([∗map] _k ↦ m ∈ mm, membership.ownMember m) ∗
      "m" ∷ m_ptr ↦ x)) $$ Hmap
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ms m Hmems]
  · iexists slice.nil, [], zero_val Loc
    simp only [named, List.map_nil]
    iframe ms m Hmems
    isplitl []
    · ipureintro; simp
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    iapply BigSepL.bigSepL_nil.2
    iempintro
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun (_ : w64) (m : Loc) => membership.ownMember (GF := GF) m) Hvv).1 $$ Hmems
      with ⟨Hown, Hmclose⟩
    iunfold membership.ownMember at Hown
    icases Hown with ⟨%id, Hown⟩
    wp_apply hClone vv id $$ [Hown] as %mc ⟨Hown, Hmc⟩
    · iframe #; iframe Hown
    ihave Hmems := Hmclose $$ [Hown]
    · iunfold membership.ownMember; iexists id; iexact Hown
    (try wp_auto)
    wp_apply wp_slice_literal (V := Loc) [mc]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2] as %sl3 ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl3, cl ++ [(mc, id)], vv
    simp only [named, List.map_append, List.map_cons, List.map_nil]
    iframe ms Hsl Hcap Hmems m
    isplitl []
    · ipureintro; refine ⟨by omega, ?_⟩; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    iapply BigSepL.bigSepL_snoc.2
    iframe Hcl Hmc
  iintro HP Hmap
  iNamed HP
  (try wp_auto)
  ihave #Hpsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hsorter := membership.sorter_byID hLen hLess hSwap sl' $$ Hpkg
  wp_apply (hSort (Loc × w64) _ (membership.sorterR sl') (fun a b => decide (uint.Z a.2 < uint.Z b.2))
      cl membership.idLt_swo) $$ [Hsl Hcl] as %l' ⟨HR, -⟩
  · iframe #
    unfold membership.sorterR
    iframe
    ipureintro
    have := Hi.2
    omega
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems]
  · inext
    iunfold membership.rcLockInv
    iexists mp, mm
    iframe Hmf Hmap Hmems Hloc
    ipureintro; exact Hsz
  (try wp_auto)
  iapply HΦ
  unfold membership.sorterR
  icases HR with ⟨Hsl, Hcl⟩
  iexists l'.map Prod.fst
  iunfold membership.membersAt
  iframe Hsl
  iapply membership.membersL_own $$ Hcl

end proof

end EtcdGrove
end Perennial
