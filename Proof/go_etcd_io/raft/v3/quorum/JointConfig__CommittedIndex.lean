/-
Port of election_proof/proof_JointConfig__CommittedIndex.v.

Lean notes: Perennial's `array_acc_same` (`v3_proof/readonly.lean`, which cannot be
imported here) is restated locally as `array_acc_same'`.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__CommittedIndex
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__CommittedIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `array_acc`, putting back the same element. -/
private theorem array_acc_same' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (i : Int) (dq : DFrac) (n : Int) (a : GoArray V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq)) := by
  have hset : a.arr.set i.toNat v = a.arr := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hlookup
    exact List.set_getElem_self h
  iintro Ha
  icases array_acc (GF := GF) p i dq n a v hpos hlookup $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ %v Hv
  rw [hset]
  iexact Ha

/-- The receiver is a value-receiver copy `c`: `c[0]` and `c[1]` are handed to
`MajorityConfig.CommittedIndex` one after the other, the voter map and the indexer's
resource lent to the first; `c[1]` is the nil component, whose answer is `MaxUint64`;
then `min`. The array element reads go through `array_acc`. -/
theorem quorum.JointConfig.CommittedIndex.wp_proof
    (wp_MajorityConfig_CommittedIndex :
      quorum.MajorityConfig.CommittedIndex.spec (GF := GF) (hG := hG)) :
    quorum.JointConfig.CommittedIndex.spec (GF := GF) (hG := hG) := by
  intro c a m0 ids l PP acked
  wp_start as ⟨%Hsz, Hc, %Harr, Hm0, #Hidx, HP⟩
  wp_auto
  wp_method_call
  wp_call
  wp_call
  wp_auto
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 0)) _ _ _ m0 (by decide) (by simp [Harr])
    $$ c with ⟨Hc0, Hcback⟩
  -- the voter map is a real map, so the callee's `map.nil` disjunct cannot come back for it
  ihave %Hvnn := ownMap_not_nil _ _ _ $$ Hm0
  wp_apply wp_MajorityConfig_CommittedIndex (domSet ids) $$ [$Hc0 $Hidx $HP Hm0]
    as %N0 ⟨Hc0, Hv, HP, %Hemp0, %Hq0⟩
  · isplitr
    · ipureintro; exact Hsz
    iright
    iexists ids
    iframe
    ipureintro; rfl
  icases Hv with (⟨%Hnil, -⟩ | ⟨%voters', %Hvoters'_dom, Hvoters⟩)
  · exact absurd Hnil Hvnn
  -- `c[1]`: the nil component of a simple configuration
  ihave c := Hcback $$ Hc0
  icases array_acc_same' (GF := GF) _ (sint.Z (W64 1)) _ _ _ map.nil (by decide) (by simp [Harr])
    $$ c with ⟨Hc1, Hcback⟩
  wp_apply wp_MajorityConfig_CommittedIndex ∅ $$ [$Hc1 $Hidx $HP]
    as %N1 ⟨Hc1, -, HP, %Hemp1, -⟩
  · isplitr
    · ipureintro; rw [GMap.map_size_empty]; decide
    ileft
    ipureintro; exact ⟨rfl, rfl⟩
  have HN1 : N1 = W64 (2 ^ 64 - 1) := Hemp1 rfl
  subst HN1
  ihave c := Hcback $$ Hc1
  -- `min`: `c[0]`'s answer on both exits
  wp_if_destruct
  · iapply HΦ
    iframe Hc HP
    isplitl [Hvoters]
    · iexists voters'
      iframe
      ipureintro; exact Hvoters'_dom
    ipureintro
    exact ⟨Hemp0, Hq0⟩
  · have Heq : N0 = W64 (2 ^ 64 - 1) := by word
    subst Heq
    iapply HΦ
    iframe Hc HP
    isplitl [Hvoters]
    · iexists voters'
      iframe
      ipureintro; exact Hvoters'_dom
    ipureintro
    exact ⟨fun _ => rfl, Hq0⟩

end proof

end EtcdGrove
end Perennial
