/-
Port of `election_proof/proof_readOnly__maybeAdvance.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.readOnly__maybeAdvance
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__CommittedIndex
public import Spec.go_etcd_io.raft.v3.readOnly__AckedIndex

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

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- Rocq `big_sepL2_take_drop`. -/
private theorem bigSepL2_take_drop {A B : Type} (Φ : A → B → IProp GF) (n : Nat)
    (l1 : List A) (l2 : List B) (Hl : l1.length = l2.length) :
    ([∗list] _k ↦ x;y ∈ l1;l2, Φ x y) ⊢
    ([∗list] _k ↦ x;y ∈ l1.take n;l2.take n, Φ x y) ∗
    ([∗list] _k ↦ x;y ∈ l1.drop n;l2.drop n, Φ x y) := by
  conv => lhs; rw [← List.take_append_drop n l1, ← List.take_append_drop n l2]
  exact (BigSepL2.bigSepL2_append (Or.inl (by simp [Hl]))).1

/-- `CommittedIndex` is called on the object itself, as an `AckedIndexer`, with the
whole object as the indexer's resource and the voter map lent (the receiver is the
value `c`). Then, if the quorum index is past `confirmedReads`, the first
`N - confirmed` requests are split off the queue (`ownSlice_split_all` at `↦*□`): the
slice returned is that prefix, read-only and without the capacity; the rest, with the
capacity (`ownSliceCap_slice`), is the new queue. -/
theorem readOnly.maybeAdvance.wp_proof
    (wp_JointConfig_CommittedIndex : quorum.JointConfig.CommittedIndex.spec (GF := GF) (hG := hG))
    (wp_readOnly_AckedIndex : readOnly.AckedIndex.spec (GF := GF) (hG := hG)) :
    readOnly.maybeAdvance.spec (GF := GF) (hG := hG) := by
  intro ro r c m0 ids
  wp_start as H
  iNamed H
  wp_auto
  -- the indexer's contract, from `readOnly.AckedIndex`'s triple, with the whole object
  -- as its resource
  ihave #Hidx : isAckedIndexer (interface.mkOk (go.GoType.PointerType readOnly.ty) #ro)
      (ownReadOnly ro r) (fun v => r.acks !! v) $$ []
  · unfold isAckedIndexer
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %id
    wp_start_folded as HP
    wp_apply wp_readOnly_AckedIndex $$ [$HP] as HP
    iapply HΦ $$ HP
  wp_apply wp_JointConfig_CommittedIndex c m0 ids _ (ownReadOnly ro r)
      (fun v => r.acks !! v) $$ [$Hvoters $Hown $Hidx]
    as %N ⟨Hv, Hown, %Hemp, %Hq⟩
  · isplitr
    · ipureintro; exact Hsz
    ipureintro; exact Hc
  iNamed Hown
  wp_auto
  ihave %Hl := ownSlice_len $$ Hucr
  ihave %Hwf := ownSlice_wf $$ Hucr
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hreqs
  wp_if_destruct
  · -- nothing confirmed: `nil`
    have Hadv : readonlyAdvance r N = (r, []) := by
      unfold readonlyAdvance; rw [ite_eq_left (by rw [← Hro_conf]; exact Hif)]
    iapply HΦ $$ %slice.nil %N
    rw [Hadv]
    isplitr
    · ipureintro; exact Hq Hne
    isplitl [Hro Hacks Hucr Hucr_cap Hreqs]
    · unfold ownReadOnly
      iexists rov, ptrs
      simp only [named]
      iframe Hro Hacks Hucr Hucr_cap Hreqs
      ipureintro; exact Hro_conf
    iframe Hv
    iexists []
    isplitl
    · iapply ownSlice_nil
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  · -- `N` is one of the acknowledged positions, so at most `confirmed + len pending`
    obtain ⟨⟨v, Hv, HNv⟩, -, -⟩ := Hq Hne
    have HNle : uint.Z N ≤ uint.Z rov.confirmedReads' + (r.pending.length : Int) := by
      rw [← HNv, Hro_conf]; exact Hbound v Hv
    have HsubZ : uint.Z (N - rov.confirmedReads') = uint.Z N - uint.Z rov.confirmedReads' := by
      word
    have HlenZ : (ptrs.length : Int) = sint.Z rov.unconfirmedReads'.len := by
      rw [Hl.1]; word
    have HkZ : uint.Z (N - rov.confirmedReads') ≤ sint.Z rov.unconfirmedReads'.len := by
      rw [HsubZ, ← HlenZ, Hlen]; omega
    have Hku : sint.Z (N - rov.confirmedReads') = uint.Z (N - rov.confirmedReads') := by
      word
    rw [ite_eq_left (by word)]
    wp_auto
    rw [ite_eq_left (by word)]
    wp_auto
    icases (ownSlice_split_all (N - rov.confirmedReads') _ _ _ ⟨by word, by word⟩).1 $$ Hucr
      with ⟨Hpre, Hrest⟩
    ihave Hcap := (ownSliceCap_slice _ (N - rov.confirmedReads') _ ⟨by word, by word, Hwf.2⟩).1
      $$ Hucr_cap
    icases bigSepL2_take_drop _ (uint.nat (N - rov.confirmedReads')) _ _ Hlen $$ Hreqs
      with ⟨Hreqs1, Hreqs2⟩
    have Hk : sint.nat (N - rov.confirmedReads') = uint.nat (N - rov.confirmedReads') := by
      word
    rw [Hk]
    iapply HΦ $$ %_ %N
    have Hadv : readonlyAdvance r N =
        ({ r with pending := r.pending.drop (uint.nat (N - r.confirmed)), confirmed := N },
         r.pending.take (uint.nat (N - r.confirmed))) := by
      unfold readonlyAdvance; rw [ite_eq_right (by rw [← Hro_conf]; exact Hif)]
    rw [Hadv, ← Hro_conf]
    isplitr
    · ipureintro; exact Hq Hne
    iframe Hv
    isplitl [Hro Hacks Hrest Hcap Hreqs2]
    · unfold ownReadOnly
      iexists _, (ptrs.drop (uint.nat (N - rov.confirmedReads')))
      simp only [named]
      iframe Hro Hacks Hrest Hcap Hreqs2
      ipureintro; rfl
    iexists _
    iframe Hpre Hreqs1

end proof

end EtcdGrove
end Perennial
