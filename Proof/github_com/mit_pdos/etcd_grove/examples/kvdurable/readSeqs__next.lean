/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/readSeqs__next.lean`. Lean-first (no
Rocq counterpart).

Under the lock, `last` is at least every replica's last read sequence number (`readSeqsInv`); the
number issued, `last + 1`, is fresh for the caller's id (nothing was minted at `(id, last + 1)`:
the minting discipline, `MintOk`, keeps every minted number at most its id's last one), so it is
minted in the store's invariant (`mintOk_next`) and becomes the id's last one.

SPEC-GAP (stage II (f), reported): the spec mints `f seq` for a caller-chosen `f`, but the minting
discipline (`MintOk`, kvreconf's, in `rkvInv`) records only read contexts, `readCtxB id seq key`
for a key shorter than `2^64` (what `kd_read_minted` and the read's answer rely on). The one fact
`f seq = readCtxB id seq key` (for some such key) is left `sorry` (`next_ctx_gap`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.readSeqs__next
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ApplyLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (MintOk readCtxB MintedRead freshIds)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A fresh read sequence number** `last + 1` for replica `id`, whose last one `ns` is at most
`last`: nothing was minted at `(id, last + 1)`, and minting the read's context there keeps the
discipline (kvreconf's `mintOk_read`, without marking the context used). -/
theorem mintOk_next (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
    (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8))
    (id ns last : w64) (key : List w8) (Hok : MintOk n Mi RS RMi O U) (HS : RS !! id = some ns)
    (Hle : uint.Z ns ≤ uint.Z last) (Hl : uint.Z last + 1 < 2 ^ 64)
    (Hk : (key.length : Int) < 2 ^ 64) :
    RMi !! (id, last + W64 1) = none ∧
      MintOk n Mi (RS.insert id (last + W64 1))
        (RMi.insert (id, last + W64 1) (readCtxB id (last + W64 1) key)) O U := by
  have Hl1 : uint.Z (last + W64 1) = uint.Z last + 1 := by word
  have HRM0 : RMi !! (id, last + W64 1) = none := by
    cases h : RMi !! (id, last + W64 1) with
    | none => rfl
    | some c =>
      obtain ⟨ns', Hns', Hle', -⟩ := Hok.2.1 _ _ _ h
      rw [HS] at Hns'; cases Hns'
      omega
  refine ⟨HRM0, Hok.1, ?_, Hok.2.2.1, ?_⟩
  · intro r s c Hc
    by_cases Heq : (r, s) = (id, last + W64 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
      rw [GMap.lookup_insert_eq] at Hc; cases Hc
      exact ⟨last + W64 1, GMap.lookup_insert_eq _ _ _, Int.le_refl _, key, Hk, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hc
      obtain ⟨ns', Hns', Hle', Hkey⟩ := Hok.2.1 _ _ _ Hc
      by_cases Hr : r = id
      · subst Hr
        rw [HS] at Hns'; cases Hns'
        exact ⟨last + W64 1, GMap.lookup_insert_eq _ _ _, by omega, Hkey⟩
      · exact ⟨ns', by rw [GMap.lookup_insert_ne _ _ (Ne.symm Hr)]; exact Hns', Hle', Hkey⟩
  · intro c Hc
    exact kvreconf.mintedRead_insert _ _ _ _ HRM0 (Hok.2.2.2 c Hc)

/-- The caller's id is one of `readSeqsInv`'s. -/
theorem freshIds_get (id : w64) (h1 : 1 ≤ uint.nat id) (h9 : uint.nat id ≤ 9) :
    (freshIds 0)[uint.nat id]? = some id := by
  unfold freshIds
  rw [List.filter_eq_self.2 (by intro a _; simp)]
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]
  congr 1; word

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- SPEC-GAP (see the file header): what `next` mints is a read's context. -/
private theorem next_ctx_gap (id seq : w64) (f : w64 → List w8) :
    ∃ key : List w8, (key.length : Int) < 2 ^ 64 ∧ f seq = readCtxB id seq key := by
  sorry

/-- **Minting the read's context** at `(id, last + 1)`, `id`'s last read sequence number `ns`
at most `last` (see the file header). -/
theorem kd_mint_next (γ : KdNames) (id ns last : w64) (key : List w8)
    (Hns : uint.Z ns ≤ uint.Z last) (Hl : uint.Z last + 1 < 2 ^ 64) (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γ -∗ id ↪[γ.r.rseq] ns ={⊤}=∗
      id ↪[γ.r.rseq] (last + W64 1) ∗
      (id, last + W64 1) ↪[γ.r.rmint]□ readCtxB id (last + W64 1) key := by
  iintro #Hinv Hfr
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %nn, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  icases ghost_map_lookup $$ HRS Hfr with %HSi
  obtain ⟨HRM0, Hok'⟩ := mintOk_next nn Mi RS RMi O U id ns last key Hok HSi Hns Hl Hk
  imod ghost_map_update (last + W64 1) $$ HRS Hfr with ⟨HRS, Hfr⟩
  imod ghost_map_insert_persist (id, last + W64 1) (readCtxB id (last + W64 1) key) HRM0 $$ HRMi
    with ⟨HRMi, #Hmint⟩
  imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
  · inext
    iexists ops, nn, Mi, RS.insert id (last + W64 1),
      RMi.insert (id, last + W64 1) (readCtxB id (last + W64 1) key), O, U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU Hn HMi HRS HRMi HO
    ipureintro; exact ⟨Hok', Hodm, Hsh⟩
  imodintro
  iframe Hfr Hmint

theorem readSeqs.next.wp_proof : readSeqs.next.spec (GF := GF) (hG := hG) := by
  intro γ vs s id f Hid1 Hid9
  wp_start as ⟨#Hseqs, #Hcl⟩
  iunfold isReadSeqs at Hseqs
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply (lc := 1) sync.Mutex.wp_Lock _ _ $$ [$Hseqs] as ⟨Hlocked, HL⟩
  iunfold readSeqsInv at HL
  icases HL with ⟨%last, Hlast, Hids⟩
  try wp_auto
  wp_if_destruct
  · -- used up
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hseqs $Hlocked Hlast Hids]
    · inext
      iunfold readSeqsInv
      iexists _
      iframe
    try wp_auto
    iapply HΦ
    iintro %Hf
    cases Hf
  -- `last + 1`, minted for `id`
  have Hl : uint.Z last + 1 < 2 ^ 64 := by
    word
  obtain ⟨key, Hk, Hfk⟩ := next_ctx_gap id (last + W64 1) f
  icases BigSepL.bigSepL_lookup_acc_impl (freshIds_get id Hid1 Hid9) $$ Hids
    with ⟨⟨%ns, Hfr, %Hns⟩, Hback⟩
  imod kd_mint_next γ id ns last key Hns Hl Hk $$ Hinv Hfr with ⟨Hfr, #Hmint⟩
  have Hl1 : uint.Z (last + W64 1) = uint.Z last + 1 := by word
  ihave Hids : iprop([∗list] i ∈ freshIds 0, ∃ ns : w64, i ↪[γ.r.rseq] ns ∗
      ⌜uint.Z ns ≤ uint.Z (last + W64 1)⌝) $$ [Hback Hfr]
  · iapply Hback
    · imodintro
      iintro %k %y %_ %_ ⟨%ns', H, %Hle⟩
      iexists ns'
      iframe H
      ipureintro; omega
    iexists last + W64 1
    iframe Hfr
    ipureintro; omega
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hseqs $Hlocked Hlast Hids]
  · inext
    iunfold readSeqsInv
    iexists last + W64 1
    iframe
  try wp_auto
  iapply HΦ
  iintro -
  rw [Hfk]
  iexact Hmint

end proof

end kvdurable
end EtcdGrove
end Perennial
