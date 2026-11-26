/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__reader.lean`: each
iteration takes a time receipt (`wp_take_receipt`, at `running`'s resolution) and keeps it, so the
counter `k` is the reader's receipts plus one, below `receiptBound GF ≤ 2 ^ 61` (`antRunFits`):
`k` never wraps, and `"r<k>"` is not among `"r1" … "r(k-1)"` (`parseUint_fmtUint10`), so the reader
mints its `readOk` (`auth_set_alloc`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__reader
public import Perennial.Spec.strconv.FormatUint
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__running
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Proof.ReceiptTactics
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- The reader's context at counter `i + 1`. -/
private abbrev rctx (i : Nat) : List w8 :=
  go!"r" ++ internal.strconv.fmtUint (W64 ((i : Int) + 1)) (W64 10)

/-- `"r<k>"` is not among the contexts `"r1" … "r(k-1)"` handed out, below the receipts' bound. -/
private theorem rctx_fresh (kv : w64) (h1 : 1 ≤ uint.nat kv) :
    (go!"r" ++ internal.strconv.fmtUint kv (W64 10) : List w8) ∉
      GMap.listToSet ((List.range (uint.nat kv - 1)).map rctx) := by
  rw [GMap.elem_of_list_to_set, List.mem_map]
  rintro ⟨i, hi, he⟩
  rw [List.mem_range] at hi
  have he' := List.append_cancel_left he
  have hp := congrArg (fun s => internal.strconv.parseUint s 10 64) he'
  simp only [internal.strconv.parseUint_fmtUint10] at hp
  injection hp with hp
  have hi1 : (W64 ((i : Int) + 1)).toNat = i + 1 := by
    have : uint.nat (W64 ((i : Int) + 1)) = i + 1 := by word
    exact this
  have hkn : uint.nat kv = kv.toNat := rfl
  omega

/-- The contexts after `"r<k>"` is handed out. -/
private theorem rctx_step (kv : w64) (h1 : 1 ≤ uint.nat kv) (hb : uint.nat kv < 2 ^ 61) :
    GMap.listToSet ((List.range (uint.nat (kv + W64 1) - 1)).map rctx) =
      ({[go!"r" ++ internal.strconv.fmtUint kv (W64 10)]} ∪
        GMap.listToSet ((List.range (uint.nat kv - 1)).map rctx) : GSet (List w8)) := by
  have hn : uint.nat (kv + W64 1) - 1 = (uint.nat kv - 1) + 1 := by word
  have hk : W64 (((uint.nat kv - 1 : Nat) : Int) + 1) = kv := by word
  rw [hn, List.range_succ, List.map_append, GMap.listToSet_app]
  apply GMap.set_eq
  intro x
  simp only [GMap.elem_of_union, GMap.elem_of_list_to_set, GMap.elem_of_singleton, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false, rctx, hk, List.mem_append]
  exact Or.comm

/-- The counter below the receipts' bound. -/
private theorem kv_bound {B : Nat} (hB : B + 3 ≤ 2 ^ 61) (n : Nat) (h : n - 1 + 1 < B) (h1 : 1 ≤ n) :
    n < 2 ^ 61 := by omega

theorem Cluster.reader.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (wp_running : Cluster.running.spec (GF := GF) (hG := hG))
    (wp_pick : Cluster.pick.spec (GF := GF) (hG := hG))
    (wp_deliver : Cluster.deliver.spec (GF := GF) (hG := hG)) :
    Cluster.reader.spec (GF := GF) (hG := hG) := by
  intro c γ
  wp_start as ⟨#Hc, Htok, Hro, %Hreads⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro', #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  ihave Hcf := Hcfg
  iStructNamed Hcf
  imod (receipt_zero (GF := GF)) with Hr0
  wp_auto
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave IH : iprop(∃ kv : w64, "c" ∷ c_ptr ↦ c ∗ "k" ∷ k_ptr ↦ kv ∗ "Hrd" ∷ readerOwn γ kv ∗
      "Hrk" ∷ ⧗ (uint.nat kv - 1) ∗ "%Hk1" ∷ ⌜1 ≤ uint.nat kv⌝) $$ [c k Hro Hr0]
  · iexists (W64 1)
    iframe
    ipureintro; decide
  wp_for IH
  wp_apply wp_running c γ $$ [$Hpkg $Hc] as %b -
  wp_if_destruct
  · try wp_auto
    wp_apply +noauto wp_pick c γ $$ [$Hpkg $Hc] as %n ⟨%j, #Hn⟩
    wp_take_receipt as Hr1
    ihave ⟨%Hlt, Hrk⟩ := receipt_add_one_lt (GF := GF) _ $$ [$Hr1 $Hrk]
    have hkb : uint.nat kv < 2 ^ 61 := kv_bound Hfits _ Hlt Hk1
    wp_apply wp_FormatUint kv (W64 10) (by decide) (by decide) $$ [$Hsc]
    try wp_auto
    wp_apply wp_string_to_bytes as %ds ⟨Hds, -⟩
    imod ownSlice_persist $$ Hds with #Hds
    iunfold readerOwn at Hrd
    imod (auth_set_alloc _ _ _ (rctx_fresh kv Hk1)) $$ Hrd with ⟨Hrd, Hok⟩
    try wp_auto
    wp_apply wp_deliver c γ n j _ $$ [$Hpkg $Hc $Hn Hds Hok]
    · iunfold inputOk
      iright; iright; ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hreads⟩
      iexists _
      isplitr [Hok]
      · iexact Hds
      iunfold readOk
      iexact Hok
    try wp_auto
    wp_for_post
    iframe
    iexists _
    iframe
    isplitl [Hrd]
    · iunfold readerOwn
      rw [rctx_step kv Hk1 hkb]
      iexact Hrd
    isplitl [Hrk]
    · have : uint.nat (kv + W64 1) - 1 = uint.nat kv - 1 + 1 := by word
      rw [this]; iexact Hrk
    ipureintro; word
  · wp_if_destruct
    · try wp_auto
      iapply HΦ
      iframe
    · exfalso; cases b <;> simp_all

end proof

end AntHarness
end EtcdGrove
end Perennial
