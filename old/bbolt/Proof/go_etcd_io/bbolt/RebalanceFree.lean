/-
`node.free` during rebalance: the freed page is not pending yet (`freedOK_hnew`: the pending
ids of the writer are slots of the freed pages, which are other pages of the view, whose slots
are disjoint from the page's), the freed pages after it (`freedOK_free`), and its token, moved
to the freed pages' (`pgToks_fresh`, `pgToks_insert`).
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem rb_w64_add_nat (a b : Nat) (h : a + b < 2 ^ 64) :
    W64 (a : Int) + W64 (b : Int) = W64 ((a + b : Nat) : Int) := by
  word

theorem rb_w64_nat_inj (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h1 : uint.Z (W64 (a : Int)) = a := by word
  have h2 : uint.Z (W64 (b : Int)) = b := by word
  rw [h] at h1; omega

theorem rb_pageOverflow_lt (pg : List w8) : pageOverflow pg < 2 ^ 32 := by
  have := leAt_lt pg 12 4
  unfold pageOverflow; simpa using this

/-- A page of the view: its id and its span are small. -/
theorem view_span_lt (W : WView) (hv : viewOK W) (id : Nat) (pg : List w8)
    (hpg : W.pages !! id = some pg) : id + (1 + pageOverflow pg) < 2 ^ 43 := by
  have h1 := hv.2.2.2.1 id pg hpg
  have h2 := hv.2.1
  have h3 := rb_pageOverflow_lt pg
  have h4 : id < 2 ^ 42 := by
    rcases Nat.lt_or_ge id (2 ^ 42) with hc | hc
    · exact hc
    · have : 2 ^ 42 * 80 ≤ id * W.ps := Nat.mul_le_mul hc h2
      omega
  omega

theorem runIds_slot' (id n : Nat) (hn : id + n < 2 ^ 64) (x : w64) (hx : x ∈ runIds (W64 id) n) :
    ∃ k < n, x = W64 ((id + k : Nat) : Int) := by
  unfold runIds at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hk
  exact ⟨k, hk, rb_w64_add_nat id k (by omega)⟩

theorem slot_mem_runIds (id n k : Nat) (hn : id + n < 2 ^ 64) (hk : k < n) :
    W64 ((id + k : Nat) : Int) ∈ runIds (W64 id) n := by
  unfold runIds
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rb_w64_add_nat id k (by omega)⟩

/-- The page `id` of the view, not freed yet, is not pending for the writer. -/
theorem freedOK_hnew (W : WView) (hv : viewOK W) (fl : FLState) (txid : w64)
    (F : GMap Nat (List w8)) (h : freedOK W fl txid F) (hdisj : pagesDisjoint W.pages)
    (id : Nat) (pg : List w8) (hpg : W.pages !! id = some pg) (hF : F !! id = none) :
    ∀ pd, fl.pending !! txid = some pd →
      ∀ x ∈ runIds (W64 id) (1 + pageOverflow pg), x ∉ pd.ids := by
  intro pd hpd x hx hxi
  have hs := view_span_lt W hv id pg hpg
  obtain ⟨k, hk, rfl⟩ := runIds_slot' id _ (by omega) x hx
  obtain ⟨id', pg', k', hF', hk', he⟩ := h.2.2 pd hpd _ hxi
  have hpg' := h.2.1 id' pg' hF'
  have hs' := view_span_lt W hv id' pg' hpg'
  have heq := rb_w64_nat_inj _ _ (by omega) (by omega) he
  have hne : id ≠ id' := by rintro rfl; rw [hF] at hF'; cases hF'
  rcases hdisj id pg id' pg' hpg hpg' hne with h1 | h1 <;> omega

/-- The freed pages after `Free` of the page `id` of the view. -/
theorem freedOK_free (W : WView) (hv : viewOK W) (fl : FLState) (txid : w64)
    (F : GMap Nat (List w8)) (h : freedOK W fl txid F) (id : Nat) (pg : List w8)
    (hpg : W.pages !! id = some pg) (hF : F !! id = none) :
    freedOK W (fl.freePages txid (W64 id) (1 + pageOverflow pg)) txid (<[id := pg]> F) := by
  have hs := view_span_lt W hv id pg hpg
  obtain ⟨h1, h2, h3⟩ := h
  have hlook : (fl.freePages txid (W64 id) (1 + pageOverflow pg)).pending !! txid =
      some ⟨((fl.pending !! txid).getD ⟨[], [], 0⟩).ids ++ runIds (W64 id) (1 + pageOverflow pg),
        ((fl.pending !! txid).getD ⟨[], [], 0⟩).alloctx ++
          List.replicate (1 + pageOverflow pg) ((fl.allocs !! W64 id).getD 0),
        ((fl.pending !! txid).getD ⟨[], [], 0⟩).lastReleaseBegin⟩ := by
    unfold FLState.freePages; simp only; rw [GMap.lookup_insert]
  refine ⟨?_, ?_, ?_⟩
  · intro id' pg' hF' k hk
    refine ⟨_, hlook, ?_⟩
    show _ ∈ _ ++ _
    rw [GMap.lookup_insert_Some] at hF'
    rcases hF' with ⟨rfl, rfl⟩ | ⟨_, hF'⟩
    · exact List.mem_append_right _ (slot_mem_runIds _ _ _ (by omega) hk)
    · obtain ⟨pd, hpd, hx⟩ := h1 id' pg' hF' k hk
      rw [hpd]; exact List.mem_append_left _ hx
  · intro id' pg' hF'
    rw [GMap.lookup_insert_Some] at hF'
    rcases hF' with ⟨rfl, rfl⟩ | ⟨_, hF'⟩
    · exact hpg
    · exact h2 id' pg' hF'
  · intro pd hpd x hx
    rw [hlook] at hpd; cases hpd
    rcases List.mem_append.1 hx with hx | hx
    · cases hp : fl.pending !! txid with
      | none => rw [hp] at hx; simp at hx
      | some pd0 =>
        rw [hp] at hx
        obtain ⟨id', pg', k, hF', hk, rfl⟩ := h3 pd0 hp x hx
        have hne : id' ≠ id := by rintro rfl; rw [hF] at hF'; cases hF'
        exact ⟨id', pg', k, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hF', hk, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := runIds_slot' id _ (by omega) x hx
      exact ⟨id, pg, k, GMap.lookup_insert _ _ _, hk, rfl⟩

end pure

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- A token held apart from the tokens of `F` is not one of `F`'s. -/
theorem pgToks_fresh (γ : GName) (F : GMap Nat (List w8)) (id : Nat) :
    pgToks (GF := GF) γ F ∗ id ↪[γ] () ⊢ pgToks γ F ∗ id ↪[γ] () ∗ ⌜F !! id = none⌝ := by
  iintro ⟨HF, Ht⟩
  cases hF : F !! id with
  | none => iframe; ipureintro; rfl
  | some pg =>
    unfold pgToks
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Nat) (Φ := fun id _ => (id ↪[γ] () : IProp GF))
      (show Std.get? F id = some pg from hF)).1 $$ HF with ⟨Ht', -⟩
    icases ghostMapElem_ne γ id id (DFrac.own 1) () () $$ Ht Ht' with %hne
    exact absurd rfl hne

theorem pgToks_insert (γ : GName) (F : GMap Nat (List w8)) (id : Nat) (pg : List w8)
    (hF : F !! id = none) :
    pgToks (GF := GF) γ F ∗ id ↪[γ] () ⊢ pgToks γ (<[id := pg]> F) := by
  unfold pgToks
  iintro ⟨HF, Ht⟩
  iapply (BigSepM.bigSepM_insert (M := GMap Nat) (Φ := fun id _ => (id ↪[γ] () : IProp GF))
    (show Std.get? F id = none from hF)).2
  iframe

open Classical in
/-- The tokens of the view's page `id` alone. -/
theorem pgToks_single (γ : GName) (P : GMap Nat (List w8)) (id : Nat) (pg : List w8)
    (hpg : P !! id = some pg) :
    pgToks (GF := GF) γ (GMap.filter (fun i _ => decide (i = id)) P) ⊣⊢ id ↪[γ] () := by
  have he : GMap.filter (fun i _ => decide (i = id)) P = {[id := pg]} := by
    apply GMap.ext; intro k
    show (P !! k).filter (fun _ => decide (k = id)) = ({[id := pg]} : GMap Nat (List w8)) !! k
    by_cases hk : k = id
    · subst hk; rw [hpg]; simp [Option.filter, GMap.lookup_singleton]
    · rw [GMap.lookup_singleton_ne pg (Ne.symm hk)]; cases P !! k <;> simp [Option.filter, hk]
  rw [he]; unfold pgToks
  exact BigSepM.bigSepM_singleton

end toks

end bbolt
end EtcdGrove
end Perennial
