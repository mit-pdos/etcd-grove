/-
Lean-first (no Rocq counterpart).

# The store's history, kept by its caller (D30j's local option)

The store's specs read etcd's key-values through `kvSeen γh σ` (`Store.lean`): every key-value of
the state, at its mod revision, is in the ghost map `γh`, read-only. The caller that hands the
store its updates keeps the map's authority with etcd's state (`histAuth γh σ`): every entry at a
revision at most the state's (`HistOk`), and the state seen. At each step of etcd's state that
the updates report (`KvNext`, `Updates.lean`), it extends the map with the new key-values, all at
the new revision, so none was there (`histAuth_next`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Updates

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The history's entries are at revisions at most the state's. -/
def HistOk (H : GMap (GoString × w64) GoString) (σ : KVState) : Prop :=
  ∀ k r v, H !! (k, r) = some v → uint.nat r ≤ σ.rev

/-- **The history's authority at etcd's state `σ`** (see the file header). -/
def histAuth (γh : GName) (σ : KVState) : IProp GF :=
  iprop(∃ H, ghostMapAuth γh 1 H ∗ ⌜HistOk H σ⌝ ∗ kvSeen γh σ)

instance histAuth_timeless (γh : GName) (σ : KVState) : Timeless (histAuth (GF := GF) γh σ) := by
  unfold histAuth kvSeen; infer_instance

/-- The state, seen. -/
theorem histAuth_seen (γh : GName) (σ : KVState) :
    histAuth (GF := GF) γh σ ⊢ histAuth γh σ ∗ kvSeen γh σ := by
  iintro H
  iunfold histAuth at H
  icases H with ⟨%H, HA, %Hok, #Hs⟩
  iframe Hs
  iunfold histAuth
  iexists H
  iframe HA Hs
  ipureintro; exact Hok

/-- Key-values at the revision `r`, none there, with distinct keys, added. -/
theorem hist_ins (γh : GName) (r : w64) (l : List EtcdKv) :
    ∀ (H : GMap (GoString × w64) GoString), (∀ v ∈ l, v.modRev = r) →
    (l.map EtcdKv.key).Nodup → (∀ v ∈ l, H !! (v.key, r) = none) →
    ghostMapAuth (GF := GF) γh 1 H ⊢ |==> ∃ H', ghostMapAuth γh 1 H' ∗
      ([∗list] v ∈ l, ghostMapElem γh (v.key, v.modRev) DFrac.discard v.value) ∗
      ⌜∀ kr x, H' !! kr = some x → H !! kr = some x ∨ kr.2 = r⌝ := by
  induction l with
  | nil =>
    intro H _ _ _
    iintro HA
    imodintro
    iexists H
    iframe HA
    isplitl []
    · iempintro
    ipureintro; exact fun _ _ h => Or.inl h
  | cons v l ih =>
    intro H hm hnd hfr
    have hv := hm v List.mem_cons_self
    have hnd' := List.nodup_cons.1 hnd
    iintro HA
    imod ghost_map_insert_persist (v.key, r) v.value (hfr v List.mem_cons_self) $$ HA
      with ⟨HA, #He⟩
    have hfr' : ∀ w ∈ l, (H.insert (v.key, r) v.value) !! (w.key, r) = none := by
      intro w hw
      have hk : v.key ≠ w.key := fun e => hnd'.1 (e ▸ List.mem_map_of_mem hw)
      rw [GMap.lookup_insert_ne _ _ (fun e => hk (Prod.mk.inj e).1)]
      exact hfr w (List.mem_cons_of_mem _ hw)
    imod (ih (H.insert (v.key, r) v.value) (fun w hw => hm w (List.mem_cons_of_mem _ hw))
      hnd'.2 hfr') $$ HA with ⟨%H', HA, Hl, %Hh⟩
    imodintro
    iexists H'
    iframe HA
    isplitl [Hl]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      rw [hv]
      iframe He Hl
    ipureintro
    intro kr x hx
    rcases Hh kr x hx with h | h
    · by_cases e : (v.key, r) = kr
      · subst e; exact Or.inr rfl
      · rw [GMap.lookup_insert_ne _ _ e] at h
        exact Or.inl h
    · exact Or.inr h

open Classical in
/-- **The history follows a step of etcd's state** (see the file header): sorted (distinct
keys), its revision fitting a word. -/
theorem histAuth_next (γh : GName) (σ σ' : KVState) (hn : KvNext σ σ') (hr : σ'.rev < 2 ^ 64)
    (hs : σ'.kvs.Pairwise etcdKvLess) :
    histAuth (GF := GF) γh σ ⊢ |==> histAuth γh σ' := by
  rcases hn with rfl | ⟨hrev, hnew⟩
  · iintro H; imodintro; iexact H
  iintro H
  iunfold histAuth at H
  icases H with ⟨%H, HA, %Hok, #Hs⟩
  have hR : uint.nat (W64 ((σ'.rev : Nat) : Int)) = σ'.rev := by
    simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
  let l := σ'.kvs.filter (fun v => decide (v ∉ σ.kvs))
  have hmem : ∀ v, v ∈ l ↔ v ∈ σ'.kvs ∧ v ∉ σ.kvs := fun v => by simp [l]
  have hm : ∀ v ∈ l, v.modRev = W64 ((σ'.rev : Nat) : Int) := by
    intro v hv
    obtain ⟨h1, h2⟩ := (hmem v).1 hv
    rcases hnew v h1 with h | h
    · exact absurd h h2
    · exact h
  have hnd : (l.map EtcdKv.key).Nodup := by
    have hp : (l.map EtcdKv.key).Pairwise go.GoStringLt := List.pairwise_map.2 (hs.filter _)
    exact hp.imp (fun h e => by subst e; exact go.goStringLt_irrefl _ h)
  have hfr : ∀ v ∈ l, H !! (v.key, W64 ((σ'.rev : Nat) : Int)) = none := by
    intro v _
    cases h : H !! (v.key, W64 ((σ'.rev : Nat) : Int)) with
    | none => rfl
    | some x =>
      have := Hok _ _ _ h
      omega
  imod (hist_ins γh (W64 ((σ'.rev : Nat) : Int)) l H hm hnd hfr) $$ HA with ⟨%H', HA, #Hl, %Hh⟩
  imodintro
  iunfold histAuth
  iexists H'
  iframe HA
  isplitr
  · ipureintro
    intro k r v hv
    rcases Hh _ _ hv with h | h
    · have := Hok _ _ _ h; omega
    · simp only at h; rw [h]; omega
  iunfold kvSeen
  imodintro
  iintro %v %hv
  by_cases hin : v ∈ σ.kvs
  · iunfold kvSeen at Hs
    iapply Hs
    ipureintro; exact hin
  · iapply (BigSepL.bigSepL_mem ((hmem v).2 ⟨hv, hin⟩)) $$ Hl

end defs

end k8s
end EtcdGrove
end Perennial
