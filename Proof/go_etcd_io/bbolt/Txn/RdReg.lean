/-
A reader's registration (U5 of `notes/bbolt-proof-plan.md`; design §3.11 "Reader begin"): its
transaction names, its key in `metaR`'s readers' txids (`fltx`), and its entry in the
transactions' invariant.
-/
module

public import Proof.go_etcd_io.bbolt.Txn.Txs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx hos sem in
/-- A reader's names: its agreed state, `ex`, the handle registry, `done` and the view at the
fixed key `null` (`viewOf`'s reader key; the writer's registries are not used). -/
theorem rd_names_alloc (c : TxViewC) (x : TxX) (v : View) :
    ⊢ |==> ∃ n : TxNames, ghostVar (GF := GF) n.v 1 (c, x) ∗ ghostVar (GF := GF) n.ex 1 () ∗
      ghostMapAuth (GF := GF) n.rbk 1 (∅ : GMap Loc RHandle) ∗ ghostVar (GF := GF) n.done 1 false ∗
      (null ↪[n.vw]□ v : IProp GF) := by
  imod ghostVar_alloc (GF := GF) (c, x) with ⟨%γv, Hv⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γe, He⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := RHandle) with ⟨%γr, Hr⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γd, Hd⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := View) with ⟨%γw, Hw⟩
  imod (ghost_map_insert_persist (GF := GF) null v (GMap.lookup_empty _)) $$ Hw with ⟨-, Hf⟩
  imodintro
  iexists ⟨γv, γe, default, γr, default, γd, default, γw⟩
  iframe

/-- A fresh key of a finite map of naturals. -/
theorem gmap_nat_fresh {V : Type} (F : GMap Nat V) : ∃ k, F !! k = none := by
  obtain ⟨k, hk⟩ := Iris.Std.List.fresh (F.toList.map Prod.fst)
  refine ⟨k, ?_⟩
  rcases h : F !! k with _ | x
  · rfl
  · exact absurd (List.mem_map.2 ⟨(k, x), (GMap.mem_toList _ _ _).2 h, rfl⟩) hk

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- The bindings of a map with a fresh key inserted. -/
theorem toList_insert_fresh_perm {V : Type} (m : GMap Nat V) (k : Nat) (v : V)
    (hk : m !! k = none) : (m.insert k v).toList.Perm ((k, v) :: m.toList) := by
  have hnd : ∀ (M : GMap Nat V), M.toList.Nodup := fun M =>
    List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e)) (GMap.toList_keys_nodup M)
  rw [List.perm_ext_iff_of_nodup (hnd _)]
  · intro ⟨k', v'⟩
    rw [GMap.mem_toList, List.mem_cons, GMap.mem_toList]
    by_cases h : k = k'
    · subst h
      rw [GMap.lookup_insert, hk]
      simp [eq_comm]
    · rw [GMap.lookup_insert_ne _ _ h]
      simp [Ne.symm h]
  · refine List.nodup_cons.2 ⟨fun hm => ?_, hnd _⟩
    rw [GMap.mem_toList, hk] at hm
    cases hm

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- The readers' txids with a new reader's: the freelist's `ro ++ [t]`. -/
theorem ro_insert_perm (F : GMap Nat w64) (k : Nat) (t : w64) (ro : List w64)
    (hk : F !! k = none) (hro : ro.Perm (F.toList.map Prod.snd)) :
    (ro ++ [t]).Perm ((F.insert k t).toList.map Prod.snd) := by
  have h1 := ((toList_insert_fresh_perm F k t hk).map Prod.snd)
  simp only [List.map_cons] at h1
  exact (List.perm_append_singleton t ro).trans ((hro.cons t).trans h1.symm)

omit go_gctx sem in
private theorem pagesInv_timeless_r (B : BNs) (p : GoString) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) B σ W) := by
    intro σ W; unfold bytesWit; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p off dq xs) := fun _ _ _ => by
      unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
    unfold osSlot; infer_instance
  unfold pagesInv
  infer_instance

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- The readers' txids without a leaving reader's: the freelist's `ro.erase t`. -/
theorem ro_delete_perm (F : GMap Nat w64) (k : Nat) (t : w64) (ro ro' : List w64)
    (hk : F !! k = some t) (hro : ro.Perm (F.toList.map Prod.snd)) (hro' : ro'.Perm (ro.erase t)) :
    ro'.Perm ((GMap.delete k F).toList.map Prod.snd) := by
  have hd : (GMap.delete k F) !! k = none := GMap.lookup_delete F k
  have he : <[k := t]> (GMap.delete k F) = F := by
    apply GMap.ext; intro k'
    by_cases h : k = k'
    · subst h; rw [GMap.lookup_insert, hk]
    · rw [GMap.lookup_insert_ne _ _ h, GMap.lookup_delete_iff]
      simp only [h, ↓reduceIte]
  have h1 := ((toList_insert_fresh_perm (GMap.delete k F) k t hd).map Prod.snd)
  rw [he] at h1
  simp only [List.map_cons] at h1
  have h2 : (ro.erase t).Perm ((t :: ((GMap.delete k F).toList.map Prod.snd)).erase t) :=
    (hro.trans h1).erase t
  simp only [List.erase_cons_head] at h2
  exact hro'.trans h2

section store
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

omit sem in
/-- **The committed tree's pages lie inside the mapping** (`storeOK`: the store slots below
`l / 4096`), read under `metalock` and a share of the mapping. -/
theorem store_pages_bound (C : CommitSt) (b : Loc) (l : Nat) (q : Qp) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map q (some (b, l) : MapSt) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map q (some (b, l) : MapSt) ∗
      ⌜∀ id pg, C.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝ := by
  iintro ⟨#Hinv, Hcur, Hmap⟩
  have := pagesInv_timeless_r (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  have hb := Hok.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hms.symm
  imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hbw Hml] with -
  · inext; iexists σ, W; iframe; ipureintro; exact Hok
  imodintro
  iframe
  ipureintro
  intro id pg hpg
  have hs : id ∈ storeSlots σ := by
    unfold storeSlots
    rw [Perennial.mem_list_dedup, List.mem_append]
    left
    unfold treeSlots
    rw [mem_pagesSlots_iff]
    exact ⟨id, pg, hC ▸ hpg, Nat.le_refl _, by omega⟩
  have := hb id hs
  have h4 : (id + 1) * 4096 ≤ l / 4096 * 4096 := Nat.mul_le_mul_right _ this
  have h5 := Nat.div_mul_le_self l 4096
  exact Nat.le_trans h4 h5

end store

end reg

end bbolt
end EtcdGrove
end Perennial
