/- Lean-first (no Rocq counterpart).

# The normalization's invariance of `WalDisk`'s readers (P6; `WalNorm.lean`)

Split from `WalNorm.lean`, which `WalEncRecs` imports below `WalDisk`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalNorm
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section norm
variable [GooseExts]

theorem walValidSnaps_normH (H : WalHist) (k : Nat) : walValidSnaps (normH H) k = walValidSnaps H k := by
  unfold walValidSnaps
  rw [walLastHS_normH, normH_drop]
  congr 1
  generalize walLastHS (H.take k) = p
  induction H.drop k generalizing p with
  | nil => rfl
  | cons o H ih =>
    cases o with
    | save h es =>
      obtain ⟨h', he, -⟩ := normOp_save p h es
      simp only [normFrom, he, List.filterMap_cons]; exact ih _
    | snap m al => simp only [normFrom, normOp_snap, List.filterMap_cons]; rw [ih]

theorem walCutPos_normH (H : WalHist) (b : Nat) : walCutPos (normH H) b ↔ walCutPos H b := by
  unfold walCutPos normH
  rw [normFrom_getElem?]
  cases H[b-1]? with
  | none => simp
  | some o =>
    cases o with
    | save h es =>
      obtain ⟨h', he, hiff⟩ := normOp_save ((H.take (b - 1)).foldl opHS hsZero) h es
      simp only [Option.map_some, he]
      constructor
      · rintro (h0 | ⟨h1, es1, e1, n1⟩ | ⟨m, al, e⟩)
        · exact .inl h0
        · cases e1; exact .inr (.inl ⟨h, es, rfl, fun hc => n1 (hiff.mpr hc)⟩)
        · cases e
      · rintro (h0 | ⟨h1, es1, e1, n1⟩ | ⟨m, al, e⟩)
        · exact .inl h0
        · cases e1; exact .inr (.inl ⟨h', es, rfl, fun hc => n1 (hiff.mp hc)⟩)
        · cases e
    | snap m al => simp [normOp_snap]

theorem walLastIdx_normFrom (p : HardStateM) (H : WalHist) : walLastIdx (normFrom p H) = walLastIdx H := by
  unfold walLastIdx
  congr 1
  · suffices ∀ x, (normFrom p H).foldl (fun (x : Nat) (o : WalOp) => match o with
        | .save _ es => (es.getLast?.map (fun e => uint.nat e.Index')).getD x
        | .snap _ _ => x) x = H.foldl (fun (x : Nat) (o : WalOp) => match o with
        | .save _ es => (es.getLast?.map (fun e => uint.nat e.Index')).getD x
        | .snap _ _ => x) x from this 0
    induction H generalizing p with
    | nil => intro x; rfl
    | cons o H ih =>
      intro x
      cases o with
      | save h es =>
        obtain ⟨h', he, -⟩ := normOp_save p h es
        simp only [normFrom, he, List.foldl_cons]; exact ih _ _
      | snap m al => simp only [normFrom, normOp_snap, List.foldl_cons]; exact ih _ _
  · suffices ∀ x, (normFrom p H).foldl (fun (x : Nat) (o : WalOp) => match o with
        | .save _ _ => x
        | .snap m _ => max x (uint.nat m.Index')) x = H.foldl (fun (x : Nat) (o : WalOp) => match o with
        | .save _ _ => x
        | .snap m _ => max x (uint.nat m.Index')) x from this 0
    induction H generalizing p with
    | nil => intro x; rfl
    | cons o H ih =>
      intro x
      cases o with
      | save h es =>
        obtain ⟨h', he, -⟩ := normOp_save p h es
        simp only [normFrom, he, List.foldl_cons]; exact ih _ _
      | snap m al => simp only [normFrom, normOp_snap, List.foldl_cons]; exact ih _ _

theorem walLastIdx_normH (H : WalHist) : walLastIdx (normH H) = walLastIdx H := walLastIdx_normFrom _ _


/-- The normalization keeps an operation's indices. -/
theorem walHasMaxIdx_normOp (p : HardStateM) (o : WalOp) :
    walHasMaxIdx [normOp p o] ↔ walHasMaxIdx [o] := by
  cases o with
  | save h es =>
    obtain ⟨h', he, -⟩ := normOp_save p h es
    rw [he]; simp [walHasMaxIdx]
  | snap m al => rw [normOp_snap]

theorem walHasMaxIdx_wop (H : List (WalOpG WalEnt)) (o : WalOpG WalEnt) :
    walHasMaxIdx [wop H o] ↔ walHasMaxIdx [o.toM] := walHasMaxIdx_normOp _ _

theorem walHasMaxIdx_cons (a : WalOp) (L : WalHist) :
    walHasMaxIdx (a :: L) ↔ walHasMaxIdx [a] ∨ walHasMaxIdx L := by
  simp [walHasMaxIdx]

/-- The normalization keeps the indices. -/
theorem walHasMaxIdx_normFrom (p : HardStateM) (H : WalHist) :
    walHasMaxIdx (normFrom p H) ↔ walHasMaxIdx H := by
  induction H generalizing p with
  | nil => exact Iff.rfl
  | cons o H ih => rw [normFrom, walHasMaxIdx_cons, walHasMaxIdx_cons o, walHasMaxIdx_normOp, ih]

end norm

end EtcdGrove
end Perennial
