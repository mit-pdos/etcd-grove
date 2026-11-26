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

theorem normH_getElem?_snap (H : WalHist) (i : Nat) (m : SnapshotMetadataM) (al : Bool) :
    (normH H)[i]? = some (.snap m al) ↔ H[i]? = some (.snap m al) := by
  unfold normH
  rw [normFrom_getElem?]
  cases H[i]? with
  | none => simp
  | some o =>
    cases o with
    | save h es =>
      obtain ⟨h', he, -⟩ := normOp_save ((H.take i).foldl opHS hsZero) h es
      simp [he]
    | snap m' al' => simp [normOp_snap]

theorem normH_getElem?_save (H : WalHist) (i : Nat) (es : List EntryM) :
    (∃ h, (normH H)[i]? = some (.save h es)) ↔ ∃ h, H[i]? = some (.save h es) := by
  unfold normH
  rw [normFrom_getElem?]
  cases H[i]? with
  | none => simp
  | some o =>
    cases o with
    | save h es' =>
      obtain ⟨h', he, -⟩ := normOp_save ((H.take i).foldl opHS hsZero) h es'
      simp [he]
    | snap m' al' => simp [normOp_snap]

theorem walLastSnapPos_normH (H : WalHist) (a : w64) : walLastSnapPos (normH H) a = walLastSnapPos H a := by
  unfold walLastSnapPos
  rw [show (normH H).length = H.length from normFrom_length _ _]
  congr 2
  apply List.filter_congr
  intro i _
  unfold normH
  rw [normFrom_getElem?]
  cases H[i]? with
  | none => rfl
  | some o =>
    cases o with
    | save h es =>
      obtain ⟨h', he, -⟩ := normOp_save ((H.take i).foldl opHS hsZero) h es
      simp [he]
    | snap m al => simp [normOp_snap]

theorem walRelGuard_normH (H : WalHist) (a : w64) (p : Nat) :
    walRelGuard (normH H) a p ↔ walRelGuard H a p := by
  unfold walRelGuard
  have hl : (normH H).length = H.length := normFrom_length _ _
  have hhs : ∀ j, walLastHS ((normH H).take j) = walLastHS (H.take j) := fun j => by
    rw [normH_take, walLastHS_normH]
  have hmx : walHasMaxIdx (normH H) ↔ walHasMaxIdx H := walHasMaxIdx_normFrom _ _
  simp only [hl, hhs, hmx]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun q j m al h es e hq ha hqj hj he => ?_, fun j m al hpj hj => ?_, h4⟩
    · obtain ⟨h', hj'⟩ := (normH_getElem?_save H j es).2 ⟨h, hj⟩
      exact h2 q j m al h' es e ((normH_getElem?_snap H q m al).2 hq) ha hqj hj' he
    · exact h3 j m al hpj ((normH_getElem?_snap H j m al).2 hj)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun q j m al h es e hq ha hqj hj he => ?_, fun j m al hpj hj => ?_, h4⟩
    · obtain ⟨h', hj'⟩ := (normH_getElem?_save H j es).1 ⟨h, hj⟩
      exact h2 q j m al h' es e ((normH_getElem?_snap H q m al).1 hq) ha hqj hj' he
    · exact h3 j m al hpj ((normH_getElem?_snap H j m al).1 hj)

theorem walGuardPos_normH (H : WalHist) (a : w64) : walGuardPos (normH H) a = walGuardPos H a := by
  unfold walGuardPos
  have hl : (normH H).length = H.length := normFrom_length _ _
  have hmx : walHasMaxIdx (normH H) ↔ walHasMaxIdx H := walHasMaxIdx_normFrom _ _
  have hex : (∃ (i : Nat) (m : SnapshotMetadataM) (al : Bool), (normH H)[i]? = some (WalOpG.snap m al) ∧
      m.Index' = a) ↔ (∃ (i : Nat) (m : SnapshotMetadataM) (al : Bool), H[i]? = some (WalOpG.snap m al) ∧
      m.Index' = a) := by
    simp only [normH_getElem?_snap]
  rw [walLastSnapPos_normH]
  by_cases h1 : walHasMaxIdx H
  · rw [if_pos (hmx.2 h1), if_pos h1, hl]
  rw [if_neg (fun h => h1 (hmx.1 h)), if_neg h1]
  by_cases h2 : a = W64 0
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : (∃ (i : Nat) (m : SnapshotMetadataM) (al : Bool), H[i]? = some (WalOpG.snap m al) ∧
      m.Index' = a) ∧ walRelGuard H a (walLastSnapPos H a)
  · rw [if_pos h3, if_pos ⟨hex.2 h3.1, (walRelGuard_normH H a _).2 h3.2⟩]
  · rw [if_neg h3, if_neg (fun h => h3 ⟨hex.1 h.1, (walRelGuard_normH H a _).1 h.2⟩), hl]

theorem walNameBound_normH (H : WalHist) (a : Nat) (strict : Bool) :
    walNameBound (normH H) a strict = walNameBound H a strict := by
  unfold walNameBound
  have hl : (normH H).length = H.length := normFrom_length _ _
  have hmx : walHasMaxIdx (normH H) ↔ walHasMaxIdx H := walHasMaxIdx_normFrom _ _
  have hli : ∀ b, walLastIdx ((normH H).take b) = walLastIdx (H.take b) := fun b => by
    rw [normH_take, walLastIdx_normH]
  by_cases h1 : walHasMaxIdx H
  · rw [if_pos (hmx.2 h1), if_pos h1, hl]
  rw [if_neg (fun h => h1 (hmx.1 h)), if_neg h1, hl]
  congr 2
  apply List.filter_congr
  intro b _
  rw [hli]
  exact decide_eq_decide.2 (and_congr_left' (walCutPos_normH H b))

theorem walReleasePos_normH (H : WalHist) (a : w64) : walReleasePos (normH H) a = walReleasePos H a := by
  unfold walReleasePos
  rw [walGuardPos_normH, walNameBound_normH]

theorem walOpenPos_normH (H : WalHist) (a : w64) : walOpenPos (normH H) a = walOpenPos H a := by
  unfold walOpenPos
  rw [walGuardPos_normH, walNameBound_normH]

end norm

end EtcdGrove
end Perennial
