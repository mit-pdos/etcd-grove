/- Lean-first (no Rocq counterpart).

# The history as `Save` writes it (P6 E0, `notes/etcd-dist-d6.md` §10, `notes/wal-p6-handoff.md`)

Since the torn-`Save` fix (the fork's `2bd3048d7`), `Save(st, ents)` with entries always ends with a
state record: `st`'s, or, when `st` is empty, `w.state`'s, the hard state last saved (`walLastHS` of the
history before it; `encodeState`, S/wal.go). So the records of `.save h es` depend on the history
before it. `normFrom p H` rewrites each such `Save` to the one with the state it writes
(`normOp`): `.save hsZero es` (entries, empty state) after a history whose last state is `p` becomes
`.save p es`. Every read of the history is unchanged by it (`walFoldChkFrom_normFrom`,
`walLastHS_normH`, ...): `phsNext p p = p`. The encoding layer (`histM`, `WalFs.Abs`) works on
`normH` of the WAL's history, so that an operation's records (`opDs`) are a function of the operation
alone.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section norm
variable [GooseExts]

instance : DecidablePred hsEmptyP := fun h => by unfold hsEmptyP; infer_instance

/-- The running hard state after an operation (`walLastHS`'s step). -/
def opHS (p : HardStateM) : WalOp → HardStateM
  | .save h _ => phsNext p h
  | .snap _ _ => p

/-- **The operation `Save` writes after a history whose last hard state is `p`**: a `Save` of
entries with an empty state writes `p`'s state record (`encodeState(w.state)`). -/
def normOp (p : HardStateM) : WalOp → WalOp
  | .save h es => if es ≠ [] ∧ hsEmptyP h then .save p es else .save h es
  | .snap m al => .snap m al

/-- **The history as written**, from the running hard state `p`. -/
def normFrom : HardStateM → WalHist → WalHist
  | _, [] => []
  | p, o :: H => normOp p o :: normFrom (opHS p o) H

/-- **The history as written** (`normFrom` from `Create`'s empty state). -/
def normH (H : WalHist) : WalHist := normFrom hsZero H

theorem walLastHS_eq_foldl (H : WalHist) : walLastHS H = H.foldl opHS hsZero := by
  unfold walLastHS
  congr 1
  funext p o
  cases o <;> rfl

theorem phsNext_self' (p : HardStateM) : phsNext p p = p := by
  unfold phsNext; split <;> [skip; rfl]
  rename_i h
  obtain ⟨t, v, c⟩ := p
  simp only at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl

theorem phsNext_of_hsEmptyP {p h : HardStateM} (he : hsEmptyP h) : phsNext p h = p :=
  phsNext_empty p h he

/-- A normalized operation moves the running state as the operation does. -/
theorem opHS_normOp (p : HardStateM) (o : WalOp) : opHS p (normOp p o) = opHS p o := by
  cases o with
  | save h es =>
    unfold normOp
    split
    · rename_i hc; simp only [opHS]; rw [phsNext_self', phsNext_of_hsEmptyP hc.2]
    · rfl
  | snap m al => rfl

@[simp] theorem normFrom_length (p : HardStateM) (H : WalHist) : (normFrom p H).length = H.length := by
  induction H generalizing p with
  | nil => rfl
  | cons o H ih => simp [normFrom, ih]

@[simp] theorem normH_length (H : WalHist) : (normH H).length = H.length := normFrom_length _ _

theorem foldl_opHS_normFrom (p : HardStateM) (H : WalHist) :
    (normFrom p H).foldl opHS p = H.foldl opHS p := by
  induction H generalizing p with
  | nil => rfl
  | cons o H ih => simp only [normFrom, List.foldl_cons, opHS_normOp, ih]

theorem walLastHS_normH (H : WalHist) : walLastHS (normH H) = walLastHS H := by
  rw [walLastHS_eq_foldl, walLastHS_eq_foldl]; exact foldl_opHS_normFrom _ _

theorem normFrom_append (p : HardStateM) (A B : WalHist) :
    normFrom p (A ++ B) = normFrom p A ++ normFrom (A.foldl opHS p) B := by
  induction A generalizing p with
  | nil => rfl
  | cons o A ih => simp [normFrom, ih]

theorem normH_append (A B : WalHist) :
    normH (A ++ B) = normH A ++ normFrom (walLastHS A) B := by
  rw [normH, normFrom_append, walLastHS_eq_foldl]; rfl

/-- A normalized concatenation: each part normalized from its running state. -/
theorem normFrom_append_fix {p : HardStateM} {A B : WalHist} (h : normFrom p (A ++ B) = A ++ B) :
    normFrom p A = A ∧ normFrom (A.foldl opHS p) B = B := by
  rw [normFrom_append] at h
  exact List.append_inj h (normFrom_length _ _)

/-- The suffix of a normalized concatenation, from the prefix's last state. -/
theorem normFrom_suffix_fix {A B : WalHist} (h : normFrom hsZero (A ++ B) = A ++ B) :
    normFrom (walLastHS A) B = B := by
  rw [walLastHS_eq_foldl]; exact (normFrom_append_fix h).2

theorem normOp_idem (p : HardStateM) (o : WalOp) : normOp p (normOp p o) = normOp p o := by
  cases o with
  | save h es =>
    unfold normOp
    by_cases hc : es ≠ [] ∧ hsEmptyP h
    · rw [if_pos hc]
      by_cases hp : hsEmptyP p
      · simp [hc.1, hp]
      · simp [hp]
    · rw [if_neg hc, if_neg hc]
  | snap m al => rfl

/-- **The normalization is idempotent**: a written history is its own normalization. -/
theorem normFrom_idem (p : HardStateM) (H : WalHist) : normFrom p (normFrom p H) = normFrom p H := by
  induction H generalizing p with
  | nil => rfl
  | cons o H ih => simp only [normFrom, normOp_idem, opHS_normOp, ih]

theorem normH_drop_fix (H : WalHist) (k : Nat) :
    normFrom (walLastHS ((normH H).take k)) ((normH H).drop k) = (normH H).drop k := by
  rw [normH_take, walLastHS_normH, normH_drop, normFrom_idem]

theorem normH_snoc (H : WalHist) (o : WalOp) :
    normH (H ++ [o]) = normH H ++ [normOp (walLastHS H) o] := by
  rw [normH_append]; rfl

theorem normFrom_take (p : HardStateM) (H : WalHist) (j : Nat) :
    (normFrom p H).take j = normFrom p (H.take j) := by
  induction H generalizing p j with
  | nil => simp [normFrom]
  | cons o H ih =>
    cases j with
    | zero => simp [normFrom]
    | succ j => simp [normFrom, ih]

theorem normH_take (H : WalHist) (j : Nat) : (normH H).take j = normH (H.take j) :=
  normFrom_take _ _ _

theorem normFrom_drop (p : HardStateM) (H : WalHist) (k : Nat) :
    (normFrom p H).drop k = normFrom ((H.take k).foldl opHS p) (H.drop k) := by
  induction H generalizing p k with
  | nil => simp [normFrom]
  | cons o H ih =>
    cases k with
    | zero => simp [normFrom]
    | succ k => simp [normFrom, ih]

theorem normH_drop (H : WalHist) (k : Nat) :
    (normH H).drop k = normFrom (walLastHS (H.take k)) (H.drop k) := by
  rw [normH, normFrom_drop, walLastHS_eq_foldl]

theorem normFrom_getElem? (p : HardStateM) (H : WalHist) (i : Nat) :
    (normFrom p H)[i]? = H[i]?.map (normOp ((H.take i).foldl opHS p)) := by
  induction H generalizing p i with
  | nil => simp [normFrom]
  | cons o H ih =>
    cases i with
    | zero => simp [normFrom]
    | succ i => simp [normFrom, ih]

/-- An operation's kind and entries are kept by the normalization. -/
def opShape : WalOp → Option (List EntryM)
  | .save _ es => some es
  | .snap _ _ => none

theorem normOp_save (p h : HardStateM) (es : List EntryM) :
    ∃ h', normOp p (.save h es) = .save h' es ∧ (hsEmptyP h' ∧ es = [] ↔ hsEmptyP h ∧ es = []) := by
  unfold normOp
  split
  · rename_i hc; exact ⟨p, rfl, by simp [hc.1]⟩
  · exact ⟨h, rfl, Iff.rfl⟩

theorem normOp_snap (p : HardStateM) (m : SnapshotMetadataM) (al : Bool) :
    normOp p (.snap m al) = .snap m al := rfl

/-- `normOp` of a `Save` of no entries is the `Save`. -/
theorem normOp_save_nil (p h : HardStateM) : normOp p (.save h []) = .save h [] := by
  simp [normOp]

/-- The filter of `walKeep` (it drops only snapshot records) commutes with the normalization. -/
theorem normFrom_filter_walKeep (c : Nat) (p : HardStateM) (H : WalHist) :
    (normFrom p H).filter (walKeep c) = normFrom p (H.filter (walKeep c)) := by
  induction H generalizing p with
  | nil => rfl
  | cons o H ih =>
    cases o with
    | save h es =>
      obtain ⟨h', he, -⟩ := normOp_save p h es
      simp only [normFrom, he, List.filter_cons, walKeep, ite_true, ih]
      rfl
    | snap m al =>
      simp only [normFrom, normOp_snap, List.filter_cons, walKeep, opHS]
      split <;> simp [ih, normFrom, normOp_snap, opHS]

/-- **The reader's fold is unchanged by the normalization** (from the running state `σ.hs`). -/
theorem walFoldChkFrom_normFrom (σ : StorContents) (H : WalHist) :
    walFoldChkFrom σ (normFrom σ.hs H) = walFoldChkFrom σ H := by
  induction H generalizing σ with
  | nil => rfl
  | cons o H ih =>
    cases o with
    | snap m al =>
      simp only [normFrom, normOp_snap, walFoldChkFrom, opHS]
      have hhs : (walSaveSnap σ m).hs = σ.hs := by unfold walSaveSnap; split <;> rfl
      rw [← hhs, ih]
    | save h es =>
      simp only [normFrom, walFoldChkFrom, opHS]
      unfold normOp
      split
      · rename_i hc
        simp only [walFoldChkFrom, phsNext_self', phsNext_of_hsEmptyP hc.2]
        cases es.foldlM (fun ents e => readEnt σ.b ents e) σ.ents with
        | none => rfl
        | some ents =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          exact ih { σ with ents := ents }
      · simp only [walFoldChkFrom]
        cases es.foldlM (fun ents e => readEnt σ.b ents e) σ.ents with
        | none => rfl
        | some ents =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          exact ih { σ with hs := phsNext σ.hs h, ents := ents }

theorem walNewest_normFrom (p : HardStateM) (H : WalHist) : walNewest (normFrom p H) = walNewest H := by
  unfold walNewest
  suffices ∀ b, (normFrom p H).foldl (fun best o => match o with
      | .snap m _ => match best with
        | none => some m
        | some b => if uint.nat b.Index' ≤ uint.nat m.Index' then some m else best
      | .save _ _ => best) b = H.foldl (fun best o => match o with
      | .snap m _ => match best with
        | none => some m
        | some b => if uint.nat b.Index' ≤ uint.nat m.Index' then some m else best
      | .save _ _ => best) b from this none
  induction H generalizing p with
  | nil => intro b; rfl
  | cons o H ih =>
    intro b
    cases o with
    | save h es =>
      obtain ⟨h', he, -⟩ := normOp_save p h es
      simp only [normFrom, he, List.foldl_cons]; exact ih _ _
    | snap m al => simp only [normFrom, normOp_snap, List.foldl_cons]; exact ih _ _

theorem walRead_normH (H : WalHist) : walRead (normH H) = walRead H := by
  unfold walRead
  rw [walLastHS_normH, normH, normFrom_filter_walKeep]
  exact walFoldChkFrom_normFrom walFresh _

theorem walReadFrom_normH (H : WalHist) (k : Nat) : walReadFrom (normH H) k = walReadFrom H k := by
  unfold walReadFrom
  simp only [walLastHS_normH, normH_take, normH_drop, normFrom_filter_walKeep, walNewest_normFrom]
  split
  · rename_i hn; rw [hn]
  · rename_i m hn
    rw [hn]
    exact walFoldChkFrom_normFrom ⟨walLastHS (H.take k), _, _, []⟩ _

theorem walReadCut_normH (H : WalHist) (k : Nat) : walReadCut (normH H) k = walReadCut H k := by
  unfold walReadCut; split
  · exact walRead_normH H
  · exact walReadFrom_normH H k

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
  · suffices ∀ x, (normFrom p H).foldl (fun x o => match o with
        | .save _ es => (es.getLast?.map (fun e => uint.nat e.Index')).getD x
        | .snap _ _ => x) x = H.foldl (fun x o => match o with
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
  · suffices ∀ x, (normFrom p H).foldl (fun x o => match o with
        | .save _ _ => x
        | .snap m _ => max x (uint.nat m.Index')) x = H.foldl (fun x o => match o with
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

/-- **The written history of a WAL's raw history** (the encoding layer's: `WalFs.histM`). -/
def histN (H : List (WalOpG WalEnt)) : WalHist := normH (H.map WalOpG.toM)

@[simp] theorem histN_length (H : List (WalOpG WalEnt)) : (histN H).length = H.length := by
  simp [histN, normH_length]

theorem histN_take (H : List (WalOpG WalEnt)) (j : Nat) : (histN H).take j = histN (H.take j) := by
  simp [histN, normH_take, List.map_take]

theorem histN_snoc (H : List (WalOpG WalEnt)) (o : WalOpG WalEnt) :
    histN (H ++ [o]) = histN H ++ [normOp (walLastHS (H.map WalOpG.toM)) o.toM] := by
  simp [histN, normH_snoc]

/-- **The operation as written after the raw history `H`** (`histN_snoc'`). -/
def wop (H : List (WalOpG WalEnt)) (o : WalOpG WalEnt) : WalOp := normOp (walLastHS (H.map WalOpG.toM)) o.toM

theorem histN_snoc' (H : List (WalOpG WalEnt)) (o : WalOpG WalEnt) :
    histN (H ++ [o]) = histN H ++ [wop H o] := histN_snoc H o

/-- **The state `Save(hs, es)` writes after the state `p`** (`encodeState`'s argument: `w.state` when
`hs` is empty and there are entries). -/
def saveHS (p hs : HardStateM) (es : List EntryM) : HardStateM :=
  if es ≠ [] ∧ hsEmptyP hs then p else hs

theorem normOp_save_eq (p hs : HardStateM) (es : List EntryM) :
    normOp p (.save hs es) = .save (saveHS p hs es) es := by
  unfold normOp saveHS; split <;> rfl

/-- After a `Save` that writes a state record, the running state is the one it wrote. -/
theorem phsNext_saveHS {p hs : HardStateM} {es : List EntryM} (h : ¬ (es = [] ∧ hsEmptyP hs)) :
    phsNext p hs = saveHS p hs es := by
  unfold saveHS
  by_cases hE : hsEmptyP hs
  · have hne : es ≠ [] := fun h0 => h ⟨h0, hE⟩
    rw [if_pos ⟨hne, hE⟩]; exact phsNext_empty _ _ hE
  · rw [if_neg (fun hc => hE hc.2)]; unfold phsNext; exact if_neg hE

theorem walLastHS_histN (H : List (WalOpG WalEnt)) : walLastHS (histN H) = walLastHS (H.map WalOpG.toM) :=
  walLastHS_normH _

/-- **What a crash can leave of a WAL whose history is `H` with its first `n` operations synced,
since the torn-`Save` fix**: the first `j` operations (`n ≤ j ≤ |H|`). A `Save` a crash interrupts
reads back as none (its entry records, no record after them, are dropped by `ReadAll`); the trusted
`walImg` (`GooseLang/Ext/AbsDisk/Impl.lean`) also allows a torn `Save`, which no longer arises:
`walImgS_walImg`. -/
def walImgS {E : Type} (H : List (WalOpG E)) (n : Nat) (I : List (WalOpG E)) : Prop :=
  ∃ j, n ≤ j ∧ j ≤ H.length ∧ I = H.take j

theorem walImgS_walImg {E : Type} {H I : List (WalOpG E)} {n : Nat} (h : walImgS H n I) :
    walImg H n I := by
  obtain ⟨j, h1, h2, h3⟩ := h
  exact ⟨j, h1, h2, .inl h3⟩

end norm

end EtcdGrove
end Perennial
