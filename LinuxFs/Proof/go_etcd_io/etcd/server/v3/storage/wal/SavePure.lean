/- Lean-first (no Rocq counterpart).

# `Save`'s pure facts (W6; `WAL__Save.lean`)

After `Save`'s commit (`walHandleIn_append`), the handle's history is `H ++ [o]` with `o =
(save hs es).toRaw` and its `|opDs o|` records (the entries', then the state's unless empty) not yet
encoded. `SaveSt h hs es i hc`: the handle `hc` after `i` of them, from the quiescent `h` (the
loop's invariant); `SaveFin h hs es hc`: every record encoded, `w.state` the new history's last hard
state. Each callee's premise in terms of them: `saveEntry`'s (`SaveSt.entryPre`: the record, the
index bound when the entry is the last record), `saveState`'s (`SaveSt.statePre`), `cut`'s
(`walCutPos_save`, `SaveFin`'s facts). `not_walMustSync`: `raft.MustSync` false is `walMustSync`
false.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open WalEnc

section pure
variable [GooseExts]

theorem chainRecs_typData (c : w32) (D : List (w64 × List w8)) :
    (chainRecs walCodec c D).map (fun r => (r.typ, r.data)) = D := by
  induction D generalizing c with
  | nil => rfl
  | cons p D ih => obtain ⟨t, d⟩ := p; simp [chainRecs, ih]

/-- **The record `D[j]` in `T ++ chainRecs c D`**, addressed as the handle does (`rest = |D| - j`). -/
theorem recAt_chain (T : List WalRec) (c : w32) (D : List (w64 × List w8)) (j : Nat)
    (hj : j < D.length) :
    ((T ++ chainRecs walCodec c D)[(T ++ chainRecs walCodec c D).length - (D.length - j)]?).map
      (fun x => (x.typ, x.data)) = D[j]? := by
  rw [List.length_append, length_chainRecs,
    show T.length + D.length - (D.length - j) = T.length + j by omega,
    List.getElem?_append_right (by omega), show T.length + j - T.length = j by omega,
    ← List.getElem?_map, chainRecs_typData]

/-- A save's records: its entries', then its state's unless empty. -/
theorem opDs_save (Mr : WalMarshal) (hs : HardStateM) (es : List EntryM) :
    opDs Mr (WalOpG.save hs es).toRaw.toM = es.map (fun e => (entryType, Mr.encEntry e)) ++
      (if hsEmptyP hs then [] else [(stateType, Mr.encState hs)]) := by
  rw [WalOpG.toM_toRaw]; rfl

theorem opDs_save_length (Mr : WalMarshal) (hs : HardStateM) (es : List EntryM) :
    (opDs Mr (WalOpG.save hs es).toRaw.toM).length = es.length + (if hsEmptyP hs then 0 else 1) := by
  rw [opDs_save]; split <;> simp

theorem histMap_save (H : List (WalOpG WalEnt)) (hs : HardStateM) (es : List EntryM) :
    (H ++ [(WalOpG.save hs es).toRaw]).map WalOpG.toM = H.map WalOpG.toM ++ [WalOpG.save hs es] := by
  rw [List.map_append, List.map_singleton, WalOpG.toM_toRaw]

/-- The `i`-th entry's record, after the commit. -/
theorem saveRec_entry (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : HardStateM) (es : List EntryM) (hc : ∀ b ∈ cuts, b ≤ H.length) (i : Nat) (e : EntryM)
    (he : es[i]? = some e) :
    ((tailRecs Mr (H ++ [(WalOpG.save hs es).toRaw]) md cuts)[(tailRecs Mr
        (H ++ [(WalOpG.save hs es).toRaw]) md cuts).length -
        ((opDs Mr (WalOpG.save hs es).toRaw.toM).length - i)]?).map (fun x => (x.typ, x.data)) =
      some (entryType, Mr.encEntry e) := by
  have hi : i < es.length := (List.getElem?_eq_some_iff.1 he).1
  rw [tailRecs_snoc Mr H md cuts _ hc,
    recAt_chain _ _ _ _ (by rw [opDs_save_length]; omega), opDs_save,
    List.getElem?_append_left (by simpa using hi), List.getElem?_map, he]
  rfl

/-- The state's record, after the entries'. -/
theorem saveRec_state (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : HardStateM) (es : List EntryM) (hc : ∀ b ∈ cuts, b ≤ H.length) (hne : ¬ hsEmptyP hs) :
    ((tailRecs Mr (H ++ [(WalOpG.save hs es).toRaw]) md cuts)[(tailRecs Mr
        (H ++ [(WalOpG.save hs es).toRaw]) md cuts).length -
        ((opDs Mr (WalOpG.save hs es).toRaw.toM).length - es.length)]?).map
        (fun x => (x.typ, x.data)) =
      some (stateType, Mr.encState hs) := by
  rw [tailRecs_snoc Mr H md cuts _ hc,
    recAt_chain _ _ _ _ (by rw [opDs_save_length]; simp [hne]), opDs_save,
    List.getElem?_append_right (by simp)]
  simp [hne]

theorem walMaxSnapIdx_save (H : WalHist) (hs : HardStateM) (es : List EntryM) :
    walMaxSnapIdx (H ++ [WalOpG.save hs es]) = walMaxSnapIdx H := by
  simp [walMaxSnapIdx, List.foldl_append]

theorem walLastIdx_save_nil (H : WalHist) (hs : HardStateM) :
    walLastIdx (H ++ [WalOpG.save hs []]) = walLastIdx H := by
  simp [walLastIdx, List.foldl_append]

theorem walLastIdx_save_last (H : WalHist) (hs : HardStateM) (es : List EntryM) (e : EntryM)
    (he : es.getLast? = some e) :
    walLastIdx (H ++ [WalOpG.save hs es]) ≤ max (uint.nat e.Index') (walMaxSnapIdx H) := by
  simp only [walLastIdx, walMaxSnapIdx, List.foldl_append, List.foldl_cons, List.foldl_nil, he,
    Option.map_some, Option.getD_some]
  exact Nat.le_refl _

theorem walLastHS_save (H : WalHist) (hs : HardStateM) (es : List EntryM) :
    walLastHS (H ++ [WalOpG.save hs es]) = phsNext (walLastHS H) hs := by
  simp [walLastHS, List.foldl_append]

/-- **`raft.MustSync` false**: no entries, the vote and term of the last saved state: no sync due. -/
theorem not_walMustSync (H : WalHist) (hs : HardStateM) (es : List EntryM)
    (h : ¬ (es ≠ [] ∨ hs.Vote' ≠ (walLastHS H).Vote' ∨ hs.Term' ≠ (walLastHS H).Term')) :
    ¬ walMustSync H hs es := by
  unfold walMustSync
  intro hm
  apply h
  rcases hm with hm | ⟨-, hm⟩
  · exact Or.inl hm
  · exact Or.inr hm

/-- The save wrote a record: its end is a cut position. -/
theorem walCutPos_save (H : List (WalOpG WalEnt)) (hs : HardStateM) (es : List EntryM)
    (hne : ¬ (hsEmptyP hs ∧ es = [])) :
    walCutPos ((H ++ [(WalOpG.save hs es).toRaw]).map WalOpG.toM)
      (H ++ [(WalOpG.save hs es).toRaw]).length := by
  right
  refine ⟨hs, es, ?_, hne⟩
  rw [histMap_save]
  simp

/-- **The handle during `Save`, after its commit and `i` records encoded** (see the file header). -/
structure SaveSt (Mr : WalMarshal) (h : WalHS) (hs : HardStateM) (es : List EntryM) (i : Nat)
    (hc : WalHS) : Prop where
  H : hc.H = h.H ++ [(WalOpG.save hs es).toRaw]
  md : hc.md = h.md
  cuts : hc.cuts = h.cuts
  rest : hc.rest = (opDs Mr (WalOpG.save hs es).toRaw.toM).length - i
  st : hc.st = h.st
  snapi : hc.snapi = h.snapi
  pc : hc.pc = h.pc
  enti0 : i = 0 → hc.enti = h.enti
  entiS : ∀ n e, i = n + 1 → es[n]? = some e → hc.enti = e.Index'

theorem SaveSt.init (Mr : WalMarshal) (h : WalHS) (hs : HardStateM) (es : List EntryM) :
    SaveSt Mr h hs es 0
      { h with H := h.H ++ [(WalOpG.save hs es).toRaw],
               rest := (opDs Mr (WalOpG.save hs es).toRaw.toM).length } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ h => by omega⟩

/-- `saveEntry`'s premises for the `i`-th entry. -/
theorem SaveSt.entryPre {Mr : WalMarshal} {h : WalHS} {hs : HardStateM} {es : List EntryM} {i : Nat}
    {hc : WalHS} (s : SaveSt Mr h hs es i hc) (hcut : ∀ b ∈ h.cuts, b ≤ h.H.length)
    (hsn : walMaxSnapIdx (h.H.map WalOpG.toM) ≤ uint.nat h.snapi) (e : EntryM)
    (he : es[i]? = some e) :
    0 < hc.rest ∧
      (hc.rest = 1 → walLastIdx (hc.H.map WalOpG.toM) ≤ max (uint.nat e.Index') (uint.nat hc.snapi)) ∧
      ((tailRecs Mr hc.H hc.md hc.cuts)[(tailRecs Mr hc.H hc.md hc.cuts).length - hc.rest]?).map
        (fun x => (x.typ, x.data)) = some (entryType, Mr.encEntry e) := by
  have hi : i < es.length := (List.getElem?_eq_some_iff.1 he).1
  have hk := opDs_save_length Mr hs es
  refine ⟨?_, ?_, ?_⟩
  · rw [s.rest, hk]; omega
  · intro h1
    rw [s.rest, hk] at h1
    have hlast : es.getLast? = some e := by
      rw [List.getLast?_eq_getElem?]
      split at h1
      · rw [show es.length - 1 = i by omega]; exact he
      · omega
    rw [s.H, histMap_save, s.snapi]
    have := walLastIdx_save_last (h.H.map WalOpG.toM) hs es e hlast
    omega
  · rw [s.H, s.md, s.cuts, s.rest]
    exact saveRec_entry Mr h.H h.md h.cuts hs es hcut i e he

/-- The handle after `saveEntry` of the `i`-th entry. -/
theorem SaveSt.step {Mr : WalMarshal} {h : WalHS} {hs : HardStateM} {es : List EntryM} {i : Nat}
    {hc : WalHS} (s : SaveSt Mr h hs es i hc) (e : EntryM) (he : es[i]? = some e)
    (out' pend' : List w8) :
    SaveSt Mr h hs es (i + 1)
      { hc with rest := hc.rest - 1, out := out', pend := pend', enti := e.Index' } :=
  ⟨s.H, s.md, s.cuts, by simp only; rw [s.rest]; omega, s.st, s.snapi, s.pc, fun h => by omega,
    fun n e' hn he' => by
      simp only
      have : n = i := by omega
      subst this
      rw [he] at he'
      cases he'; rfl⟩

/-- `saveState`'s premise after every entry. -/
theorem SaveSt.statePre {Mr : WalMarshal} {h : WalHS} {hs : HardStateM} {es : List EntryM}
    {hc : WalHS} (s : SaveSt Mr h hs es es.length hc) (hcut : ∀ b ∈ h.cuts, b ≤ h.H.length)
    (hidx : walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi))
    (hsn : walMaxSnapIdx (h.H.map WalOpG.toM) ≤ uint.nat h.snapi) :
    ¬ hsEmptyP hs → 0 < hc.rest ∧
      ((tailRecs Mr hc.H hc.md hc.cuts)[(tailRecs Mr hc.H hc.md hc.cuts).length - hc.rest]?).map
        (fun x => (x.typ, x.data)) = some (stateType, Mr.encState hs) ∧
      (hc.rest = 1 → walLastIdx (hc.H.map WalOpG.toM) ≤ max (uint.nat hc.enti) (uint.nat hc.snapi)) := by
  intro hne
  have hk := opDs_save_length Mr hs es
  refine ⟨?_, ?_, ?_⟩
  · rw [s.rest, hk]; simp [hne]
  · rw [s.H, s.md, s.cuts, s.rest]
    exact saveRec_state Mr h.H h.md h.cuts hs es hcut hne
  · intro _
    rw [s.H, histMap_save, s.snapi]
    cases hes : es.getLast? with
    | none =>
      have : es = [] := List.getLast?_eq_none_iff.1 hes
      subst this
      rw [walLastIdx_save_nil, s.enti0 rfl]; exact hidx
    | some e =>
      have hne' : es ≠ [] := by intro h0; subst h0; simp at hes
      have hlen : 0 < es.length := List.length_pos_iff.2 hne'
      have he : es[es.length - 1]? = some e := by rw [← List.getLast?_eq_getElem?]; exact hes
      rw [s.entiS (es.length - 1) e (by omega) he]
      have := walLastIdx_save_last (h.H.map WalOpG.toM) hs es e hes
      omega

/-- **Every record encoded** (see the file header). -/
structure SaveFin (h : WalHS) (hs : HardStateM) (es : List EntryM) (hc : WalHS) : Prop where
  H : hc.H = h.H ++ [(WalOpG.save hs es).toRaw]
  md : hc.md = h.md
  cuts : hc.cuts = h.cuts
  rest : hc.rest = 0
  st : hc.st = walLastHS (hc.H.map WalOpG.toM)
  pc : hc.pc = h.pc

theorem SaveSt.finEmpty {Mr : WalMarshal} {h : WalHS} {hs : HardStateM} {es : List EntryM}
    {hc : WalHS} (s : SaveSt Mr h hs es es.length hc) (hD : h.Done) (he : hsEmptyP hs) :
    SaveFin h hs es hc :=
  ⟨s.H, s.md, s.cuts, by rw [s.rest, opDs_save_length]; simp [he], by
    rw [s.st, s.H, histMap_save, walLastHS_save, phsNext_empty _ _ he]; exact hD.2, s.pc⟩

theorem SaveSt.finState {Mr : WalMarshal} {h : WalHS} {hs : HardStateM} {es : List EntryM}
    {hc : WalHS} (s : SaveSt Mr h hs es es.length hc) (hne : ¬ hsEmptyP hs) (out' pend' : List w8) :
    SaveFin h hs es { hc with rest := hc.rest - 1, out := out', pend := pend', st := hs } :=
  ⟨s.H, s.md, s.cuts, by simp only; rw [s.rest, opDs_save_length]; simp [hne], by
    simp only
    rw [s.H, histMap_save, walLastHS_save]
    unfold phsNext
    exact (if_neg hne).symm, s.pc⟩

theorem SaveFin.done {h : WalHS} {hs : HardStateM} {es : List EntryM} {hc : WalHS}
    (s : SaveFin h hs es hc) : hc.Done := ⟨s.rest, s.st⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
