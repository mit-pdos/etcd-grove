/-
Port of election_proof/proof_raft__hasUnappliedConfChanges.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__hasUnappliedConfChanges
public import Spec.go_etcd_io.raft.v3.raftLog__scan

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

set_option hygiene false in
/-- Rocq's local `read_field`: one read of `r.raftLog.f` -- the struct gives the log's
location, the log (taken out and put back around the one load) the field, whose value
the log's state pins for `applied`/`committed`. Works on `Hphys`. -/
local macro "read_field" : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty)))) (Val _))
  iapply Perennial.EtcdGrove.raft.wp_load_raftLogC $$ Hphys
  inext
  iintro Hphys
  icases Perennial.EtcdGrove.ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases Perennial.EtcdGrove.ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ Hlog
  try rw [Hlv.1]
  try rw [Hlv.2]
  try clear Hlv lv))

/-- `hasUnappliedConfChanges` is

    if r.raftLog.applied >= r.raftLog.committed { return false }
    found := false
    lo, hi := r.raftLog.applied+1, r.raftLog.committed+1
    pageSize := r.raftLog.maxApplyingEntsSize
    if err := r.raftLog.scan(lo, hi, pageSize, func(ents []pb.Entry) error {
        for i := range ents {
            if ents[i].Type == pb.EntryConfChange ||
               ents[i].Type == pb.EntryConfChangeV2 {
                found = true
                return errBreak
            }
        }
        return nil
    }); err != nil && err != errBreak {
        r.logger.Panicf(...)
    }
    return found

- No loan: the log is inside `ownRaftPhys`, so each read of `r.raftLog.f` loads the
  location through the struct and then takes the log out (`ownRaftPhysC_log_same`) just
  for the field load (`ownRaftLog_struct`); `read_field` above. The log's state pins
  `applied`/`committed`, so every read sees the values the facts (read once up front)
  are about.
- For the `scan`, `Happlied`/`Hcommitted`/`Hnowrap` put `[applied+1, committed+1)`
  inside the log without wrapping, which is exactly `raftLog.scan.spec`'s range
  premise; the range is `unappliedEnts`.
- (2026-10-13) The callback's state is `found ↦ false` and "no conf-change entry in the
  pages so far" (`I`); at the first conf-change entry it stores `found = true` and
  returns `errBreak` (`B`: `found ↦ true`, the error is `errBreak`, and the range has a
  conf-change entry). So `scan` returns `nil` with `found` false and no conf-change entry
  in the range, or `errBreak` with `found` true; `errBreak` is a pointer error
  (`IsNewError`, `isInitialized`'s `ErrBreak`), so `err != errBreak` steps and is false:
  the `Panicf` is dead. (Until 2026-10-13 the log had no conf-change entry, the
  callback's `found = true` branch was dead, and `scan` always returned `nil`.)

Lean notes: `wp_apply raft.wp_load_raftLogC` does not find the first loads of
`r.raftLog` in this function, so `read_field` binds the load with `wp_bind` and
`iapply`s the lemma. The `ents[i].Type` field loads go through a *fractional* element
points-to, which the generated `AccessStrict` instances do not reach, so the element is
split with `iStructNamed` and recombined with `typedPointsto_combine`. The range
construct's counter and the body's `i` share a Go name; the body's is renamed `ibp`. -/
theorem raft.hasUnappliedConfChanges.wp_proof
    (wp_raftLog_scan : raftLog.scan.spec (GF := GF) (hG := hG)) :
    raft.hasUnappliedConfChanges.spec (GF := GF) (hG := hG) := by
  intro c r id s Hsn
  wp_start as Hphys
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  icases ErrBreak with ⟨%eb, #Heb, %Hebf⟩
  obtain ⟨Hebnz, Hebnew⟩ := Hebf
  -- the log's facts, read once: `applied`/`committed` inside the log
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_pure _ _
      (uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied ∧
       uint.Z s.logst.applied ≤ uint.Z s.logst.committed ∧
       uint.Z s.logst.committed ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
         + (s.logst.uents.length : Int) ∧
       uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
         + (s.logst.uents.length : Int) + 1 < 2^64)
      (fun _ _ _ Hnw _ _ Happ Hpap Hcom _ _ => ⟨Hpap Hsn, Happ.2, Hcom, Hnw⟩) $$ Hlog
    with ⟨%Hfacts, Hlog⟩
  obtain ⟨Hpa, Hac, Hcl, Hnw⟩ := Hfacts
  ihave Hphys := Hback $$ Hlog
  wp_auto
  read_field
  read_field
  wp_if_destruct
  · -- `applied >= committed`: the range is empty and the answer is `false`
    iapply HΦ
    iframe Hphys
    ipureintro
    have Hemp : unappliedEnts s.logst = [] := by
      unfold unappliedEnts scanRange
      rw [show (uint.Z (s.logst.committed + W64 1) - uint.Z (s.logst.applied + W64 1)).toNat = 0
        by word]
      rfl
    rw [Hemp]
    simp
  -- the reads of `r.raftLog` for `lo`, `hi`, `pageSize`
  read_field
  read_field
  read_field
  wp_bind (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty)))) (Val _))
  iapply raft.wp_load_raftLogC $$ Hphys
  inext
  iintro Hphys
  wp_pures
  -- `scan` is specified on `ownRaftLog`
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  have Hrange : uint.Z s.logst.prev.index' + 1 ≤ uint.Z (s.logst.applied + W64 1) ∧
      uint.Z (s.logst.applied + W64 1) ≤ uint.Z (s.logst.committed + W64 1) ∧
      uint.Z (s.logst.committed + W64 1) ≤ uint.Z s.logst.prev.index'
        + (s.logst.sents.length : Int) + (s.logst.uents.length : Int) + 1 := by
    word
  wp_func_lits
  wp_apply wp_raftLog_scan _ s.logst _ _ _ _
    (fun acc => iprop(found_ptr ↦ false ∗ ⌜∀ e ∈ acc, ¬ IsConfEnt e⌝))
    (fun err => iprop(⌜err = eb⌝ ∗ found_ptr ↦ true ∗
      ⌜∃ e ∈ unappliedEnts s.logst, IsConfEnt e⌝)) Hrange
    $$ [$Hlog found] as %err ⟨Hlog, Hres⟩
  · isplitl [found]
    · simp only [named]
      iframe
      ipureintro; simp
    imodintro
    unfold scanClosure
    iintro %sl %acc %es %dq
    iintro %Ψ
    imodintro
    iintro ⟨Hes, %Hpg, Hf, %Hacc⟩ HΨ
    obtain ⟨_, Hpre⟩ := Hpg
    wp_auto
    -- the range construct's own counter `i_ptr` and the body's `i` (`ib`) share a Go
    -- name; rename the body's
    rename_i ibp
    irename: (ibp ↦ (_ : w64)) => ib
    ihave %Hslen := ownSlice_len _ _ _ $$ Hes
    ihave IH : iprop(∃ (k m : w64), "i" ∷ i_ptr ↦ k ∗ "ib" ∷ ibp ↦ m ∗
        "Hes" ∷ sl ↦*{dq} es ∗ "Hf" ∷ found_ptr ↦ false ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (es.length : Int)⌝ ∗
        "%Hnc" ∷ ⌜∀ e ∈ es.take (sint.Z k).toNat, ¬ IsConfEnt e⌝)
      $$ [i ib Hes Hf]
    · iexists W64 0, zero_val w64
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      simp
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.Z k < sint.Z sl.len := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      list_elem es (sint.nat k) as e
      -- the range construct's own read of `ents[j]`
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index sl (sint.Z k) es dq e (by word) $$ [Hes] with Hes
      · iframe
        ipureintro
        exact He_lookup
      -- the two `ents[i].Type` reads load a *field*, so lend the element out rather than
      -- using `wp_load_slice_index`
      icases ownSlice_elem_acc (sint.Z k) e sl dq es (by word) He_lookup $$ Hes
        with ⟨Hel, Hesback⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hel with ⟨Hel, %Hel_nn⟩
      iStructNamed Hel
      have Hset : es.set (sint.Z k).toNat e = es := by
        have Hl : es[(sint.Z k).toNat]? = some e := He_lookup
        obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 Hl
        exact List.set_getElem_self h
      have Hmem : e ∈ es := List.mem_of_getElem? He_lookup
      have HinL : e ∈ unappliedEnts s.logst := (Hpre.subset (List.mem_append_right _ Hmem))
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_auto
      by_cases H1 : e.Type' = W32 1
      · -- `EntryConfChange`: found
        rw [decide_eq_true (by rw [H1])]
        wp_auto
        ihave Hel : sliceIndexRef raftpb.Entry (sint.Z k) sl ↦{dq} e $$ [Term Index Type' Data]
        · iapply typedPointsto_combine _ _ _ Hel_nn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave Hes := Hesback $$ %e Hel
        rw [Hset]
        wp_for_post
        iapply HΨ
        iframe
        iright
        iframe
        ipureintro
        exact ⟨Hebnz, rfl, e, HinL, Or.inl H1⟩
      rw [decide_eq_false (by intro h; apply H1; rw [h])]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_auto
      by_cases H2 : e.Type' = W32 2
      · -- `EntryConfChangeV2`: found
        rw [decide_eq_true (by rw [H2])]
        wp_auto
        ihave Hel : sliceIndexRef raftpb.Entry (sint.Z k) sl ↦{dq} e $$ [Term Index Type' Data]
        · iapply typedPointsto_combine _ _ _ Hel_nn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave Hes := Hesback $$ %e Hel
        rw [Hset]
        wp_for_post
        iapply HΨ
        iframe
        iright
        iframe
        ipureintro
        exact ⟨Hebnz, rfl, e, HinL, Or.inr H2⟩
      rw [decide_eq_false (by intro h; apply H2; rw [h])]
      wp_auto
      ihave Hel : sliceIndexRef raftpb.Entry (sint.Z k) sl ↦{dq} e $$ [Term Index Type' Data]
      · iapply typedPointsto_combine _ _ _ Hel_nn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hes := Hesback $$ %e Hel
      rw [Hset]
      wp_for_post
      iframe
      iexists k + W64 1, k
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      intro x Hx
      rw [show (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1 by word,
        List.take_add_one, He_lookup] at Hx
      rcases List.mem_append.1 Hx with Hx | Hx
      · exact Hnc x Hx
      · simp only [Option.toList_some, List.mem_singleton] at Hx
        subst Hx
        rintro (h | h)
        · exact H1 h
        · exact H2 h
    · have Hge : ¬ sint.Z k < sint.Z sl.len := by
        first
        | exact Hif
        | exact fun h => Hif (congrArg (fun b : Bool => (#b : val)) (decide_eq_true h))
      iapply HΨ
      iframe
      ileft
      iframe
      ipureintro
      refine ⟨rfl, ?_⟩
      intro x Hx
      rcases List.mem_append.1 Hx with Hx | Hx
      · exact Hacc x Hx
      · apply Hnc x
        rw [List.take_of_length_le (by word)]
        exact Hx
  ihave Hphys := Hback $$ Hlog
  icases Hres with (⟨%Herr, Hf, %Hnone⟩ | ⟨%Hne, %Herr, Hf, %Hsome⟩)
  · -- `scan` returned `nil`: no conf-change entry in the range, `found` is `false`
    subst Herr
    wp_auto
    iapply HΦ
    iframe Hphys
    ipureintro
    constructor
    · intro h; cases h
    · rintro ⟨e, He, Hc⟩; exact absurd Hc (Hnone e He)
  · -- `scan` returned `errBreak`: `found` is `true`
    subst Herr
    obtain ⟨ty, p, rfl⟩ := Hebnew
    wp_auto
    iapply HΦ
    iframe Hphys
    ipureintro
    exact ⟨fun _ => Hsome, fun _ => rfl⟩

end proof

end EtcdGrove
end Perennial
