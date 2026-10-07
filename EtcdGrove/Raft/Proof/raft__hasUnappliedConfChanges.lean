/-
Port of election_proof/proof_raft__hasUnappliedConfChanges.v.
-/
import EtcdGrove.Raft.Spec.raft__hasUnappliedConfChanges
import EtcdGrove.Raft.Spec.raftLog__scan

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- Rocq's local `read_field`: one read of `r.raftLog.f` -- the struct gives the log's
location, the log (taken out and put back around the one load) the field, whose value
the log's state pins for `applied`/`committed`. Works on `Hphys`. -/
local macro "read_field" : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty)))) (Val _))
  iapply Perennial.EtcdGrove.raft.wp_load_raftLog $$ Hphys
  inext
  iintro Hphys
  icases Perennial.EtcdGrove.ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
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
  location through the struct and then takes the log out (`ownRaftPhys_log_same`) just
  for the field load (`ownRaftLog_struct`); `read_field` above. The log's state pins
  `applied`/`committed`, so every read sees the values the facts (read once up front)
  are about.
- For the `scan`, `Happlied`/`Hcommitted`/`Hnowrap` put `[applied+1, committed+1)`
  inside the log without wrapping, which is exactly `raftLog.scan.spec`'s range
  premise, and `HnoConfChange` is its `∀ e ∈ sents ++ uents, P e` premise at
  `P := fun e => e.Type' = EntryNormal`.
- The invariant `I` handed to `scan` is `emp`. The closure's only write is
  `found = true`, which is on the dead branch, so it needs no ownership of the
  enclosing frame -- which is what lets the closure obligation be proved under the `□`
  that `scanClosure` sits behind.
- `errBreak` is therefore never returned, `scan` returns `nil`, the `Panicf` is dead
  and `found` is still `false`.

Lean notes: `wp_apply raft.wp_load_raftLog` does not find the first loads of
`r.raftLog` in this function, so `read_field` binds the load with `wp_bind` and
`iapply`s the lemma. The `ents[i].Type` field loads go through a *fractional* element
points-to, which the generated `AccessStrict` instances do not reach, so the element is
split with `iStructNamed` and recombined with `typedPointsto_combine`. The range
construct's counter and the body's `i` share a Go name; the body's is renamed `ibp`. -/
theorem raft.hasUnappliedConfChanges.wp_proof
    (wp_raftLog_scan : raftLog.scan.spec (GF := GF) (hG := hG)) :
    raft.hasUnappliedConfChanges.spec (GF := GF) (hG := hG) := by
  intro cfg r id s Hsn
  wp_start as Hphys
  -- the log's facts, read once: `applied`/`committed` inside the log, and no conf
  -- change in it
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_pure _ _
      (uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied ∧
       uint.Z s.logst.applied ≤ uint.Z s.logst.committed ∧
       uint.Z s.logst.committed ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
         + (s.logst.uents.length : Int) ∧
       uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
         + (s.logst.uents.length : Int) + 1 < 2^64 ∧
       ∀ e ∈ s.logst.sents ++ s.logst.uents, e.Type' = EntryNormal)
      (fun lv _ _ _ Hcm Hap _ Hnw _ Hnc Happ Hpap Hcom => by
        rw [← Hcm, ← Hap]
        exact ⟨Hpap Hsn, Happ.2, Hcom, Hnw, Hnc⟩) $$ Hlog
    with ⟨%Hfacts, Hlog⟩
  obtain ⟨Hpa, Hac, Hcl, Hnw, Hnc⟩ := Hfacts
  ihave Hphys := Hback $$ Hlog
  wp_auto
  read_field
  read_field
  wp_if_destruct
  · -- `applied >= committed`: the range is empty and the answer is `false`
    iapply HΦ $$ Hphys
  -- the reads of `r.raftLog` for `lo`, `hi`, `pageSize`
  read_field
  read_field
  read_field
  wp_bind (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty)))) (Val _))
  iapply raft.wp_load_raftLog $$ Hphys
  inext
  iintro Hphys
  wp_pures
  -- `scan` is specified on `ownRaftLog`
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
  have Hrange : uint.Z s.logst.prev.index' + 1 ≤ uint.Z (s.logst.applied + W64 1) ∧
      uint.Z (s.logst.applied + W64 1) ≤ uint.Z (s.logst.committed + W64 1) ∧
      uint.Z (s.logst.committed + W64 1) ≤ uint.Z s.logst.prev.index'
        + (s.logst.sents.length : Int) + (s.logst.uents.length : Int) + 1 := by
    word
  wp_func_lits
  wp_apply wp_raftLog_scan _ s.logst _ _ _ _ emp (fun e => e.Type' = EntryNormal) Hrange Hnc
    $$ [$Hlog] as ⟨Hlog, -⟩
  · -- the callback, at `I := emp`
    isplitr
    · iempintro
    imodintro
    unfold scanClosure
    iintro %sl %es %dq
    iintro %Ψ
    imodintro
    iintro ⟨Hes, %HPes, -⟩ HΨ
    wp_auto
    -- the range construct's own counter `i_ptr` and the body's `i` (`ib`) share a Go
    -- name; rename the body's
    rename_i ibp
    irename: (ibp ↦ (_ : w64)) => ib
    ihave %Hslen := ownSlice_len _ _ _ $$ Hes
    ihave IH : iprop(∃ (k m : w64), "i" ∷ i_ptr ↦ k ∗ "ib" ∷ ibp ↦ m ∗
        "Hes" ∷ sl ↦*{dq} es ∗ "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (es.length : Int)⌝)
      $$ [i ib Hes]
    · iexists W64 0, zero_val w64
      iframe
      ipureintro
      word
    wp_for IH
    wp_if_destruct
    · list_elem es (sint.nat k) as e
      -- the range construct's own read of `ents[j]`
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index sl (sint.Z k) es dq e (by word) $$ [Hes] with Hes
      · iframe
        ipureintro
        exact He_lookup
      have HeT : e.Type' = EntryNormal := HPes e (List.mem_of_getElem? He_lookup)
      -- the two `ents[i].Type` reads load a *field*, so lend the element out rather than
      -- using `wp_load_slice_index`
      icases ownSlice_elem_acc (sint.Z k) e sl dq es (by word) He_lookup $$ Hes
        with ⟨Hel, Hesback⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hel with ⟨Hel, %Hel_nn⟩
      iStructNamed Hel
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_auto
      rw [decide_eq_false (by rw [HeT, EntryNormal]; word)]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_auto
      rw [decide_eq_false (by rw [HeT, EntryNormal]; word)]
      wp_auto
      ihave Hel : sliceIndexRef raftpb.Entry (sint.Z k) sl ↦{dq} e $$ [Term Index Type' Data]
      · iapply typedPointsto_combine _ _ _ Hel_nn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hes := Hesback $$ %e Hel
      -- `list_insert_id`
      have Hset : es.set (sint.Z k).toNat e = es := by
        have Hl : es[(sint.Z k).toNat]? = some e := He_lookup
        obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 Hl
        exact List.set_getElem_self h
      rw [Hset]
      wp_for_post
      iframe
      iexists k + W64 1, k
      iframe
      ipureintro
      word
    · iapply HΨ
      iframe
  -- `scan` returned `nil`, so the `Panicf` is dead and `found` is `false`
  ihave Hphys := Hback $$ Hlog
  iapply HΦ $$ Hphys

end proof

end EtcdGrove
end Perennial
