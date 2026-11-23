/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecOrder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`recOrder(kept, ids)` (recovery.go) against the model's `sp.recOrder`: each round of the Go
loop is one `sp.recOrderStep` (the first unplaced id whose kept dependencies are placed, else
the first unplaced one), the `placed` map mirroring the model's placed list.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecReaches

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

theorem find?_idx {α : Type} (l : List α) (q : α → Bool) (i : Nat) (hi : i < l.length)
    (hq : q l[i] = true) (hpre : ∀ j (hj : j < i), q (l[j]'(by omega)) = false) :
    l.find? q = some l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp at hq; simp [List.find?_cons, hq]
    | succ i =>
      have ha := hpre 0 (by omega)
      simp only [List.getElem_cons_zero] at ha
      rw [List.find?_cons, ha]
      exact ih i (by simp at hi; omega) hq (fun j hj => by
        have := hpre (j + 1) (by omega); simpa using this)

/-- `recOrder`'s readiness test of `c` against the placed list `P`. -/
def readyIn (k : Kept) (P : List CmdId) (c : CmdId) : Bool :=
  ((k.get c).map RecEntry.dep).getD [] |>.all (fun d => (k.get d).isNone || d ∈ P)

/-- The step when the first ready unplaced id is `ids[i]`. -/
theorem recOrderStep_readyI (k : Kept) (ids P : List CmdId) (i : Nat) (hi : i < ids.length)
    (hP : ids[i] ∉ P) (hr : readyIn k P ids[i] = true)
    (hpre : ∀ j (hj : j < i), ids[j]'(by omega) ∈ P ∨ readyIn k P (ids[j]'(by omega)) = false) :
    recOrderStep k ids P = P ++ [ids[i]] := by
  have hf : (ids.filter (· ∉ P)).find? (readyIn k P) = some ids[i] := by
    rw [List.find?_filter]
    apply find?_idx ids _ i hi
    · simp [hP]; exact hr
    · intro j hj
      rcases hpre j hj with h | h
      · simp [h]
      · simp [h]
  unfold recOrderStep
  simp only
  have : (List.find? (fun c => (((k.get c).map RecEntry.dep).getD []).all
      (fun d => (k.get d).isNone || decide (d ∈ P))) (ids.filter (· ∉ P))) = some ids[i] := hf
  rw [this]

/-- The step when no unplaced id is ready and the first unplaced one is `ids[i]`. -/
theorem recOrderStep_first (k : Kept) (ids P : List CmdId) (i : Nat) (hi : i < ids.length)
    (hnone : ∀ j (hj : j < ids.length), ids[j] ∈ P ∨ readyIn k P ids[j] = false)
    (hP : ids[i] ∉ P) (hpre : ∀ j (hj : j < i), ids[j]'(by omega) ∈ P) :
    recOrderStep k ids P = P ++ [ids[i]] := by
  have hf : (ids.filter (· ∉ P)).find? (readyIn k P) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx.1
    rcases hnone j hj with h | h
    · simp [h] at hx
    · simp [h]
  have hh : (ids.filter (· ∉ P)).head? = some ids[i] := by
    rw [List.head?_filter]
    apply find?_idx ids _ i hi
    · simp [hP]
    · intro j hj; simp [hpre j hj]
  unfold recOrderStep
  simp only
  have : (List.find? (fun c => (((k.get c).map RecEntry.dep).getD []).all
      (fun d => (k.get d).isNone || decide (d ∈ P))) (ids.filter (· ∉ P))) = none := hf
  rw [this, hh]

/-- The placed list after `n ≤ |ids|` rounds: `n` distinct ids. -/
theorem recOrder_iter_len (k : Kept) (ids : List CmdId) (hnd : ids.Nodup) :
    ∀ n ≤ ids.length, (iter (recOrderStep k ids) n []).length = n ∧
      (iter (recOrderStep k ids) n []).Nodup ∧ ∀ c ∈ iter (recOrderStep k ids) n [], c ∈ ids := by
  intro n
  induction n with
  | zero => intro _; simp [iter]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [iter_succ']
    generalize iter (recOrderStep k ids) n [] = P at h1 h2 h3
    have hex : ∃ c ∈ ids, c ∉ P := by
      apply Classical.byContradiction
      intro hno
      simp only [not_exists, not_and, Classical.not_not] at hno
      have := (List.subperm_of_subset hnd hno).length_le
      omega
    obtain ⟨c0, hc0, hc0P⟩ := hex
    have hrest : c0 ∈ ids.filter (· ∉ P) := by simp [hc0, hc0P]
    have key : ∃ c ∈ ids.filter (· ∉ P), recOrderStep k ids P = P ++ [c] := by
      unfold recOrderStep
      simp only
      cases hf : (ids.filter (· ∉ P)).find? (fun c => (((k.get c).map RecEntry.dep).getD []).all
          (fun d => (k.get d).isNone || decide (d ∈ P))) with
      | some c => exact ⟨c, List.mem_of_find?_eq_some hf, rfl⟩
      | none =>
        cases hh : (ids.filter (· ∉ P)).head? with
        | none => rw [List.head?_eq_none_iff] at hh; rw [hh] at hrest; simp at hrest
        | some c => exact ⟨c, List.mem_of_mem_head? hh, rfl⟩
    obtain ⟨c, hc, he⟩ := key
    rw [List.mem_filter] at hc
    simp only [decide_eq_true_eq] at hc
    rw [he]
    refine ⟨by simp [h1], ?_, ?_⟩
    · rw [List.nodup_append]; refine ⟨h2, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hc.2 ha
    · intro a ha; simp at ha; rcases ha with ha | rfl
      · exact h3 a ha
      · exact hc.1

end sp

/-- After `recOrder`'s search for a ready id: none (`next = -1`, every unplaced id blocked),
or the step's id at `next`. -/
def swift.findOk (k : sp.Kept) (ids : List swift.CommandId) (P : List sp.CmdId) (nx : w64) : Prop :=
  (sint.Z nx = -1 ∧ ∀ j (hj : j < ids.length), toCmdId ids[j] ∈ P ∨
      sp.readyIn k P (toCmdId ids[j]) = false) ∨
  (∃ i0, ∃ h : i0 < ids.length, sint.Z nx = i0 ∧
    sp.recOrderStep k (ids.map toCmdId) P = P ++ [toCmdId ids[i0]])

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

theorem swift.recOrder.wp_proof : swift.recOrder.specI (hG := hG) := by
  intro m k o isl ids dq
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hk, Hids, %Hpre⟩
  iunfold swift.keptOwn at Hk
  icases Hk with ⟨%mk, Hm, %Hmk, Hents⟩
  ihave %Hlen := ownSlice_len $$ Hids
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Bool)) as %pm0 Hpm
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %osl0 ⟨Ho0, Hocap0⟩
  wp_auto
  ihave HI : (∃ (P : List sp.CmdId) (osl : GoSlice) (pm : GMap swift.CommandId Bool),
      "order" ∷ order_ptr ↦ osl ∗ "Ho" ∷ osl ↦* P.map ofCmdId ∗
      "Hocap" ∷ ownSliceCap swift.CommandId osl (DFrac.own 1) ∗
      "Hpm" ∷ pm0 ↦$ pm ∗
      "%Hout" ∷ ⌜P = sp.iter (sp.recOrderStep k (ids.map toCmdId)) P.length [] ∧
        P.length ≤ ids.length ∧ ∀ c, (pm !! c).getD false = decide (toCmdId c ∈ P)⌝ : IProp netDistGF)
    $$ [order Ho0 Hocap0 Hpm]
  · iexists [], _, ∅
    simp only [List.map_nil, List.length_nil]
    iframe
    ipureintro; refine ⟨rfl, by simp, by simp⟩
  ipersist ids
  ipersist kept
  ipersist placed
  wp_for HI
  wp_if_destruct
  · ihave %Hol := ownSlice_len $$ Ho
    simp only [List.length_map] at Hol
    rename_i iu_ptr
    irename : (iu_ptr ↦ zero_val w64 : IProp netDistGF) => iu
    wp_bind (App (App (App (Val doFor) _) _) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (nx : w64) (cv : swift.CommandId)
        (iv w : w64), next_ptr ↦ nx ∗ c_ptr ↦ cv ∗ iu_ptr ↦ iv ∗ i_ptr ↦ w ∗
        pm0 ↦$ pm ∗ m ↦$ mk ∗ isl ↦*{dq} ids ∗
        ([∗map] c ↦ p ∈ mk, ∃ e, ⌜k.get (toCmdId c) = some e⌝ ∗ swift.recOwn p e (o (toCmdId c))) ∗
        ⌜swift.findOk k ids P nx⌝))) $$ [next c iu i Hpm Hm Hids Hents]
    · ihave HF : (∃ (w : w64) (cv : swift.CommandId) (iv : w64),
          "i" ∷ i_ptr ↦ w ∗ "c" ∷ c_ptr ↦ cv ∗ "iu" ∷ iu_ptr ↦ iv ∗
          "%Hf" ∷ ⌜0 ≤ sint.Z w ∧ sint.Z w ≤ sint.Z isl.len ∧ ∀ j (hj : j < sint.nat w)
            (hj' : j < ids.length), toCmdId ids[j] ∈ P ∨ sp.readyIn k P (toCmdId ids[j]) = false⌝ :
          IProp netDistGF) $$ [i c iu]
      · iexists W64 0, _, _
        iframe
        ipureintro; refine ⟨by word, by word, ?_⟩; intro j hj; word
      wp_for HF
      wp_if_destruct
      · -- the id `ids[w]`
        have hwl : sint.nat w < ids.length := by have := Hf.1; word
        rw [ite_eq_left (show 0 ≤ sint.Z w ∧ sint.Z w < sint.Z isl.len from ⟨Hf.1, Hif⟩)]
        wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z w) _ _ ids[sint.nat w]
          Hf.1) $$ [Hids] as Hids
        · iframe; ipureintro
          rw [show (sint.Z w).toNat = sint.nat w by word]; simp
        wp_apply (wp_map_lookup1 _ _ pm0 pm ids[sint.nat w]) $$ Hpm as Hpm
        rw [show (zero_val Bool) = false from rfl, Hout.2.2]
        have hfw : ∀ j (hj : j < sint.nat (w + W64 1)) (hj' : j < ids.length), j ≠ sint.nat w →
            j < sint.nat w := by intro j hj _ hne; have := Hf.1; have : sint.nat (w + W64 1) = sint.nat w + 1 := by word
                                 omega
        wp_if_destruct
        · -- placed
          wp_for_post
          iframe
          iexists w + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          intro j hj hj'
          by_cases hjw : j = sint.nat w
          · subst hjw; exact Or.inl Hif
          · exact Hf.2.2 j (hfw j hj hj' hjw) hj'
        · -- not placed: its dependencies
          have hck := Hpre.2 _ (List.getElem_mem hwl)
          rw [← Hmk.2] at hck
          obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hck
          obtain ⟨e, he⟩ : ∃ e, k.get (toCmdId ids[sint.nat w]) = some e := by
            have := Hmk.2 ids[sint.nat w]; rw [hp] at this
            exact Option.isSome_iff_exists.mp this.symm
          wp_apply (wp_map_lookup1 _ _ m mk ids[sint.nat w]) $$ Hm as Hm
          rw [hp]
          simp only [Option.getD_some]
          icases (BigSepM.bigSepM_lookup_acc (show Iris.Std.PartialMap.get? mk ids[sint.nat w] = some p from hp)).1
            $$ Hents with ⟨⟨%e', %he', Hre⟩, Hents⟩
          rw [he] at he'; cases he'
          iunfold swift.recOwn at Hre
          icases Hre with ⟨%ph, %cls, %vs, %dsl, Hp, #Hvs, Hdsl, %Hph⟩
          wp_auto
          icases swift.depRead _ dsl _ $$ Hdsl with ⟨%dq', Hd, Hdback⟩
          ihave %Hdl := ownSlice_len $$ Hd
          simp only [List.length_map] at Hdl
          have hrd : sp.readyIn k P (toCmdId ids[sint.nat w]) =
              e.dep.all (fun d => (k.get d).isNone || decide (d ∈ P)) := by
            unfold sp.readyIn; rw [he]; rfl
          wp_bind (App (App (App (Val doFor) _) _) _)
          iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (rv : Bool) (jv : w64)
              (dv : swift.CommandId), ready_ptr ↦ rv ∗ i_ptr ↦ jv ∗ d_ptr ↦ dv ∗
              pm0 ↦$ pm ∗ m ↦$ mk ∗ dsl ↦*{dq'} List.map ofCmdId e.dep ∗
              ⌜rv = sp.readyIn k P (toCmdId ids[sint.nat w])⌝))) $$ [i d ready Hpm Hm Hd]
          · ihave HD : (∃ (j : w64) (dv : swift.CommandId),
                "i" ∷ i_ptr ↦ j ∗ "d" ∷ d_ptr ↦ dv ∗ "ready" ∷ ready_ptr ↦ true ∗
                "%Hdj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z dsl.len ∧ ∀ j' dd, j' < sint.nat j →
                  e.dep[j']? = some dd → ((k.get dd).isNone || decide (dd ∈ P)) = true⌝ :
                IProp netDistGF) $$ [i d ready]
            · iexists W64 0, _
              iframe
              ipureintro; refine ⟨by word, by word, ?_⟩; intro j' dd hj; word
            wp_for HD
            wp_if_destruct
            · have hjl : sint.nat j < e.dep.length := by have := Hdj.1; word
              obtain ⟨dd, hdd⟩ : ∃ dd, e.dep[sint.nat j]? = some dd :=
                ⟨_, List.getElem?_eq_getElem hjl⟩
              rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z dsl.len from ⟨Hdj.1, Hif⟩)]
              wp_apply (wp_load_slice_index (V := swift.CommandId) dsl (sint.Z j) _ _ (ofCmdId dd)
                Hdj.1) $$ [Hd] as Hd
              · iframe; ipureintro
                rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hdd]; rfl
              wp_apply (wp_map_lookup2 _ _ m mk (ofCmdId dd)) $$ Hm as Hm
              have hex : (mk !! ofCmdId dd).isSome = (k.get dd).isSome := by
                rw [Hmk.2]; rfl
              have hok_next : ∀ (hok : ((k.get dd).isNone || decide (dd ∈ P)) = true),
                  ∀ j' dd', j' < sint.nat (j + W64 1) → e.dep[j']? = some dd' →
                    ((k.get dd').isNone || decide (dd' ∈ P)) = true := by
                intro hok j' dd' hj' hjd
                have : sint.nat (j + W64 1) = sint.nat j + 1 := by have := Hdj.1; word
                by_cases hjj : j' = sint.nat j
                · subst hjj; rw [hdd] at hjd; cases hjd; exact hok
                · exact Hdj.2.2 j' dd' (by omega) hjd
              wp_if_destruct
              · -- kept
                wp_apply (wp_map_lookup1 _ _ pm0 pm (ofCmdId dd)) $$ Hpm as Hpm
                rw [show (zero_val Bool) = false from rfl, Hout.2.2]
                simp only [toCmdId_ofCmdId]
                by_cases hP : dd ∈ P
                · -- placed: fine
                  simp only [hP, decide_true, Bool.not_true]
                  wp_auto
                  wp_for_post
                  iframe
                  iexists j + W64 1, _
                  iframe
                  ipureintro
                  refine ⟨by word, by word, hok_next (by simp [hP])⟩
                · -- not placed: not ready
                  simp only [hP, decide_false, Bool.not_false]
                  wp_auto
                  wp_for_post
                  iframe
                  ipureintro
                  refine ⟨rfl, ?_⟩
                  rw [hrd]
                  symm
                  rw [List.all_eq_false]
                  refine ⟨dd, List.mem_of_getElem? hdd, ?_⟩
                  rw [hex] at Hif
                  simp [Option.isSome_iff_ne_none] at Hif
                  simp [Hif, hP]
              · -- not kept: fine
                wp_for_post
                iframe
                iexists j + W64 1, _
                iframe
                ipureintro
                rw [hex] at Hif
                refine ⟨by word, by word, hok_next (by simp at Hif; simp [Hif])⟩
            · -- done: ready
              iframe
              ipureintro
              rw [hrd]
              symm
              rw [List.all_eq_true]
              intro dd hdd
              obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hdd
              have : j' < e.dep.length := by
                rcases Nat.lt_or_ge j' e.dep.length with h | h
                · exact h
                · rw [List.getElem?_eq_none_iff.mpr h] at hj'; cases hj'
              exact Hdj.2.2 j' dd (by word) hj'
          · iintro %v ⟨%hv, %rv, %jv, %dv, ready, i, d, Hpm, Hm, Hd, %hrv⟩
            subst hv
            ihave Hents := Hents $$ [Hp Hd Hdback]
            · iexists e
              isplitr
              · ipureintro; exact he
              iunfold swift.recOwn
              iexists ph, cls, vs, dsl
              iframe Hp Hvs
              isplitl [Hd Hdback]
              · iapply Hdback $$ Hd
              ipureintro; exact Hph
            wp_auto
            subst hrv
            cases hr : sp.readyIn k P (toCmdId ids[sint.nat w])
            · -- not ready
              wp_auto
              wp_for_post
              iframe
              iexists w + W64 1, _, _
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              intro j hj hj'
              by_cases hjw : j = sint.nat w
              · subst hjw; exact Or.inr hr
              · exact Hf.2.2 j (hfw j hj hj' hjw) hj'
            · -- ready: found
              wp_auto
              wp_for_post
              iframe
              ipureintro
              refine ⟨rfl, ?_⟩
              unfold swift.findOk
              right
              refine ⟨sint.nat w, hwl, by word, ?_⟩
              have := sp.recOrderStep_readyI k (ids.map toCmdId) P (sint.nat w) (by simpa using hwl)
                (by simpa using Hif) (by simpa using hr)
                (fun j hj => by
                  have := Hf.2.2 j hj (by omega)
                  simpa using this)
              simpa using this
      · -- the search done: none ready
        iframe
        ipureintro
        unfold swift.findOk
        left
        refine ⟨by word, ?_⟩
        intro j hj
        exact Hf.2.2 j (by have := Hf.1; word) hj
    · iintro %v ⟨%hv, %nx, %cv, %iv, %w', next, c, iu, i, Hpm, Hm, Hids, Hents, %Hfo⟩
      subst hv
      wp_auto
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (nx' : w64), next_ptr ↦ nx' ∗
          pm0 ↦$ pm ∗ isl ↦*{dq} ids ∗
          ⌜∃ i0, ∃ h : i0 < ids.length, sint.Z nx' = i0 ∧
            sp.recOrderStep k (ids.map toCmdId) P = P ++ [toCmdId ids[i0]]⌝))) $$ [next Hpm Hids]
      · unfold swift.findOk at Hfo
        rcases Hfo with ⟨hnx, hnone⟩ | ⟨i0, hi0, hnx, hstep⟩
        · -- none ready: the first unplaced
          have hnx' : nx = W64 (-1) := by word
          subst hnx'
          wp_auto
          rename_i iu2_ptr
          irename : (iu2_ptr ↦ zero_val w64 : IProp netDistGF) => iu2
          ihave HB : (∃ (w : w64) (cv : swift.CommandId) (iv : w64),
              "i" ∷ i_ptr ↦ w ∗ "c" ∷ c_ptr ↦ cv ∗ "iu" ∷ iu2_ptr ↦ iv ∗
              "%Hb" ∷ ⌜0 ≤ sint.Z w ∧ sint.Z w ≤ sint.Z isl.len ∧ ∀ j (hj : j < sint.nat w)
                (hj' : j < ids.length), toCmdId ids[j] ∈ P⌝ : IProp netDistGF) $$ [i c iu2]
          · iexists W64 0, _, _
            iframe
            ipureintro; refine ⟨by word, by word, ?_⟩; intro j hj; word
          wp_for HB
          wp_if_destruct
          · have hwl : sint.nat w < ids.length := by have := Hb.1; word
            rw [ite_eq_left (show 0 ≤ sint.Z w ∧ sint.Z w < sint.Z isl.len from ⟨Hb.1, Hif⟩)]
            wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z w) _ _ ids[sint.nat w]
              Hb.1) $$ [Hids] as Hids
            · iframe; ipureintro
              rw [show (sint.Z w).toNat = sint.nat w by word]; simp
            wp_apply (wp_map_lookup1 _ _ pm0 pm ids[sint.nat w]) $$ Hpm as Hpm
            rw [show (zero_val Bool) = false from rfl, Hout.2.2]
            by_cases hP : toCmdId ids[sint.nat w] ∈ P
            · simp only [hP, decide_true, Bool.not_true]
              wp_auto
              wp_for_post
              iframe
              iexists w + W64 1, _, _
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              intro j hj hj'
              by_cases hjw : j = sint.nat w
              · subst hjw; exact hP
              · exact Hb.2.2 j (by have := Hb.1; have : sint.nat (w + W64 1) = sint.nat w + 1 := by word
                                   omega) hj'
            · simp only [hP, decide_false, Bool.not_false]
              wp_auto
              wp_for_post
              iframe
              ipureintro
              refine ⟨rfl, sint.nat w, hwl, by word, ?_⟩
              have := sp.recOrderStep_first k (ids.map toCmdId) P (sint.nat w) (by simpa using hwl)
                (fun j hj => by have := hnone j (by simpa using hj); simpa using this)
                (by simpa using hP)
                (fun j hj => by have := Hb.2.2 j hj (by omega); simpa using this)
              simpa using this
          · -- every id placed: impossible (fewer placed than ids)
            exfalso
            have hall : ∀ c ∈ ids.map toCmdId, c ∈ P := by
              intro c hc
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
              simp only [List.length_map] at hj
              simpa using Hb.2.2 j (by have := Hb.1; word) hj
            have hnd : (ids.map toCmdId).Nodup :=
              List.Pairwise.map toCmdId (fun a b hab h => hab (by simpa using congrArg ofCmdId h)) Hpre.1
            have := (List.subperm_of_subset hnd hall).length_le
            simp only [List.length_map] at this
            word
        · -- found
          have hnx' : nx ≠ W64 (-1) := by intro h; subst h; word
          rw [decide_eq_false hnx']
          wp_auto
          iframe
          ipureintro
          exact ⟨rfl, i0, hi0, hnx, hstep⟩
      · iintro %v ⟨%hv, %nx', next, Hpm, Hids, %Hnx⟩
        subst hv
        obtain ⟨i0, hi0, hnx, hstep⟩ := Hnx
        wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z nx' ∧ sint.Z nx' < sint.Z isl.len by word)]
        wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z nx') _ _ ids[i0]
          (by word)) $$ [Hids] as Hids
        · iframe; ipureintro
          rw [show (sint.Z nx').toNat = i0 by word]; simp
        wp_apply (wp_mapInsert _ pm0 pm ids[i0] true) $$ Hpm as Hpm
        rw [ite_eq_left (show 0 ≤ sint.Z nx' ∧ sint.Z nx' < sint.Z isl.len by word)]
        wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z nx') _ _ ids[i0]
          (by word)) $$ [Hids] as Hids
        · iframe; ipureintro
          rw [show (sint.Z nx').toNat = i0 by word]; simp
        wp_bind (App (Val (GoInstruction (CompositeLiteral
          (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [ids[i0]]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [Ho Hocap Hlsl] as %nsl ⟨Ho, Hocap, -⟩
        · iframe
        wp_for_post
        iframe
        iexists P ++ [toCmdId ids[i0]], nsl, _
        simp only [List.map_append, List.map_cons, List.map_nil, ofCmdId_toCmdId]
        iframe
        ipureintro
        have hPl : P.length < ids.length := by have := Hlen; word
        have hnd : (ids.map toCmdId).Nodup :=
          List.Pairwise.map toCmdId (fun a b hab h => hab (by simpa using congrArg ofCmdId h)) Hpre.1
        have hP' : P ++ [toCmdId ids[i0]] = sp.iter (sp.recOrderStep k (ids.map toCmdId)) (P.length + 1) [] := by
          rw [sp.iter_succ', ← Hout.1, hstep]
        refine ⟨?_, ?_, ?_⟩
        · simpa using hP'
        · simp; omega
        · intro c
          by_cases hc : c = ids[i0]
          · subst hc; rw [GMap.lookup_insert_eq]; simp
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc), Hout.2.2]
            have : toCmdId c ≠ toCmdId ids[i0] := fun h => hc (by simpa using congrArg ofCmdId h)
            simp [this]
  · -- every id placed: the model's order
    ihave %Hol := ownSlice_len $$ Ho
    simp only [List.length_map] at Hol
    have hPl : P.length = ids.length := by have := Hout.2.1; word
    have hP : P = sp.recOrder k (ids.map toCmdId) := by
      rw [sp.recOrder_eq, List.length_map, ← hPl]; exact Hout.1
    rw [← hP]
    iapply HΦ
    iframe
    iunfold swift.keptOwn
    iexists mk
    iframe
    ipureintro; exact Hmk

end proof

end Perennial.github_com.imdea_software.swiftpaxos
