/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__processMessages.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The messages' types, from their `rnMsgOk`. -/
theorem rnMsgOk_tys (E : RNEnv GF) : ∀ msL : List Loc,
    ([∗list] m ∈ msL, rnMsgOk E m) ⊢
      ∃ tys : List w32, [∗list] m; ty ∈ msL; tys, ∃ to : w64, msgAt m to ty
  | [] => by
    iintro -
    iexists []
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m (ty : w32) => iprop(∃ to : w64, msgAt (GF := GF) m to ty))).2
    iempintro
  | m :: msL => by
    iintro H
    icases (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgOk (GF := GF) E m)).1 $$ H with ⟨Hm, Hrest⟩
    ihave Hrest := rnMsgOk_tys E msL $$ Hrest
    icases Hrest with ⟨%tys, Hrest⟩
    iunfold rnMsgOk at Hm
    icases Hm with ⟨%to, %ty, Hm, -⟩
    iexists ty :: tys
    iapply (BigSepL2.bigSepL2_cons (Φ := fun _ m (ty : w32) => iprop(∃ to : w64, msgAt (GF := GF) m to ty))).2
    isplitl [Hm]
    · iexists to; iexact Hm
    · iexact Hrest

/-- The first loop's state at its counter `K`: the marks `kl` are `rnKeepAt`'s above `K` (false at
and below), and `sentAppResp` (`b`) says whether a `MsgAppResp` to a member not removed is above. -/
def pmL1 (tys : List w32) (rm kl : List Bool) (b : Bool) (K : Int) : Prop :=
  (∀ j : Nat, j < tys.length →
    kl[j]? = some (decide (K < (j : Int)) && @decide (rnKeepAt tys rm j) (Classical.propDecidable _))) ∧
  (b = true ↔ ∃ j : Nat, K < (j : Int) ∧ tys[j]? = some (W32 4) ∧ rm[j]? = some false)

theorem pmL1_init (tys : List w32) :
    pmL1 tys (List.replicate tys.length false) (List.replicate tys.length false) false
      ((tys.length : Int) - 1) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    have : ¬ ((tys.length : Int) - 1 < (j : Int)) := by omega
    simp [hj, this]
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j hj ht
    have : tys.length ≤ j := by omega
    rw [List.getElem?_eq_none (by omega)] at ht
    cases ht

theorem rnKeepAt_set_gt {tys : List w32} {rm : List Bool} {kn j : Nat} {a : Bool} (h : kn < j) :
    rnKeepAt tys (rm.set kn a) j ↔ rnKeepAt tys rm j := by
  unfold rnKeepAt
  have h1 : ∀ j', j ≤ j' → (rm.set kn a)[j']? = rm[j']? := fun j' hj' =>
    List.getElem?_set_ne (by omega)
  rw [h1 j (Nat.le_refl _)]
  constructor
  · rintro ⟨A, B, C⟩
    refine ⟨A, B, fun h4 j' hj' h4' => ?_⟩
    rw [← h1 j' (by omega)]; exact C h4 j' hj' h4'
  · rintro ⟨A, B, C⟩
    refine ⟨A, B, fun h4 j' hj' h4' => ?_⟩
    rw [h1 j' (by omega)]; exact C h4 j' hj' h4'

theorem rnKeepAt_at {tys : List w32} {rm kl : List Bool} {b : Bool} {kn : Nat} {ty : w32} {a : Bool}
    (H : pmL1 tys rm kl b (kn : Int)) (hr : rm.length = tys.length) (hk : kn < tys.length)
    (hty : tys[kn]? = some ty) :
    rnKeepAt tys (rm.set kn a) kn ↔ (a = false ∧ ty ≠ W32 7 ∧ (ty = W32 4 → b = false)) := by
  unfold rnKeepAt
  rw [List.getElem?_set_self (by omega), hty]
  have hb := H.2
  constructor
  · rintro ⟨A, B, C⟩
    refine ⟨by simpa using A, fun h => B (by rw [h]), fun h4 => ?_⟩
    cases hbb : b
    · rfl
    · obtain ⟨j, hj, hj4, hjr⟩ := hb.1 hbb
      have := C (by rw [h4]) j (by omega) hj4
      rw [List.getElem?_set_ne (by omega)] at this
      rw [this] at hjr; cases hjr
  · rintro ⟨A, B, C⟩
    refine ⟨by rw [A], fun h => B (by simpa using h), fun h4 j hj hj4 => ?_⟩
    have hbf : b = false := C (by simpa using h4)
    rw [List.getElem?_set_ne (by omega)]
    have hjl : j < rm.length := by
      have := (List.getElem?_eq_some_iff.1 hj4).1; omega
    obtain ⟨v, hv⟩ : ∃ v, rm[j]? = some v := ⟨_, List.getElem?_eq_getElem hjl⟩
    cases v
    · exfalso
      have := hb.2 ⟨j, by omega, hj4, hv⟩
      rw [hbf] at this; cases this
    · exact hv

theorem pmL1_step {tys : List w32} {rm kl : List Bool} {b : Bool} {kn : Nat} {ty : w32}
    (H : pmL1 tys rm kl b (kn : Int)) (hr : rm.length = tys.length) (hl : kl.length = tys.length)
    (hk : kn < tys.length) (hty : tys[kn]? = some ty) (a b' : Bool) (keep : Bool) (kl' : List Bool)
    (hkeep : keep = true ↔ (a = false ∧ ty ≠ W32 7 ∧ (ty = W32 4 → b = false)))
    (hb' : b' = true ↔ (b = true ∨ (a = false ∧ ty = W32 4)))
    (hkl' : kl' = if keep then kl.set kn true else kl) :
    pmL1 tys (rm.set kn a) kl' b' ((kn : Int) - 1) := by
  have hat := rnKeepAt_at (a := a) H hr hk hty
  refine ⟨?_, ?_⟩
  · intro j hj
    by_cases hjk : j = kn
    · subst hjk
      have hd : decide ((j : Int) - 1 < (j : Int)) = true := decide_eq_true (by omega)
      rw [hd, Bool.true_and]
      have e : @decide (rnKeepAt tys (rm.set j a) j) (Classical.propDecidable _) = keep := by
        cases hkk : keep
        · simp only [decide_eq_false_iff_not]; intro h; rw [hat] at h; have := hkeep.2 h; rw [hkk] at this; cases this
        · simp only [decide_eq_true_eq]; rw [hat]; exact hkeep.1 hkk
      rw [e, hkl']
      cases keep
      · have := H.1 j hj; simp at this; simp [this]
      · simp [List.getElem?_set_self (show j < kl.length by omega)]
    · have hkl'j : kl'[j]? = kl[j]? := by
        rw [hkl']; cases keep
        · rfl
        · exact List.getElem?_set_ne (Ne.symm hjk)
      rw [hkl'j, H.1 j hj]
      by_cases hgt : kn < j
      · have e1 : decide ((kn : Int) < (j : Int)) = true := decide_eq_true (by omega)
        have e2 : decide ((kn : Int) - 1 < (j : Int)) = true := decide_eq_true (by omega)
        rw [e1, e2]
        simp only [Bool.true_and]
        exact congrArg some (decide_eq_decide.2 (rnKeepAt_set_gt hgt).symm)
      · have e1 : decide ((kn : Int) < (j : Int)) = false := decide_eq_false (by omega)
        have e2 : decide ((kn : Int) - 1 < (j : Int)) = false := decide_eq_false (by omega)
        rw [e1, e2]; rfl
  · rw [hb', H.2]
    constructor
    · rintro (⟨j, hj, h4, hrm⟩ | ⟨ha, h4⟩)
      · exact ⟨j, by omega, h4, by rw [List.getElem?_set_ne (by omega)]; exact hrm⟩
      · exact ⟨kn, by omega, by rw [hty, h4], by rw [List.getElem?_set_self (by omega), ha]⟩
    · rintro ⟨j, hj, h4, hrm⟩
      by_cases hjk : j = kn
      · subst hjk
        rw [List.getElem?_set_self (by omega)] at hrm
        rw [hty] at h4
        right; exact ⟨by simpa using hrm, by simpa using h4⟩
      · left
        exact ⟨j, by omega, h4, by rw [List.getElem?_set_ne (Ne.symm hjk)] at hrm; exact hrm⟩

section steps
variable {tys : List w32} {rm kl : List Bool} {b : Bool} {kn : Nat}

/-- To a removed member: `continue`. -/
theorem pmL1_removed {ty : w32} (H : pmL1 tys rm kl b (kn : Int)) (hr : rm.length = tys.length)
    (hl : kl.length = tys.length) (hk : kn < tys.length) (hty : tys[kn]? = some ty) :
    pmL1 tys (rm.set kn true) kl b ((kn : Int) - 1) :=
  pmL1_step H hr hl hk hty true b false kl (by simp) (by simp) (by simp)

/-- A `MsgAppResp` with a later one kept: `continue`. -/
theorem pmL1_resp_dup (H : pmL1 tys rm kl true (kn : Int)) (hr : rm.length = tys.length)
    (hl : kl.length = tys.length) (hk : kn < tys.length) (hty : tys[kn]? = some (W32 4)) :
    pmL1 tys (rm.set kn false) kl true ((kn : Int) - 1) :=
  pmL1_step H hr hl hk hty false true false kl (by simp) (by simp) (by simp)

/-- The last `MsgAppResp` to a member not removed: kept. -/
theorem pmL1_resp_last (H : pmL1 tys rm kl false (kn : Int)) (hr : rm.length = tys.length)
    (hl : kl.length = tys.length) (hk : kn < tys.length) (hty : tys[kn]? = some (W32 4)) :
    pmL1 tys (rm.set kn false) (kl.set kn true) true ((kn : Int) - 1) :=
  pmL1_step H hr hl hk hty false true true _ (by decide) (by simp) (by simp)

/-- A `MsgSnap`: to `msgSnapC` or dropped, not kept. -/
theorem pmL1_snap (H : pmL1 tys rm kl b (kn : Int)) (hr : rm.length = tys.length)
    (hl : kl.length = tys.length) (hk : kn < tys.length) (hty : tys[kn]? = some (W32 7)) :
    pmL1 tys (rm.set kn false) kl b ((kn : Int) - 1) := by
  have h74 : W32 7 ≠ W32 4 := by decide
  exact pmL1_step H hr hl hk hty false b false kl
    (Iff.intro (fun h => by cases h) (fun h => absurd rfl h.2.1))
    (Iff.intro Or.inl (fun h => h.elim id (fun h' => absurd h'.2 h74))) (by simp)

/-- Any other message: kept. -/
theorem pmL1_other {ty : w32} (H : pmL1 tys rm kl b (kn : Int)) (hr : rm.length = tys.length)
    (hl : kl.length = tys.length) (hk : kn < tys.length) (hty : tys[kn]? = some ty)
    (h7 : ty ≠ W32 7) (h4 : ty ≠ W32 4) :
    pmL1 tys (rm.set kn false) (kl.set kn true) b ((kn : Int) - 1) :=
  pmL1_step H hr hl hk hty false b true _
    (Iff.intro (fun _ => ⟨rfl, h7, fun h => absurd h h4⟩) (fun _ => rfl))
    (Iff.intro Or.inl (fun h => h.elim id (fun h' => absurd h'.2 h4))) (by simp)

end steps

/-- The kept messages are in `msL`'s order. -/
theorem rnKept_sublist (msL : List Loc) (tys : List w32) (rm : List Bool) :
    (rnKept msL tys rm).Sublist msL := by
  unfold rnKept
  have := (List.filter_sublist (l := msL.zipIdx)
    (p := fun p => @decide (rnKeepAt tys rm p.2) (Classical.propDecidable _))).map Prod.fst
  rwa [List.zipIdx_map_fst] at this

/-- The second loop's output so far: the marked messages among the first `jn`. -/
def pmOut (msL : List Loc) (kl : List Bool) (jn : Nat) : List Loc :=
  (((msL.zipIdx).take jn).filter fun p => kl[p.2]? == some true).map Prod.fst

theorem pmOut_succ {msL : List Loc} {kl : List Bool} {jn : Nat} {m : Loc} {kv : Bool}
    (hm : msL[jn]? = some m) (hkv : kl[jn]? = some kv) :
    pmOut msL kl (jn + 1) = pmOut msL kl jn ++ (if kv then [m] else []) := by
  unfold pmOut
  rw [List.take_add_one, List.getElem?_zipIdx, hm]
  cases kv <;> simp [List.filter_append, hkv]

theorem pmOut_done {msL : List Loc} {tys : List w32} {rm kl : List Bool}
    (hn : tys.length = msL.length)
    (H : ∀ j : Nat, j < tys.length →
      kl[j]? = some (decide ((-1 : Int) < (j : Int)) && @decide (rnKeepAt tys rm j) (Classical.propDecidable _))) :
    pmOut msL kl msL.length = rnKept msL tys rm := by
  unfold pmOut rnKept
  rw [List.take_of_length_le (by simp)]
  congr 1
  apply List.filter_congr
  intro p hp
  obtain ⟨x, i⟩ := p
  have hi := (List.mem_zipIdx' hp).1
  simp only
  rw [H i (by omega)]
  have : decide ((-1 : Int) < (i : Int)) = true := decide_eq_true (by omega)
  rw [this]
  simp

theorem pmOut_nil {msL : List Loc} {kl : List Bool} {jn : Nat} (h : true ∉ kl) :
    pmOut msL kl jn = [] := by
  unfold pmOut
  rw [List.filter_eq_nil_iff.2]
  · rfl
  · intro p _
    simp only [beq_iff_eq]
    cases h' : kl[p.2]?
    · simp
    · rename_i v
      cases v
      · simp
      · exact absurd (List.mem_of_getElem? h') h

theorem raftNode.processMessages.wp_proof
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.processMessages.spec (GF := GF) (hG := hG) := by
  have wp_GetTo := wp_msgAt_GetTo wp_GetTo
  have wp_GetType := wp_msgAt_GetType wp_GetType
  intro E γ r sl msL
  wp_start as ⟨#Hr, #Hsl, #Hall⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave #Htys := rnMsgOk_tys E msL $$ Hall
  icases Htys with ⟨%tys, #Htys⟩
  ihave %Htyslen := BigSepL2.bigSepL2_length $$ Htys
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  wp_auto
  wp_apply wp_slice_make2 (V := Bool) sl.len as %ksl ⟨Hkeep, -⟩
  · ipureintro; word
  ihave IH : iprop(∃ (k : w64) (kl : List Bool) (b : Bool) (c : w64) (rm : List Bool),
      "r" ∷ r_ptr ↦ r ∗ "ms" ∷ ms_ptr ↦ sl ∗ "i" ∷ i_ptr ↦ k ∗
      "keep" ∷ keep_ptr ↦ ksl ∗ "Hkeep" ∷ ksl ↦* kl ∗ "count" ∷ count_ptr ↦ c ∗
      "sentAppResp" ∷ sentAppResp_ptr ↦ b ∗
      "%Hk" ∷ ⌜-1 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len ∧ kl.length = msL.length ∧
        rm.length = msL.length ∧ 0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z sl.len - 1 - sint.Z k ∧
        (c = W64 0 → true ∉ kl) ∧ pmL1 tys rm kl b (sint.Z k)⌝)
      $$ [r ms i keep Hkeep count sentAppResp]
  · iexists sl.len - W64 1, List.replicate (sint.nat sl.len) false, false, W64 0,
      List.replicate (sint.nat sl.len) false
    iframe
    ipureintro
    have e : sint.nat sl.len = tys.length := by rw [← Htyslen, Hlen.1]
    have e2 : sint.Z (sl.len - W64 1) = (tys.length : Int) - 1 := by
      rw [← Htyslen, Hlen.1]; word
    refine ⟨by word, by word, by simp [Hlen.1], by simp [Hlen.1], by word, by word,
      fun _ => by simp, ?_⟩
    rw [e, e2]; exact pmL1_init tys
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_for IH
  wp_if_destruct
  · have hk0 : 0 ≤ sint.Z k := by word
    have hkl : (sint.Z k).toNat < msL.length := by rw [Hlen.1]; word
    obtain ⟨m, hm⟩ : ∃ m, msL[(sint.Z k).toNat]? = some m :=
      ⟨_, List.getElem?_eq_getElem hkl⟩
    obtain ⟨ty, hty⟩ : ∃ ty, tys[(sint.Z k).toNat]? = some ty :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Htyslen]; exact hkl)⟩
    have hK : sint.Z k = (((sint.Z k).toNat : Nat) : Int) := by omega
    have H' : pmL1 tys rm kl b ((sint.Z k).toNat : Int) := by rw [← hK]; exact Hk.2.2.2.2.2.2.2
    have hk1 : sint.Z (k - W64 1) = ((sint.Z k).toNat : Int) - 1 := by rw [← hK]; word
    have hr : rm.length = tys.length := by rw [Hk.2.2.2.1, Htyslen]
    have hl : kl.length = tys.length := by rw [Hk.2.2.1, Htyslen]
    have hkn : (sint.Z k).toNat < tys.length := by rw [← Htyslen]; exact hkl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index sl (sint.Z k) msL DFrac.discard m (by word) $$ [] as -
    · iframe Hsl; ipureintro; exact hm
    ihave #HmOk := (BigSepL.bigSepL_lookup (Φ := fun _ m => rnMsgOk E m) hm) $$ Hall
    ihave #Hmt := (BigSepL2.bigSepL2_lookup
      (Φ := fun _ m (ty : w32) => iprop(∃ to : w64, msgAt (GF := GF) m to ty)) hm hty) $$ Htys
    icases Hmt with ⟨%to, #Hmat⟩
    wp_apply wp_GetTo m to ty $$ [$Hrpb $Hmat]
    iunfold isRNIDRemoved at Hidri
    ispecialize Hidri $$ %to
    wp_apply Hidri as %ans -
    wp_if_destruct
    rotate_left
    · -- removed member: `continue`
      wp_for_post
      iframe HΦ
      iexists k - W64 1, kl, b, c, rm.set (sint.Z k).toNat true
      iframe
      ipureintro
      refine ⟨by word, by word, Hk.2.2.1, by simp [Hk.2.2.2.1], by word, by word, Hk.2.2.2.2.2.2.1, ?_⟩
      rw [hk1]; exact pmL1_removed H' hr hl hkn hty
    wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
    wp_if_destruct
    · -- `MsgAppResp`: only the last one
      cases b
      rotate_left
      · wp_auto
        wp_for_post
        iframe HΦ
        iexists k - W64 1, kl, true, c, rm.set (sint.Z k).toNat false
        iframe
        ipureintro
        refine ⟨by word, by word, Hk.2.2.1, by simp [Hk.2.2.2.1], by word, by word, Hk.2.2.2.2.2.2.1, ?_⟩
        rw [hk1]; exact pmL1_resp_dup H' hr hl hkn hty
      wp_auto
      wp_apply wp_GetType m to _ $$ [$Hrpb $Hmat]
      wp_apply wp_GetType m to _ $$ [$Hrpb $Hmat]
      ihave %Hksl := ownSlice_len _ _ _ $$ Hkeep
      have hkk : sint.Z k < sint.Z ksl.len := by
        have := Hk.2.2.1; have := Hlen.1; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, hkk⟩)]
      wp_apply wp_store_slice_index ksl (sint.Z k) kl true $$ [$Hkeep] as Hkeep
      · ipureintro; constructor
        · word
        · have := Hk.2.2.1; word
      wp_for_post
      iframe HΦ
      iexists k - W64 1, kl.set (sint.Z k).toNat true, true, c + W64 1, rm.set (sint.Z k).toNat false
      iframe
      ipureintro
      refine ⟨by word, by word, by simp [Hk.2.2.1], by simp [Hk.2.2.2.1], by word, by word,
        fun h => absurd h (by word), ?_⟩
      rw [hk1]; exact pmL1_resp_last H' hr hl hkn hty
    · wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
      wp_if_destruct
      · -- `MsgSnap`: to `msgSnapC` if it has room, then `continue`
        iunfold isRNMsgSnapC at Hmsci
        icases Hmsci with ⟨%γc, #Hbag⟩
        ihave #Hbagch := is_bag_is_chan γc msc (rnMsgOk E) $$ Hbag
        rw [isChanBag_unseal]
        iunfold isChanBagDef at Hbag
        icases Hbag with ⟨#Hch, #Hinv⟩
        wp_apply_core chan.wp_select_nonblocking
        isplit
        · iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.nonblockingClausePre]
            iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, msc, γc, m
            isplitr
            · ipureintro; exact ⟨rfl, rfl⟩
            isplitr
            · iexact Hbagch
            unfold nonblockingSendAu nonblockingSendAuInner
            isplit
            · iinv Hinv with Hi Hclose
              iapply fupd_mask_intro Std.LawfulSet.empty_subset
              iintro Hmask
              inext
              unfold chanBagInv
              icases Hi with ⟨%s, Hoc, Hi⟩
              iexists s
              iframe Hoc
              cases s with
              | RcvPending =>
                dsimp only
                iintro Hoc
                imod Hmask with -
                imod Hclose $$ [Hoc] with -
                · inext; iexists .SndCommit m; iframe Hoc; dsimp only; iexact HmOk
                imodintro
                wp_auto
                wp_for_post
                iframe HΦ
                iexists k - W64 1, kl, b, c, rm.set (sint.Z k).toNat false
                iframe
                ipureintro
                refine ⟨by word, by word, Hk.2.2.1, by simp [Hk.2.2.2.1], by word, by word, Hk.2.2.2.2.2.2.1, ?_⟩
                rw [hk1]; exact pmL1_snap H' hr hl hkn hty
              | Buffered buff =>
                dsimp only
                iintro Hoc
                imod Hmask with -
                imod Hclose $$ [Hoc Hi] with -
                · inext; iexists .Buffered (buff ++ [m]); iframe Hoc; dsimp only
                  iapply BigSepL.bigSepL_snoc.2; iframe Hi HmOk
                imodintro
                wp_auto
                wp_for_post
                iframe HΦ
                iexists k - W64 1, kl, b, c, rm.set (sint.Z k).toNat false
                iframe
                ipureintro
                refine ⟨by word, by word, Hk.2.2.1, by simp [Hk.2.2.2.1], by word, by word, Hk.2.2.2.2.2.2.1, ?_⟩
                rw [hk1]; exact pmL1_snap H' hr hl hkn hty
              | Closed d =>
                dsimp only
                iexfalso; iexact Hi
              | _ => dsimp only; itrivial
            · itrivial
          iapply BigAndL.bigAndL_nil.2
          itrivial
        · -- `default`: dropped
          wp_auto
          wp_for_post
          iframe HΦ
          iexists k - W64 1, kl, b, c, rm.set (sint.Z k).toNat false
          iframe
          ipureintro
          refine ⟨by word, by word, Hk.2.2.1, by simp [Hk.2.2.2.1], by word, by word, Hk.2.2.2.2.2.2.1, ?_⟩
          rw [hk1]; exact pmL1_snap H' hr hl hkn hty
      wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
      wp_if_destruct
      · -- `MsgHeartbeat`: the timeout detector
        wp_apply wp_GetTo m to _ $$ [$Hrpb $Hmat]
        iunfold isRNTimeoutDetector at Htdi
        icases Htdi with ⟨%Htdnn, #HReset, #HObs⟩
        ispecialize HObs $$ %to
        wp_apply HObs as %ok %d -
        cases ok
        · -- late: the warning and the counter
          wp_auto
          ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
          · iPkgInit
          ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
          · iPkgInit
          wp_apply wp_GetTo m to _ $$ [$Hrpb $Hmat]
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1)
            (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (_root_.Perennial.fmt.IntArgValue.uint64 to)
              _root_.Perennial.fmt.ArgsWf.nil) $$ [$Hfmt $Hasl] as %str -
          wp_apply wp_String _ _ $$ [$Hzap] as %f0 -
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f1 -
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f2 -
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f3 -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl -
          wp_auto
          wp_apply wp_Warn lg _ _ $$ [$Hzap]
          · ipureintro; exact Hlgnn
          ihave Hsi : (srvInit : IProp GF) $$ []
          · iapply isPkgInit_access $$ Hpkg
          iunfold srvInit at Hsi
          icases Hsi with ⟨⟨-, -, -, -, ⟨%cn, #Hcn, #Hcs⟩⟩, -⟩
          iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at Hcs
          icases Hcs with ⟨#HInc, -⟩
          wp_auto
          wp_apply HInc
          ihave %Hksl := ownSlice_len _ _ _ $$ Hkeep
          have hkk : sint.Z k < sint.Z ksl.len := by
            have := Hk.2.2.1; have := Hlen.1; word
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, hkk⟩)]
          wp_apply wp_store_slice_index ksl (sint.Z k) kl true $$ [$Hkeep] as Hkeep
          · ipureintro; constructor
            · word
            · have := Hk.2.2.1; word
          wp_for_post
          iframe HΦ
          iexists k - W64 1, kl.set (sint.Z k).toNat true, b, c + W64 1, rm.set (sint.Z k).toNat false
          iframe
          ipureintro
          refine ⟨by word, by word, by simp [Hk.2.2.1], by simp [Hk.2.2.2.1], by word, by word,
            fun h => absurd h (by word), ?_⟩
          rw [hk1]; exact pmL1_other H' hr hl hkn hty (by assumption) (by assumption)
        · wp_auto
          ihave %Hksl := ownSlice_len _ _ _ $$ Hkeep
          have hkk : sint.Z k < sint.Z ksl.len := by
            have := Hk.2.2.1; have := Hlen.1; word
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, hkk⟩)]
          wp_apply wp_store_slice_index ksl (sint.Z k) kl true $$ [$Hkeep] as Hkeep
          · ipureintro; constructor
            · word
            · have := Hk.2.2.1; word
          wp_for_post
          iframe HΦ
          iexists k - W64 1, kl.set (sint.Z k).toNat true, b, c + W64 1, rm.set (sint.Z k).toNat false
          iframe
          ipureintro
          refine ⟨by word, by word, by simp [Hk.2.2.1], by simp [Hk.2.2.2.1], by word, by word,
            fun h => absurd h (by word), ?_⟩
          rw [hk1]; exact pmL1_other H' hr hl hkn hty (by assumption) (by assumption)
      ihave %Hksl := ownSlice_len _ _ _ $$ Hkeep
      have hkk : sint.Z k < sint.Z ksl.len := by
        have := Hk.2.2.1; have := Hlen.1; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, hkk⟩)]
      wp_apply wp_store_slice_index ksl (sint.Z k) kl true $$ [$Hkeep] as Hkeep
      · ipureintro; constructor
        · word
        · have := Hk.2.2.1; word
      wp_for_post
      iframe HΦ
      iexists k - W64 1, kl.set (sint.Z k).toNat true, b, c + W64 1, rm.set (sint.Z k).toNat false
      iframe
      ipureintro
      refine ⟨by word, by word, by simp [Hk.2.2.1], by simp [Hk.2.2.2.1], by word, by word,
        fun h => absurd h (by word), ?_⟩
      rw [hk1]; exact pmL1_other H' hr hl hkn hty (by assumption) (by assumption)
  · have hkm1 : sint.Z k = -1 := by word
    have HL : pmL1 tys rm kl b (-1) := by rw [← hkm1]; exact Hk.2.2.2.2.2.2.2
    have Hrm := Hk.2.2.2.1
    have Hdone : pmOut msL kl msL.length = rnKept msL tys rm := pmOut_done Htyslen.symm HL.1
    wp_if_destruct
    · -- nothing kept: `nil`
      have h0 : true ∉ kl := Hk.2.2.2.2.2.2.1 rfl
      iapply HΦ
      iexists []
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply (BigSepL.bigSepL_nil (Φ := fun _ m => rnMsgOk (GF := GF) E m)).2; iempintro
      iexists tys, rm
      iframe Htys
      ipureintro
      refine ⟨Hrm, ?_⟩
      rw [← Hdone, pmOut_nil h0]
    wp_apply wp_slice_make3 (V := Loc) (W64 0) c (by word) as %osl ⟨Hosl, Hocap, -⟩
    rename_i ig
    irename : (ig ↦ (zero_val w64) : IProp GF) => gi
    ihave %Hksl := ownSlice_len _ _ _ $$ Hkeep
    have Hkl := Hk.2.2.1
    ihave IH2 : iprop(∃ (j : w64) (out : GoSlice) (outL : List Loc) (g : w64) (okv : Bool),
        "i" ∷ i_ptr ↦ j ∗ "gi" ∷ ig ↦ g ∗ "ok" ∷ ok_ptr ↦ okv ∗ "ms" ∷ ms_ptr ↦ sl ∗
        "Hkeep" ∷ ksl ↦* kl ∗
        "messages" ∷ messages_ptr ↦ out ∗ "Hout" ∷ out ↦* outL ∗
        "Hcap" ∷ ownSliceCap Loc out (DFrac.own 1) ∗
        "Houtok" ∷ ([∗list] m ∈ outL, rnMsgOk E m) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ksl.len ∧ outL = pmOut msL kl (sint.nat j)⌝)
        $$ [i gi ok ms Hkeep messages Hosl Hocap]
    · iexists W64 0, osl, [], _, _
      iframe
      isplitr
      · iapply (BigSepL.bigSepL_nil (Φ := fun _ m => rnMsgOk (GF := GF) E m)).2; iempintro
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 by word]; simp [pmOut]
    wp_for IH2
    wp_if_destruct
    · have hjl : (sint.Z j).toNat < kl.length := by rw [Hksl.1]; word
      obtain ⟨kv, hkv⟩ : ∃ kv, kl[(sint.Z j).toNat]? = some kv :=
        ⟨_, List.getElem?_eq_getElem hjl⟩
      have hml : (sint.Z j).toNat < msL.length := by rw [← Hkl]; exact hjl
      obtain ⟨m, hm⟩ : ∃ m, msL[(sint.Z j).toNat]? = some m :=
        ⟨_, List.getElem?_eq_getElem hml⟩
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hjn : sint.nat j = (sint.Z j).toNat := rfl
      have Hstep := pmOut_succ (kl := kl) hm hkv
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, Hif⟩)]
      wp_apply wp_load_slice_index ksl (sint.Z j) kl (DFrac.own 1) kv (by word) $$ [$Hkeep] as Hkeep
      · ipureintro; exact hkv
      cases kv
      · wp_auto
        wp_for_post
        iframe HΦ
        iexists j + W64 1, out, outL, j, false
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, hjn, Hstep, Hj.2.2]; simp
      · ihave #HmOk := (BigSepL.bigSepL_lookup (Φ := fun _ m => rnMsgOk E m) hm) $$ Hall
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by have := Hlen.1; word⟩)]
        wp_apply wp_load_slice_index sl (sint.Z j) msL DFrac.discard m (by word) $$ [] as -
        · iframe Hsl; ipureintro; exact hm
        wp_apply wp_slice_literal (l := [m])
        isplitr
        · ipureintro; rfl
        iintro %msl ⟨Hmsl, -⟩
        wp_apply wp_slice_append out outL _ [m] (DFrac.own 1) $$ [$Hout $Hcap $Hmsl]
          as %out' ⟨Hout, Hcap, -⟩
        wp_for_post
        iframe HΦ
        iexists j + W64 1, out', outL ++ [m], j, true
        iframe i ms messages Hout Hcap Hkeep ok gi
        isplitl [Houtok]
        · iapply BigSepL.bigSepL_snoc.2
          iframe Houtok HmOk
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, hjn, Hstep, Hj.2.2]; simp
    · -- done: every mark read
      have hjn : sint.nat j = msL.length := by rw [← Hkl, Hksl.1]; word
      iapply HΦ
      iexists outL
      iframe Hout Houtok
      iexists tys, rm
      iframe Htys
      ipureintro
      refine ⟨Hrm, ?_⟩
      rw [Hj.2.2, hjn, Hdone]

/-- The spec before etcd-io/etcd#22485 (`lean` at 51547df02): the kept messages, in no stated
order (the code returned them in reverse). -/
abbrev raftNode.processMessages.spec_old : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (ms : GoSlice) (msL : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      ms ↦*□ msL ∗ [∗list] m ∈ msL, rnMsgOk E m }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"processMessages")) (Val #ms))
  {{ (out : GoSlice), RET #out; ∃ outL : List Loc, out ↦* outL ∗ [∗list] m ∈ outL, rnMsgOk E m }}

/-- The new spec is compatible: it implies the old one (it only adds the order and the types). -/
theorem raftNode.processMessages.spec_implies_old
    (h : raftNode.processMessages.spec (GF := GF) (hG := hG)) :
    raftNode.processMessages.spec_old (GF := GF) (hG := hG) := by
  intro E γ r ms msL
  iintro %Φ Hpre HΦ
  iapply h E γ r ms msL $$ Hpre
  inext
  iintro %out ⟨%outL, Hout, Hok, -⟩
  iapply HΦ
  iexists outL
  iframe

end proof

end EtcdGrove
end Perennial
