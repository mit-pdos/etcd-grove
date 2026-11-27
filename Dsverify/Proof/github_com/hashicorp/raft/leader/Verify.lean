/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/Verify.lean (241f27e).
-/
/-
The leader part of the main goroutine (agent MAIN-L), stage 2: the ghost steps of the verify
futures' registry (`verifyRegistry`, core/Defs.lean) taken by `verifyLeader` (registration), the
leader loop's `verifyCh` cases (a voted future comes back) and `runLeader`'s step down (every
future in the leader's notify set is answered).

* `vreg_register`: a fresh future is registered (its registration `vregIs`, back token, notify-set
  token, vote tokens; its responder side goes into the registry, pending);
* `vreg_retire`: a voted future comes back (its back token): it leaves the registry and the
  leader's notify set; its responder side comes out (pending only if it was in the notify set, so
  registered in the leader's term);
* `vreg_unnotify`: the leader steps down: a future of its notify set leaves it, its responder side
  comes out and goes back answered.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- A full and a persistent points-to of one `w64` location cannot coexist. -/
theorem w64_own_discard (l : Loc) (a b : w64) :
    typedPointsto (GF := GF) l a (DFrac.own 1) ∗ typedPointsto l b DFrac.discard ⊢ False := by
  iintro ⟨H1, H2⟩
  ihave H1 := typedPointsto_split l a _ $$ H1
  ihave H2 := typedPointsto_split l b _ $$ H2
  rw [typedPointstoDef_w64, typedPointstoDef_w64]
  simp only [natBytes, bytesPointsto]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  icombine H1 H2 gives %Hv
  have := DFrac.valid_own_op Hv.1
  simp at this

instance vregIs_persistent' (rc : RCtx GF) (v : Loc) (T : Nat) (sv : Snap) :
    Persistent (vregIs rc v T sv) := by
  unfold vregIs; infer_instance

instance verifyReg_persistent' (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (sv : Snap)
    (L : RLog) (vch v : Loc) : Persistent (verifyReg γ rc i T sv L vch v) := by
  unfold verifyReg respWit; infer_instance

/-- A `w64` points-to made read-only. -/
theorem w64_persist (l : Loc) (a : w64) :
    typedPointsto (GF := GF) l a (DFrac.own 1) ⊢ |==> typedPointsto l a DFrac.discard :=
  (typedPointsto_dfractional l a).dfractional_persist _

/-- Vote tokens for the voters `Js` of a future `v` none of whose tokens exist yet. -/
theorem vtok_alloc (γv : GName) (v : Loc) :
    ∀ (Js : List SID) (V : GMap (Loc × SID) Unit), Js.Nodup → (∀ j ∈ Js, V !! (v, j) = none) →
    ghostMapAuth (GF := GF) γv 1 V ⊢ |==> ∃ V' : GMap (Loc × SID) Unit, ghostMapAuth γv 1 V' ∗
      ⌜∀ p, (V'.lookup p).isSome → (V.lookup p).isSome ∨ p.1 = v⌝ ∗
      [∗list] j ∈ Js, (v, j) ↪[γv] () := by
  intro Js
  induction Js with
  | nil =>
    intro V _ _
    iintro H
    imodintro
    iexists V
    iframe H
    isplitr
    · ipureintro; intro p hp; left; exact hp
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | cons j rest ih =>
    intro V hnd hfr
    iintro H
    imod ghost_map_insert (v, j) () (hfr j List.mem_cons_self) $$ H with ⟨H, Hj⟩
    have hnd' := List.nodup_cons.mp hnd
    imod ih (V.insert (v, j) ()) hnd'.2 (fun j' hj' => by
      have hne : (v, j) ≠ (v, j') := fun h => hnd'.1 (by cases h; exact hj')
      show (<[(v, j) := ()]> V) !! (v, j') = none
      rw [GMap.lookup_insert_ne _ _ hne]; exact hfr j' (List.mem_cons_of_mem _ hj')) $$ H
      with ⟨%V', H, %hV', Hrest⟩
    imodintro
    iexists V'
    iframe H
    isplitr
    · ipureintro
      intro p hp
      rcases hV' p hp with h | h
      · by_cases hpj : (v, j) = p
        · right; rw [← hpj]
        · left
          have : (<[(v, j) := ()]> V) !! p = V !! p := GMap.lookup_insert_ne _ _ hpj
          change ((<[(v, j) := ()]> V) !! p).isSome at h
          rw [this] at h; exact h
      · right; exact h
    · iapply BigSepL.bigSepL_cons.2
      iframe

/-- **Registration of a fresh verify future** (`verifyLeader`'s ghost step): the future `v` (its
quorum size now `q ≠ 0`, made read-only), registered by the leader of `T` at `sv` after the
client's snapshot `sc`, enters the registry pending (its responder side, answering `verifyQ` for
`sc`), the futures not yet back, and the leader's notify set (`NM`, the other half of whose
authority `leaderOwn` holds); its registration, back token, notify-set token and the vote tokens of
the voters `Js` come out. -/
theorem vreg_register (γ : GNames) (rc : RCtx GF) (i : SID) (v : Loc) (q : w64) (hq : q ≠ W64 0)
    (T : Nat) (sv sc : Snap) (hsc : snapLe sc sv) (NM : GMap Loc Unit) (Js : List SID)
    (hJs : Js.Nodup) :
    verifyRegistry γ rc i ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NM ∗
      v.[verifyFuture, go!"quorumSize"] ↦ q ∗ histLb γ sc ∗
      deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc) ⊢ |==>
    (verifyRegistry γ rc i ∗ ghostMapAuth rc.names.vnm (1 : Qp).half (<[v := ()]> NM) ∗
      v.[verifyFuture, go!"quorumSize"] ↦□ q ∗ vregIs rc v T sv ∗ backTok rc v ∗ nmTok rc v ∗
      ([∗list] j ∈ Js, voteTok rc v j) ∗ ⌜NM !! v = none⌝) := by
  unfold verifyRegistry
  iintro ⟨⟨%V, %R, %Live, %NMs, HV, HR, HL, HN, %Hc, #HRq, HLive⟩, HN2, Hq, #Hsc, Hresp⟩
  obtain ⟨hVR, hLR, hNL⟩ := Hc
  ihave %HNeq := ghostMapAuth_agree _ _ _ _ _ $$ HN HN2
  subst HNeq
  -- `v` is not registered: a registered future's quorum size is read-only
  have hR : R !! v = none ∨ ∃ x, R !! v = some x := by
    cases R !! v with
    | none => left; rfl
    | some x => right; exact ⟨x, rfl⟩
  rcases hR with hR | ⟨x, hRv⟩
  rotate_left
  · ihave Hx := (BigSepM.bigSepM_lookup (Φ := fun v _x => iprop(∃ q : w64,
      v.[verifyFuture, go!"quorumSize"] ↦□ q ∗ ⌜q ≠ W64 0⌝)) hRv) $$ HRq
    icases Hx with ⟨%q', Hq', -⟩
    iexfalso
    iapply w64_own_discard _ q q' $$ [Hq Hq']
    iframe; iexact Hq'
  have hL : Live !! v = none := by
    cases h : Live !! v with
    | none => rfl
    | some _ => exfalso; have := hLR v (by simp [h]); simp [hR] at this
  have hN : NMs !! v = none := by
    cases h : NMs !! v with
    | none => rfl
    | some _ => exfalso; have := hNL v (by simp [h]); simp [hL] at this
  imod w64_persist _ q $$ Hq with #Hq
  imod ghost_map_insert_persist v (T, sv) hR $$ HR with ⟨HR, #Hreg⟩
  imod ghost_map_insert v () hL $$ HL with ⟨HL, Hback⟩
  ihave HN := (ghostMapAuth_halves (GF := GF) rc.names.vnm NMs).2 $$ [HN HN2]
  · iframe
  imod ghost_map_insert (γ := rc.names.vnm) v () hN $$ HN with ⟨HN, Hnm⟩
  ihave ⟨HN, HN2⟩ := (ghostMapAuth_halves (GF := GF) rc.names.vnm _).1 $$ HN
  imod vtok_alloc rc.names.vtok v Js V hJs (fun j _ => by
    cases h : V !! (v, j) with
    | none => rfl
    | some _ => exfalso; have := hVR (v, j) (by simp [h]); simp [hR] at this) $$ HV
    with ⟨%V', HV, %hV', Htoks⟩
  imodintro
  unfold vregIs backTok nmTok voteTok
  isplitl [HV HR HL HN HLive Hresp]
  · iexists V', R.insert v (T, sv), Live.insert v (), NMs.insert v ()
    iframe HV HR HL HN
    isplitr
    · ipureintro
      refine ⟨fun p hp => ?_, fun w hw => ?_, fun w hw => ?_⟩
      · rcases hV' p hp with h | h
        · have := hVR p h
          show ((<[v := (T, sv)]> R) !! p.1).isSome
          by_cases hv : v = p.1
          · rw [← hv, GMap.lookup_insert]; rfl
          · rw [GMap.lookup_insert_ne _ _ hv]; exact this
        · show ((<[v := (T, sv)]> R) !! p.1).isSome
          rw [h, GMap.lookup_insert]; rfl
      · show ((<[v := (T, sv)]> R) !! w).isSome
        change ((<[v := ()]> Live) !! w).isSome at hw
        by_cases hv : v = w
        · rw [← hv, GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ hv] at hw ⊢; exact hLR w hw
      · show ((<[v := ()]> Live) !! w).isSome
        change ((<[v := ()]> NMs) !! w).isSome at hw
        by_cases hv : v = w
        · rw [← hv, GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ hv] at hw ⊢; exact hNL w hw
    isplitl [HRq]
    · iapply (BigSepM.bigSepM_insert (Φ := fun v _x => iprop(∃ q : w64,
        v.[verifyFuture, go!"quorumSize"] ↦□ q ∗ ⌜q ≠ W64 0⌝)) hR).2
      isplitr
      · iexists q; iframe #; ipureintro; exact hq
      iexact HRq
    iapply (BigSepM.bigSepM_insert hL).2
    isplitl [Hresp]
    · iexists T, sv
      isplitr
      · ipureintro; exact GMap.lookup_insert _ _ _
      unfold vregState
      ileft
      iexists sc
      iframe #
      iframe
      ipureintro
      refine ⟨hsc, ?_⟩
      rw [GMap.lookup_insert]; rfl
    iapply (BigSepM.bigSepM_mono (fun {w x} hw => ?_)) $$ HLive
    have hv : v ≠ w := fun h => by
      subst h; rw [show Live !! v = some x from hw] at hL; cases hL
    rw [GMap.lookup_insert_ne _ _ hv, GMap.lookup_insert_ne _ _ hv]
  iframe
  iframe #
  ipureintro; exact hN

/-- A big separating conjunction over a map without one key (dropping its entry). -/
theorem bigSepM_drop {V : Type} (Φ : Loc → V → IProp GF) (M : GMap Loc V) (k : Loc) :
    ([∗map] x ↦ y ∈ M, Φ x y) ⊢ [∗map] x ↦ y ∈ GMap.delete k M, Φ x y := by
  cases h : M !! k with
  | none =>
    have : GMap.delete k M = M := by
      apply GMap.ext; intro k'
      show (GMap.delete k M) !! k' = M !! k'
      by_cases hk : k = k'
      · subst hk; rw [GMap.lookup_delete, h]
      · rw [GMap.lookup_delete_ne _ hk]
    rw [this]
  | some y =>
    iintro H
    ihave ⟨-, H⟩ := (BigSepM.bigSepM_delete (show get? M k = some y from h)).1 $$ H
    iexact H

/-- Taking the token of `k` (not yet taken, `¬ P k`) from a list of tokens some of which are taken
(`P`). -/
theorem tok_take (tok : SID → IProp GF) (P : SID → Prop) (k : SID) :
    ∀ (L : List SID), k ∈ L → ¬ P k →
    ([∗list] j ∈ L, ⌜P j⌝ ∨ tok j) ⊢ tok k ∗ [∗list] j ∈ L, ⌜P j ∨ j = k⌝ ∨ tok j := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons x L ih =>
    intro hk hP
    iintro H
    ihave ⟨Hx, H⟩ := BigSepL.bigSepL_cons.1 $$ H
    by_cases hxk : x = k
    · subst hxk
      icases Hx with (%hx | Hx)
      · exact absurd hx hP
      iframe Hx
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · ileft; ipureintro; right; rfl
      iapply (BigSepL.bigSepL_mono (fun {n y} _ => ?_)) $$ H
      iintro (%hy | Hy)
      · ileft; ipureintro; left; exact hy
      · iright; iexact Hy
    · have hk' : k ∈ L := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hxk
        · exact h
      ihave ⟨Hk, H⟩ := ih hk' hP $$ H
      iframe Hk
      iapply BigSepL.bigSepL_cons.2
      iframe H
      icases Hx with (%hx | Hx)
      · ileft; ipureintro; left; exact hx
      · iright; iexact Hx

/-- `delete` of an absent key. -/
theorem gmap_delete_absent {K V : Type} [DecidableEq K] (m : GMap K V) (k : K) (h : m !! k = none) :
    GMap.delete k m = m := by
  apply GMap.ext; intro k'
  show (GMap.delete k m) !! k' = m !! k'
  by_cases hk : k = k'
  · subst hk; rw [GMap.lookup_delete, h]
  · rw [GMap.lookup_delete_ne _ hk]

/-- The leader's notify set without `v`, from the halves of its authority (the registry's and
`leaderOwn`'s) and `v`'s token. -/
theorem vnm_delete (rc : RCtx GF) (v : Loc) (NM : GMap Loc Unit) :
    ghostMapAuth (GF := GF) rc.names.vnm (1 : Qp).half NM ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NM ∗
      nmTok rc v ⊢ |==>
    (ghostMapAuth rc.names.vnm (1 : Qp).half (GMap.delete v NM) ∗
      ghostMapAuth rc.names.vnm (1 : Qp).half (GMap.delete v NM)) := by
  iintro ⟨H1, H2, Ht⟩
  ihave H := (ghostMapAuth_halves (GF := GF) rc.names.vnm NM).2 $$ [H1 H2]
  · iframe
  unfold nmTok
  imod ghost_map_delete (γ := rc.names.vnm) $$ H Ht with H
  imodintro
  iapply (ghostMapAuth_halves (GF := GF) rc.names.vnm _).1 $$ H

/-- **A voted future comes back** (the leader loop's `verifyCh` case, with the future's back
token and registration): it leaves the futures not yet back and the leader's notify set (`NM`, of
the leader of `T`); its responder state comes out: pending only if it was in the notify set (then
registered in `T`), else already answered. -/
theorem vreg_retire (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch v : Loc) (T' : Nat)
    (sv : Snap) (NM : GMap Loc Unit) :
    verifyRegistry γ rc i ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NM ∗
      ([∗map] w ↦ _u ∈ NM, leaderNotifyEntry γ rc i T vch w) ∗ backTok rc v ∗ vregIs rc v T' sv ⊢
    |==> (verifyRegistry γ rc i ∗ ghostMapAuth rc.names.vnm (1 : Qp).half (GMap.delete v NM) ∗
      ([∗map] w ↦ _u ∈ GMap.delete v NM, leaderNotifyEntry γ rc i T vch w) ∗
      ((∃ sc : Snap, histLb γ sc ∗ histLb γ sv ∗ ⌜snapLe sc sv ∧ T' = T⌝ ∗
          deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
        deferDone (v.[verifyFuture, go!"deferError"]))) := by
  unfold verifyRegistry
  iintro ⟨⟨%V, %R, %Live, %NMs, HV, HR, HL, HN, %Hc, #HRq, HLive⟩, HN2, HNM, Hback, #Hreg⟩
  obtain ⟨hVR, hLR, hNL⟩ := Hc
  ihave %HNeq := ghostMapAuth_agree _ _ _ _ _ $$ HN HN2
  subst HNeq
  unfold backTok vregIs
  icombine HL Hback gives %hLv
  icombine HR Hreg gives %hRv
  ihave ⟨Hv, HLive⟩ := (BigSepM.bigSepM_delete (Φ := fun v _u => iprop(∃ (T : Nat) (sv : Snap),
      ⌜R !! v = some (T, sv)⌝ ∗ vregState γ rc i v sv ((NMs !! v).isSome))) hLv).1 $$ HLive
  icases Hv with ⟨%T1, %sv1, %hR1, Hst⟩
  rw [hRv] at hR1
  cases hR1
  imod ghost_map_delete (γ := rc.names.vlive) $$ HL Hback with HL
  -- the rest of the futures not yet back, with the notify set without `v`
  have hrest : ∀ w, w ≠ v → (GMap.delete v NMs) !! w = NMs !! w :=
    fun w hw => GMap.lookup_delete_ne _ (Ne.symm hw)
  cases hNv : NMs !! v with
  | none =>
    rw [gmap_delete_absent NMs v hNv]
    unfold vregState
    icases Hst with (⟨%sc, -, %Hsc, -⟩ | Hd)
    · exfalso; exact absurd Hsc.2 (by simp)
    imodintro
    isplitr [HN2 HNM Hd]
    · iexists V, R, GMap.delete v Live, NMs
      iframe HV HR HL HN
      isplitr
      · ipureintro
        refine ⟨hVR, fun w hw => ?_, fun w hw => ?_⟩
        · by_cases hwv : v = w
          · subst hwv; simp at hw
          · rw [show (GMap.delete v Live) !! w = Live !! w from GMap.lookup_delete_ne _ hwv] at hw
            exact hLR w hw
        · by_cases hwv : v = w
          · subst hwv; rw [hNv] at hw; simp at hw
          · rw [show (GMap.delete v Live) !! w = Live !! w from GMap.lookup_delete_ne _ hwv]
            exact hNL w hw
      isplitr
      · iexact HRq
      iexact HLive
    iframe
  | some u =>
    ihave ⟨Hent, HNM⟩ := (BigSepM.bigSepM_delete (Φ := fun w _u => leaderNotifyEntry γ rc i T vch w)
      (show get? NMs v = some u from hNv)).1 $$ HNM
    unfold leaderNotifyEntry verifyReg
    icases Hent with ⟨%sv2, %L2, #Hsv2, ⟨%q, #Hreg2, -⟩, Hnm⟩
    ihave %Hag := vregIs_agree rc v T' T sv sv2 $$ [Hreg Hreg2]
    · unfold vregIs; iframe #
    obtain ⟨hT, hsv⟩ := Hag
    subst hsv
    imod vnm_delete rc v NMs $$ [HN HN2 Hnm] with ⟨HN, HN2⟩
    · iframe
    imodintro
    isplitr [HN2 HNM Hst]
    · iexists V, R, GMap.delete v Live, GMap.delete v NMs
      iframe HV HR HL HN
      isplitr
      · ipureintro
        refine ⟨hVR, fun w hw => ?_, fun w hw => ?_⟩
        · by_cases hwv : v = w
          · subst hwv; simp at hw
          · rw [show (GMap.delete v Live) !! w = Live !! w from GMap.lookup_delete_ne _ hwv] at hw
            exact hLR w hw
        · by_cases hwv : v = w
          · subst hwv; simp at hw
          · rw [show (GMap.delete v Live) !! w = Live !! w from GMap.lookup_delete_ne _ hwv]
            rw [show (GMap.delete v NMs) !! w = NMs !! w from GMap.lookup_delete_ne _ hwv] at hw
            exact hNL w hw
      isplitr
      · iexact HRq
      iapply (BigSepM.bigSepM_mono (fun {w x} hw => ?_)) $$ HLive
      have hwv : w ≠ v := fun h => by
        rw [h, Iris.Std.get?_delete_eq rfl] at hw; cases hw
      rw [hrest w hwv]
    iframe HN2 HNM
    unfold vregState
    icases Hst with (⟨%sc, #Hsc, %Hsc, Hresp⟩ | Hd)
    · ileft; iexists sc; iframe; iframe #; ipureintro; exact ⟨Hsc.1, hT⟩
    · iright; iexact Hd

/-- **The leader steps down**: a future `v` of its notify set `NM` leaves it (with its token);
its responder state comes out (pending or already answered) and goes back answered. -/
theorem vreg_unnotify (γ : GNames) (rc : RCtx GF) (i : SID) (v : Loc) (NM : GMap Loc Unit) :
    verifyRegistry γ rc i ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NM ∗ nmTok rc v ⊢
    |==> (((∃ sc : Snap, deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
          deferDone (v.[verifyFuture, go!"deferError"])) ∗
      (deferDone (v.[verifyFuture, go!"deferError"]) -∗
        verifyRegistry γ rc i ∗ ghostMapAuth rc.names.vnm (1 : Qp).half (GMap.delete v NM))) := by
  unfold verifyRegistry
  iintro ⟨⟨%V, %R, %Live, %NMs, HV, HR, HL, HN, %Hc, #HRq, HLive⟩, HN2, Hnm⟩
  obtain ⟨hVR, hLR, hNL⟩ := Hc
  ihave %HNeq := ghostMapAuth_agree _ _ _ _ _ $$ HN HN2
  subst HNeq
  ihave %hNv : ⌜NMs !! v = some ()⌝ $$ [HN Hnm]
  · unfold nmTok; icombine HN Hnm gives %h; ipureintro; exact h
  have hLv : (Live !! v).isSome := hNL v (by rw [hNv]; rfl)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hLv
  ihave ⟨Hv, HLive⟩ := (BigSepM.bigSepM_delete (Φ := fun v _u => iprop(∃ (T : Nat) (sv : Snap),
      ⌜R !! v = some (T, sv)⌝ ∗ vregState γ rc i v sv ((NMs !! v).isSome))) hu).1 $$ HLive
  icases Hv with ⟨%T1, %sv1, %hR1, Hst⟩
  imod vnm_delete rc v NMs $$ [HN HN2 Hnm] with ⟨HN, HN2⟩
  · iframe
  imodintro
  isplitl [Hst]
  · unfold vregState
    icases Hst with (⟨%sc, -, -, Hresp⟩ | Hd)
    · ileft; iexists sc; iexact Hresp
    · iright; iexact Hd
  iintro Hd
  isplitl [HV HR HL HN HLive Hd]
  · iexists V, R, Live, GMap.delete v NMs
    iframe HV HR HL HN
    isplitr
    · ipureintro
      refine ⟨hVR, hLR, fun w hw => ?_⟩
      by_cases hwv : v = w
      · subst hwv; simp at hw
      · rw [show (GMap.delete v NMs) !! w = NMs !! w from GMap.lookup_delete_ne _ hwv] at hw
        exact hNL w hw
    isplitr
    · iexact HRq
    iapply (BigSepM.bigSepM_delete (Φ := fun w _u => iprop(∃ (T : Nat) (sv : Snap),
        ⌜R !! w = some (T, sv)⌝ ∗ vregState γ rc i w sv (((GMap.delete v NMs) !! w).isSome)))
        (show get? Live v = some u from hu)).2
    isplitl [Hd]
    · iexists T1, sv1; isplitr; · ipureintro; exact hR1
      unfold vregState; iright; iexact Hd
    iapply (BigSepM.bigSepM_mono (fun {w x} hw => ?_)) $$ HLive
    have hwv : v ≠ w := fun h => by
      rw [← h, Iris.Std.get?_delete_eq rfl] at hw; cases hw
    rw [show (GMap.delete v NMs) !! w = NMs !! w from GMap.lookup_delete_ne _ hwv]
  iexact HN2

end defs

end github_com.hashicorp.raft

end Perennial
