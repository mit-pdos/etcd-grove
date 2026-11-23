/-
The send steps over the bodies: `SendMsg`'s send update (`flush`: the head of the outbox becomes
the next message of the wire list) and the lost send (`lose`); the broadcast's read steps
(`bcastStep`) and the recovery's step (`recover`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostSimple

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

instance sys_inhabited : Inhabited Sys := ⟨Sys.init⟩

/-- A replica's non-empty outbox is to another replica. -/
theorem outbox_ne {S : Sys} (hS : Inv S) {i to : Nat} {m : Msg} {rest : List Msg}
    (h : S.outbox i to = m :: rest) : i < nR ∧ to < nR ∧ i ≠ to :=
  hS.1.1.2.2.2.2.2.1 i to (by simp [Sys.msgs, h])

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

instance ite_timeless {c : Prop} [Decidable c] {P Q : IProp GF} [Timeless P] [Timeless Q] :
    Timeless (if c then P else Q) := by
  split <;> infer_instance

instance chanAuthB_timeless (γ : EpNames) (i : Nat) (c : List Proposal) :
    Timeless (chanAuthB (GF := GF) γ i c) := by
  unfold chanAuthB; infer_instance

instance sysAuthB_timeless (γ : EpNames) (S : Sys) : Timeless (sysAuthB (GF := GF) γ S) := by
  unfold sysAuthB sysAuthRepB; infer_instance

instance outboxFragB_timeless (γ : EpNames) (i to : Nat) (ms : List Msg) :
    Timeless (outboxFragB (GF := GF) γ i to ms) := by
  unfold outboxFragB; infer_instance

/-- The wire lists' halves, one changed. -/
theorem sents_update (γ : EpNames) (S S' : Sys) (f t : Nat) (hf : f < nR) (ht : t < nR)
    (hne : f ≠ t) (h : ∀ f' t', (f', t') ≠ (f, t) → S'.sent f' t' = S.sent f' t') :
    ([∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
      if fr = to then iprop(True) else sentHalf (GF := GF) γ fr to (S.sent fr to)) ⊢
    sentHalf γ f t (S.sent f t) ∗ (sentHalf γ f t (S'.sent f t) -∗
      [∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
        if fr = to then iprop(True) else sentHalf γ fr to (S'.sent fr to)) := by
  iintro H
  ihave ⟨Hrow, Hrows⟩ := BigSepL.bigSepL_lookup_acc_impl (range_getElem? hf) $$ H
  ihave ⟨Hc, Hrow⟩ := BigSepL.bigSepL_lookup_acc_impl (range_getElem? ht) $$ Hrow
  irevert Hc
  simp only [if_neg hne]
  iintro Hc
  iframe Hc
  iintro Hc
  ispecialize Hrow $$ %(fun _ to => if f = to then iprop(True) else sentHalf γ f to (S'.sent f to))
  ihave Hrow := Hrow $$ [] [Hc]
  · imodintro
    iintro %k %t' %hk %hkt H
    obtain ⟨rfl, -⟩ := range_getElem?_eq hk
    rw [show (fun (_ : Nat) (to : Nat) => if f = to then iprop(True)
      else sentHalf γ f to (S'.sent f to)) t' t' = if f = t' then iprop(True)
      else sentHalf γ f t' (S.sent f t') from by
        simp only []; rw [h f t' (by simp [hkt])]]
    iexact H
  · simp only [if_neg hne]; iexact Hc
  iapply Hrows $$ %(fun _ fr => iprop([∗list] to ∈ List.range nR,
    if fr = to then iprop(True) else sentHalf γ fr to (S'.sent fr to))) [] Hrow
  imodintro
  iintro %k %f' %hk %hkf H
  obtain ⟨rfl, -⟩ := range_getElem?_eq hk
  simp only []
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro _ t' _
  rw [h f' t' (by simp [hkf])]

theorem ep_sendUpdB (γ : EpNames) (N : Namespace) (i to : Nat) (m : Msg) (rest : List Msg) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ outboxFragB γ i to (m :: rest) -∗
      ∀ ms, sentHalf γ i to ms ={⊤}=∗ sentHalf γ i to (ms ++ [m]) ∗ outboxFragB γ i to rest := by
  iintro #Hinv Hob %ms Hh
  iinv Hinv with Hi Hclose
  iunfold epInvB at Hi
  icases Hi with ⟨%S, >Ha, >%hS, >%hX, Hkv, Hfired, >Hsents, Hdel, Hops⟩
  ihave %hob := outbox_agreeB γ S i to _ $$ Ha Hob
  obtain ⟨hi, hto, hne⟩ := outbox_ne hS hob
  let S' : Sys := { S with sent := upd S.sent i (upd (S.sent i) to (S.sent i to ++ [m])),
                           outbox := upd S.outbox i (upd (S.outbox i) to rest) }
  have hS' : Inv S' := inv_step_flush S i to m rest hS hob
  ihave ⟨Hc, Hsents⟩ := sents_update γ S S' i to hi hto hne (fun f t h => by
    simp only [S', upd_apply]
    by_cases hf : f = i
    · subst hf; have : t ≠ to := fun e => h (by rw [e]); simp [this]
    · simp [hf]) $$ Hsents
  ihave %he := sentHalf_agree $$ Hc Hh
  subst he
  imod sentHalf_append $$ Hc Hh with ⟨Hc, Hh⟩
  imod outbox_updateB γ S S' i to (m :: rest) (fun j t h => by
      simp only [S', upd_apply]
      by_cases hj : j = i
      · subst hj; have : t ≠ to := fun e => h (by rw [e]); simp [this]
      · simp [hj]) ⟨rfl, rfl, rfl, rfl, fun _ => List.Subperm.refl _⟩ $$ Ha Hob with ⟨Ha, Hob⟩
  ihave Hsents := Hsents $$ [Hc]
  · simp [S']; iexact Hc
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iunfold epInvB
    iexists S'
    iframe Ha
    isplitr; · ipureintro; exact hS'
    isplitr; · ipureintro; exact InvX_rep_eq hX rfl rfl
    iframe
    rw [show S'.kv = S.kv from rfl]; iexact Hkv
  imodintro
  iframe Hh
  simp [S']
  iexact Hob

theorem ep_sendLostB (γ : EpNames) (N : Namespace) (E : CoPset) (i to : Nat) (m : Msg)
    (rest : List Msg) (hE : ↑N ⊆ E) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ outboxFragB γ i to (m :: rest) ={E}=∗ outboxFragB γ i to rest := by
  iintro #Hinv Hob
  iinv Hinv with Hi Hclose
  iunfold epInvB at Hi
  icases Hi with ⟨%S, >Ha, >%hS, >%hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hob := outbox_agreeB γ S i to _ $$ Ha Hob
  let S' : Sys := { S with outbox := upd S.outbox i (upd (S.outbox i) to rest) }
  have hS' : Inv S' := inv_step_lose S i to m rest hS hob
  imod outbox_updateB γ S S' i to (m :: rest) (fun j t h => by
      simp only [S', upd_apply]
      by_cases hj : j = i
      · subst hj; have : t ≠ to := fun e => h (by rw [e]); simp [this]
      · simp [hj]) ⟨rfl, rfl, rfl, rfl, fun _ => List.Subperm.refl _⟩ $$ Ha Hob with ⟨Ha, Hob⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S S' hS' (InvX_rep_eq hX rfl rfl) rfl rfl rfl rfl rfl $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  simp [S']
  iexact Hob


theorem ep_recoverB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState) (x : InstId)
    (n : w32) (hE : ↑N ⊆ E) (hi : i < nR) (hq : x.q < nR) (hn : (x.i : Int) ≤ zz n) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ repIdleB γ i -∗ crtLbB γ i x.q n -∗ £ 1 ={E}=∗
      ⌜∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ⌝ ∗
      repFragB γ i (hRecover σ x).1 ∗ outsOkB γ i (hRecover σ x).2 := by
  iintro #Hinv Hf Hidle #Hlb Hlc
  ihave %hcrtb := crtLb_validB γ i x.q σ n $$ Hf Hlb
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hid := sysAuthB_idle γ S i hi $$ Ha Hidle
  have hidle : S.idle i := ⟨hid.1, hid.2.1⟩
  have hx : (x.i : Int) ≤ zz ((S.rep i).crtInstance x.q) := by rw [hσ]; exact Int.le_trans hn hcrtb
  have hstep : Step S (S.applyStep i (hRecover (S.rep i) x)) := Step.recover S i x hi hidle hq hx
  have hS' := inv_step_recover S i x hS hi hidle hq hx
  have hcrt := step_crt_mono S _ hS hstep i
  generalize hS'def : S.applyStep i (hRecover (S.rep i) x) = S' at hstep hS' hcrt
  have eS' : S' = S.applyStep i ((hRecover σ x).1, (hRecover σ x).2) := by rw [← hS'def, ← hσ]
  have hrest : ∀ j, j ≠ i → sameAt S S' j := fun j hj => by
    rw [eS']
    exact applyStep_sameAt _ _ i j _ hj ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hrep : S'.rep i = (hRecover σ x).1 := by rw [eS']; simp
  have hcrt' : ∀ q, zz (σ.crtInstance q) ≤ zz ((hRecover σ x).1.crtInstance q) := fun q => by
    have := hcrt q; rwa [hσ, hrep] at this
  have hout : ∀ to, S'.outbox i to = S.outbox i to ++ sendsToB (hRecover σ x).2 to := fun to => by
    rw [eS', sendsToB_eq]; simp
  have hpend : S'.pending i = pendOf (hRecover σ x).2 := by
    rw [eS', pendOf_eq]; simp [hid.1]
  have hcur : S'.execCur i = S.execCur i ∧ S'.execIdx i = S.execIdx i := by
    rw [eS']; simp
  have hchan : S'.proposeChan i = S.proposeChan i ++ (hRecover σ x).2.filterMap Out.reprop := by
    rw [eS']; simp
  imod ghost_step_idle γ i S S' σ (hRecover σ x).1 (hRecover σ x).2 hi hrest hrep hcrt' hout hpend
    hcur hchan $$ Ha Hf Hidle with ⟨-, Ha, Hf, Hob, Hpd, Hcu, Htoks⟩
  have ekv : S'.kv = S.kv := by rw [eS']; unfold Sys.kv; simp
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S S' hS'
      ⟨NR_step hstep hX.1, fun y ps hy => hX.2 y ps (by rwa [eS', applyStep_owner'] at hy)⟩ ekv (by rw [eS']; simp) (by rw [eS']; simp) (by rw [eS']; simp)
      (by rw [eS']; simp) $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  isplitr
  · ipureintro; exact ⟨S, hS, hi, hσ⟩
  iframe Hf
  iunfold outsOkB
  iframe Hob Hpd Hcu
  iapply outOkB_of_toks γ i hi _ (hRecover_noRep σ x) $$ Htoks

theorem ep_bcastStepB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (b : Bcast) (p : Nat) (ps : List Nat) (a : Bool) (hE : ↑N ⊆ E) (hi : i < nR)
    (hb : b.peers = p :: ps) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ pendFragB γ i (some b) -∗ outboxFragB γ i p [] -∗
      £ 1 ={E}=∗ repFragB γ i (bcastRep σ b a) ∗ pendFragB γ i (b.next a) ∗
        outboxFragB γ i p (if a then [b.m] else []) := by
  iintro #Hinv Hf Hpd Hob Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hpd := pend_agreeB γ S i _ $$ Ha Hpd
  ihave %hob := outbox_agreeB γ S i p _ $$ Ha Hob
  have hp : b.peers ≠ [] := by rw [hb]; simp
  have hstep : Step S (S.bcastStep i b a) := Step.bcastStep S i b a hi hpd hp
  have hS' := inv_step_bcast S i b a hS hi hpd hp
  have hcrt := step_crt_mono S _ hS hstep i
  generalize hS'def : S.bcastStep i b a = S' at hstep hS' hcrt
  subst hσ
  have hrep : S'.rep i = bcastRep (S.rep i) b a := by
    rw [← hS'def]; cases a <;> simp [Sys.bcastStep, hb, Sys.emit]
  have hrepj : ∀ j, j ≠ i → S'.rep j = S.rep j := fun j hj => by
    rw [← hS'def]; cases a <;> simp [Sys.bcastStep, hb, Sys.emit, upd_other _ _ _ _ hj]
  have hpend : S'.pending = upd S.pending i (b.next a) := by
    rw [← hS'def]; cases a <;> simp [Sys.bcastStep, hb, Sys.emit]
  have hout : ∀ j t, S'.outbox j t =
      if j = i ∧ t = p then S.outbox i p ++ (if a then [b.m] else []) else S.outbox j t := by
    intro j t; rw [← hS'def]
    cases a
    · by_cases h : j = i ∧ t = p
      · obtain ⟨rfl, rfl⟩ := h; simp [Sys.bcastStep, hb]
      · simp only [Sys.bcastStep, hb, if_neg h]
    · by_cases hj : j = i
      · subst hj; by_cases ht : t = p
        · subst ht; simp [Sys.bcastStep, hb, Sys.emit]
        · simp [Sys.bcastStep, hb, Sys.emit, upd_apply, ht]
      · simp [Sys.bcastStep, hb, Sys.emit, upd_apply, hj]
  have hcur : S'.execCur = S.execCur ∧ S'.execIdx = S.execIdx ∧ S'.proposeChan = S.proposeChan := by
    rw [← hS'def]; cases a <;> simp [Sys.bcastStep, hb, Sys.emit]
  have hoth : S'.kv = S.kv ∧ S'.fired = S.fired ∧ S'.sent = S.sent ∧
      S'.delivered = S.delivered ∧ S'.ops = S.ops := by
    rw [← hS'def]; unfold Sys.bcastStep; rw [hb]; cases a <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- the replica's part
  ihave ⟨Hi, Hclose'⟩ := sysAuthB_acc γ S i hi $$ Ha
  iunfold sysAuthRepB at Hi
  iunfold repFragB at Hf
  iunfold pendFragB at Hpd
  iunfold outboxFragB at Hob
  icases Hi with ⟨⟨%L, HL, %hL⟩, Hobs, Hpa, Hcu, Hch⟩
  icases Hf with ⟨-, %L', HL', %hL'⟩
  icases Hpd with ⟨-, Hpd⟩
  icases Hob with ⟨%hip, Hob⟩
  ihave %hLL := rsAuth_agree _ _ _ _ _ $$ HL HL'
  obtain ⟨-, rfl⟩ := hLL
  have hcrt' : ∀ q, zz ((S.rep i).crtInstance q) ≤ zz ((bcastRep (S.rep i) b a).crtInstance q) :=
    fun q => by have := hcrt q; rwa [hrep] at this
  imod rep_update γ i L (S.rep i) (bcastRep (S.rep i) b a) hi hL'.1 hL'.2 hcrt' $$ HL HL'
    with ⟨HL, Hf⟩
  imod gvar_update _ _ _ (b.next a) $$ Hpa Hpd with ⟨Hpa, Hpd⟩
  ihave ⟨Ho, Hobs⟩ := BigSepL.bigSepL_lookup_acc_impl (range_getElem? hip.2) $$ Hobs
  imod gvar_update _ _ _ (if a then [b.m] else []) $$ Ho Hob with ⟨Ho, Hob⟩
  ihave Hobs := Hobs $$ %(fun _ t => ghostVar (GF := GF) (γ.proto.outbox i t) (1 : Qp).half
    (S'.outbox i t)) [] [Ho]
  · imodintro
    iintro %k %t %hk %hne Ht
    obtain ⟨rfl, -⟩ := range_getElem?_eq hk
    rw [show ((fun (_ : Nat) (t' : Nat) => ghostVar (GF := GF) (γ.proto.outbox i t')
      (1 : Qp).half (S'.outbox i t')) t t) = ghostVar (GF := GF) (γ.proto.outbox i t)
      (1 : Qp).half (S.outbox i t) from by simp only []; rw [hout]; simp [hne]]
    iexact Ht
  · simp only []
    rw [hout, if_pos (And.intro rfl rfl), hob, List.nil_append]
    iexact Ho
  ihave Ha := Hclose' $$ %S' %(fun j hj => ⟨hrepj j hj,
    funext fun t => by rw [hout]; simp [hj], by rw [hpend]; simp [upd_other _ _ _ _ hj],
    by rw [hcur.1], by rw [hcur.2.1], by rw [hcur.2.2]⟩)
  ihave Ha := Ha $$ [HL Hobs Hpa Hcu Hch]
  · iunfold sysAuthRepB
    rw [hrep, hpend, hcur.1, hcur.2.1, hcur.2.2]
    simp only [upd_same]
    iframe
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S S' hS'
      ⟨NR_step hstep hX.1, fun y ps hy => hX.2 y ps (by
        rw [← hS'def] at hy; unfold Sys.bcastStep at hy; split at hy <;> exact hy)⟩ hoth.1 hoth.2.1 hoth.2.2.1 hoth.2.2.2.1 hoth.2.2.2.2
      $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  iframe Hf
  isplitl [Hpd]
  · iunfold pendFragB; iframe Hpd; ipureintro; exact hi
  · iunfold outboxFragB; iframe Hob; ipureintro; exact hip

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
