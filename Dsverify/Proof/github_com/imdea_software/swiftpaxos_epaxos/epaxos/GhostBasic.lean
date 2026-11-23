/-
The interface's basic ghost laws over the bodies (`EpaxosGhost.lean` states them over its names):
agreement of each fragment with the authority, the updates of the authority, `crtLb`, the
re-proposal tokens, the allocation.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostDeliver

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem repFragB_lt (γ : EpNames) (i : Nat) (σ : RState) : repFragB (GF := GF) γ i σ -∗ ⌜i < nR⌝ := by
  iintro H; iunfold repFragB at H; icases H with ⟨%h, -⟩; ipureintro; exact h

/-- A channel's authority for a smaller channel holds for a larger one. -/
theorem chanAuthB_mono (γ : EpNames) (i : Nat) (c c' : List Proposal) (h : c.Subperm c') :
    chanAuthB (GF := GF) γ i c ⊢ chanAuthB γ i c' := by
  unfold chanAuthB
  iintro ⟨%M, %l, HM, %hM⟩
  iexists M, l
  iframe HM
  ipureintro
  exact ⟨hM.1, hM.2.1, hM.2.2.trans h⟩

/-- The channels grow, nothing else tracked changes. -/
theorem sysAuthB_chan_mono (γ : EpNames) (S S' : Sys)
    (hrep : S'.rep = S.rep) (hob : S'.outbox = S.outbox) (hpd : S'.pending = S.pending)
    (hcur : S'.execCur = S.execCur) (hidx : S'.execIdx = S.execIdx)
    (hch : ∀ j, (S.proposeChan j).Subperm (S'.proposeChan j)) :
    sysAuthB (GF := GF) γ S ⊢ sysAuthB γ S' := by
  unfold sysAuthB
  apply BigSepL.bigSepL_mono
  intro _ j _
  unfold sysAuthRepB
  rw [hrep, hob, hpd, hcur, hidx]
  iintro ⟨H1, H2, H3, H4, H5⟩
  iframe H1 H2 H3 H4
  iapply chanAuthB_mono γ j _ _ (hch j) $$ H5

theorem sysAuthB_rep_update (γ : EpNames) (S : Sys) (i : Nat) (σ σ' : RState)
    (hcrt : ∀ q, zz ((S.rep i).crtInstance q) ≤ zz (σ'.crtInstance q)) :
    sysAuthB (GF := GF) γ S -∗ repFragB γ i σ ==∗
      sysAuthB γ { S with rep := upd S.rep i σ' } ∗ repFragB γ i σ' := by
  iintro Ha Hf
  ihave %hi := repFragB_lt γ i σ $$ Hf
  ihave ⟨Hi, Hclose⟩ := sysAuthB_acc γ S i hi $$ Ha
  ihave %hσ := rep_agree γ S i σ $$ Hi Hf
  iunfold sysAuthRepB at Hi
  iunfold repFragB at Hf
  icases Hi with ⟨⟨%L, HL, %hL⟩, Hrest⟩
  icases Hf with ⟨-, %L', HL', %hL'⟩
  ihave %hLL := rsAuth_agree _ _ _ _ _ $$ HL HL'
  obtain ⟨-, rfl⟩ := hLL
  subst hσ
  imod rep_update γ i L (S.rep i) σ' hi hL'.1 hL'.2 hcrt $$ HL HL' with ⟨HL, Hf⟩
  imodintro
  iframe Hf
  iapply Hclose $$ %({ S with rep := upd S.rep i σ' } : Sys) %(fun j hj => ⟨by simp [upd_other _ _ _ _ hj], rfl, rfl, rfl, rfl, rfl⟩)
  iunfold sysAuthRepB
  iframe Hrest
  simp only [upd_same]
  iexact HL

theorem sys_updateB (γ : EpNames) (S S' : Sys) (i : Nat) (σ : RState)
    (h : ∀ j, j ≠ i → S'.rep j = S.rep j)
    (hcrt : ∀ q, zz ((S.rep i).crtInstance q) ≤ zz ((S'.rep i).crtInstance q))
    (hrest : S'.outbox = S.outbox ∧ S'.pending = S.pending ∧ S'.execCur = S.execCur ∧
      S'.execIdx = S.execIdx ∧ ∀ j, (S.proposeChan j).Subperm (S'.proposeChan j)) :
    sysAuthB (GF := GF) γ S -∗ repFragB γ i σ ==∗ sysAuthB γ S' ∗ repFragB γ i (S'.rep i) := by
  iintro Ha Hf
  imod sysAuthB_rep_update γ S i σ (S'.rep i) hcrt $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Hf
  iapply sysAuthB_chan_mono γ ({ S with rep := upd S.rep i (S'.rep i) } : Sys) S' ?_ hrest.1
    hrest.2.1 hrest.2.2.1 hrest.2.2.2.1 hrest.2.2.2.2 $$ Ha
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [upd_other _ _ _ _ hj, h j hj]

theorem crtLb_getB (γ : EpNames) (i q : Nat) (σ : RState) :
    repFragB (GF := GF) γ i σ -∗ repFragB γ i σ ∗ crtLbB γ i q (σ.crtInstance q) := by
  iintro Hf
  iunfold repFragB at Hf
  icases Hf with ⟨%hi, %L, HL, %hL⟩
  have hk : L[L.length - 1]? = some σ := by
    rw [List.getLast?_eq_getElem?] at hL; exact hL.1
  ihave ⟨HL, #Hidx⟩ := rsIdx_get _ _ L _ σ hk $$ HL
  isplitl [HL]
  · iunfold repFragB
    isplitr; · ipureintro; exact hi
    iexists L; iframe HL; ipureintro; exact hL
  · iunfold crtLbB
    iexists L.length - 1, σ
    iframe Hidx
    ipureintro; exact Int.le_refl _

theorem crtLb_validB (γ : EpNames) (i q : Nat) (σ : RState) (n : w32) :
    repFragB (GF := GF) γ i σ -∗ crtLbB γ i q n -∗ ⌜zz n ≤ zz (σ.crtInstance q)⌝ := by
  iintro Hf Hlb
  iunfold repFragB at Hf
  iunfold crtLbB at Hlb
  icases Hf with ⟨-, %L, HL, %hL⟩
  icases Hlb with ⟨%k, %σ0, Hidx, %hn⟩
  ihave %hk := rsAuth_idx_lookup _ _ _ _ _ $$ HL Hidx
  ipureintro
  exact Int.le_trans hn (hL.2 σ0 (List.mem_of_getElem? hk) q)

theorem crtLb_monoB (γ : EpNames) (i q : Nat) (n n' : w32) (h : zz n' ≤ zz n) :
    crtLbB (GF := GF) γ i q n -∗ crtLbB γ i q n' := by
  iintro H
  iunfold crtLbB at H
  iunfold crtLbB
  icases H with ⟨%k, %σ0, Hidx, %hn⟩
  iexists k, σ0
  iframe Hidx
  ipureintro; exact Int.le_trans h hn

theorem inChan_toks (γ : EpNames) (i : Nat) (ps : List Proposal) :
    ([∗list] p ∈ ps, inChanB (GF := GF) γ i p) ⊢ [∗list] p ∈ ps, chanTok γ i p := by
  apply BigSepL.bigSepL_mono
  intro _ p _
  unfold inChanB
  iintro ⟨-, H⟩
  iexact H

theorem inChan_subB (γ : EpNames) (S : Sys) (i : Nat) (ps : List Proposal) :
    sysAuthB (GF := GF) γ S -∗ ([∗list] p ∈ ps, inChanB γ i p) -∗ ⌜ps.Subperm (S.proposeChan i)⌝ := by
  cases ps with
  | nil => iintro - -; ipureintro; exact List.nil_subperm
  | cons p ps =>
    iintro Ha H
    ihave %hi : ⌜i < nR⌝ $$ [H]
    · ihave ⟨Hp, -⟩ := BigSepL.bigSepL_cons.1 $$ H
      iunfold inChanB at Hp
      icases Hp with ⟨%h, -⟩
      ipureintro; exact h
    ihave ⟨Hi, -⟩ := sysAuthB_acc γ S i hi $$ Ha
    iunfold sysAuthRepB at Hi
    icases Hi with ⟨-, -, -, -, Hch⟩
    ihave H := inChan_toks γ i _ $$ H
    iapply chan_sub $$ Hch H

theorem outbox_agreeB (γ : EpNames) (S : Sys) (i to : Nat) (ms : List Msg) :
    sysAuthB (GF := GF) γ S -∗ outboxFragB γ i to ms -∗ ⌜S.outbox i to = ms⌝ := by
  iintro Ha Hf
  iunfold outboxFragB at Hf
  icases Hf with ⟨%h, Hf⟩
  ihave ⟨Hi, -⟩ := sysAuthB_acc γ S i h.1 $$ Ha
  iunfold sysAuthRepB at Hi
  icases Hi with ⟨-, Hob, -⟩
  ihave Ho := BigSepL.bigSepL_lookup (range_getElem? h.2) $$ Hob
  iapply gvar_agree $$ Ho Hf

theorem pend_agreeB (γ : EpNames) (S : Sys) (i : Nat) (ob : Option Bcast) :
    sysAuthB (GF := GF) γ S -∗ pendFragB γ i ob -∗ ⌜S.pending i = ob⌝ := by
  iintro Ha Hf
  iunfold pendFragB at Hf
  icases Hf with ⟨%h, Hf⟩
  ihave ⟨Hi, -⟩ := sysAuthB_acc γ S i h $$ Ha
  iunfold sysAuthRepB at Hi
  icases Hi with ⟨-, -, Hpd, -⟩
  iapply gvar_agree $$ Hpd Hf

theorem cur_agreeB (γ : EpNames) (S : Sys) (i : Nat) (cur : List InstId) (idx : Nat) :
    sysAuthB (GF := GF) γ S -∗ curFragB γ i cur idx -∗ ⌜S.execCur i = cur ∧ S.execIdx i = idx⌝ := by
  iintro Ha Hf
  iunfold curFragB at Hf
  icases Hf with ⟨%h, Hf⟩
  ihave ⟨Hi, -⟩ := sysAuthB_acc γ S i h $$ Ha
  iunfold sysAuthRepB at Hi
  icases Hi with ⟨-, -, -, Hcu, -⟩
  ihave %e := gvar_agree _ _ _ $$ Hcu Hf
  ipureintro; exact Prod.mk.inj e

/-- The outbox to `to` moves (the authority's outboxes become `S'`'s, which differ only there). -/
theorem outbox_updateB (γ : EpNames) (S S' : Sys) (i to : Nat) (ms : List Msg)
    (h : ∀ j t, (j, t) ≠ (i, to) → S'.outbox j t = S.outbox j t)
    (hrest : S'.rep = S.rep ∧ S'.pending = S.pending ∧ S'.execCur = S.execCur ∧
      S'.execIdx = S.execIdx ∧ ∀ j, (S.proposeChan j).Subperm (S'.proposeChan j)) :
    sysAuthB (GF := GF) γ S -∗ outboxFragB γ i to ms ==∗ sysAuthB γ S' ∗ outboxFragB γ i to (S'.outbox i to) := by
  iintro Ha Hf
  iunfold outboxFragB at Hf
  icases Hf with ⟨%hit, Hf⟩
  ihave ⟨Hi, Hclose⟩ := sysAuthB_acc γ S i hit.1 $$ Ha
  iunfold sysAuthRepB at Hi
  icases Hi with ⟨HL, Hob, Hrest⟩
  ihave ⟨Ho, Hob⟩ := BigSepL.bigSepL_lookup_acc_impl (range_getElem? hit.2) $$ Hob
  imod gvar_update _ _ _ (S'.outbox i to) $$ Ho Hf with ⟨Ho, Hf⟩
  ihave Hob := Hob $$ %(fun _ t => ghostVar (GF := GF) (γ.proto.outbox i t) (1 : Qp).half
    (S'.outbox i t))
  ihave Hob := Hob $$ [] Ho
  · imodintro
    iintro %k %t %hk %hne Ht
    obtain ⟨rfl, -⟩ := range_getElem?_eq hk
    rw [show ((fun (_ : Nat) (t' : Nat) => ghostVar (GF := GF) (γ.proto.outbox i t')
      (1 : Qp).half (S'.outbox i t')) t t) = ghostVar (GF := GF) (γ.proto.outbox i t)
      (1 : Qp).half (S.outbox i t) from by simp only []; rw [h i t (by simp [hne])]]
    iexact Ht
  let Sm : Sys := { S with outbox := S'.outbox }
  ihave Ha := Hclose $$ %Sm %(fun j hj => ⟨rfl, funext fun t => h j t (by simp [hj]), rfl, rfl,
    rfl, rfl⟩)
  ihave Ha := Ha $$ [HL Hob Hrest]
  · iunfold sysAuthRepB
    iframe
  imodintro
  isplitl [Ha]
  · iapply sysAuthB_chan_mono γ Sm S' hrest.1 rfl hrest.2.1 hrest.2.2.1 hrest.2.2.2.1
      hrest.2.2.2.2 $$ Ha
  · iunfold outboxFragB
    iframe Hf
    ipureintro; exact hit


/-! ## Allocation -/

/-- One replica's fresh ghost state, by its names. -/
def repRaw (i : Nat) (b : GName × (Nat → GName) × GName × GName × GName) : IProp GF :=
  iprop(rsAuth b.1 1 [RState.init i] ∗
    ([∗list] to ∈ List.range nR, ghostVar (GF := GF) (b.2.1 to) 1 ([] : List Msg)) ∗
    ghostVar (GF := GF) b.2.2.1 1 (none : Option Bcast) ∗
    ghostVar (GF := GF) b.2.2.2.1 1 (([] : List InstId), (0 : Nat)) ∗
    ghostMapAuth (GF := GF) b.2.2.2.2 1 (∅ : GMap Nat Proposal))

theorem repRaw_alloc (i : Nat) : ⊢ |==> ∃ b, repRaw (GF := GF) i b := by
  imod rsAuth_alloc [RState.init i] with ⟨%γr, Hr⟩
  imod allocFun (0 : GName) (fun _ g => ghostVar (GF := GF) g 1 ([] : List Msg))
    (fun _ => ghostVar_alloc ([] : List Msg)) (List.range nR) List.nodup_range with ⟨%go, Ho⟩
  imod ghostVar_alloc (GF := GF) (none : Option Bcast) with ⟨%gp, Hp⟩
  imod ghostVar_alloc (GF := GF) (([] : List InstId), (0 : Nat)) with ⟨%gc, Hc⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Proposal) with ⟨%gm, Hm⟩
  imodintro
  iexists (γr, go, gp, gc, gm)
  iunfold repRaw
  iframe

theorem quarter_add : Qp.quarter + Qp.threeQuarters = 1 := by
  apply Subtype.ext; show (1 / 4 + 3 / 4 : Rat) = 1; grind

theorem rsAuth_split1 (γ : GName) (l : List RState) :
    rsAuth (GF := GF) γ 1 l ⊢ rsAuth γ Qp.quarter l ∗ rsAuth γ Qp.threeQuarters l := by
  rw [← quarter_add]; exact (rsAuth_op _ _ _ _).1

theorem repRaw_split (γ : EpNames) (i : Nat) (hi : i < nR)
    (b : GName × (Nat → GName) × GName × GName × GName)
    (hb : γ.proto.rep i = b.1 ∧ (∀ to, γ.proto.outbox i to = b.2.1 to) ∧ γ.proto.pend i = b.2.2.1 ∧
      γ.proto.cur i = b.2.2.2.1 ∧ γ.proto.chan i = b.2.2.2.2) :
    repRaw (GF := GF) i b ⊢ sysAuthRepB γ Sys.init i ∗ repFragB γ i (RState.init i) ∗ repIdleB γ i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  iintro H
  iunfold repRaw at H
  icases H with ⟨Hr, Ho, Hp, Hc, Hm⟩
  ihave ⟨Hr1, Hr2⟩ := rsAuth_split1 _ _ $$ Hr
  ihave Ho := BigSepL.bigSepL_mono (Ψ := fun _ to =>
      iprop(ghostVar (GF := GF) (γ.proto.outbox i to) (1 : Qp).half ([] : List Msg) ∗
        outboxFragB γ i to [])) (fun {k to} hk => by
      obtain ⟨rfl, hk'⟩ := range_getElem?_eq hk
      show _ ⊢ iprop(ghostVar (GF := GF) (γ.proto.outbox i to) (1 : Qp).half ([] : List Msg) ∗
        outboxFragB γ i to [])
      iintro H
      ihave ⟨H1, H2⟩ := (ghostVar_split_half (GF := GF) _ (1 : Qp) ([] : List Msg)).1 $$ H
      rw [h2]
      isplitl [H1]
      · iexact H1
      iunfold outboxFragB
      rw [h2]
      iframe H2
      ipureintro; exact ⟨hi, hk'⟩) $$ Ho
  ihave ⟨Ho1, Ho2⟩ := BigSepL.bigSepL_sep_eqv.1 $$ Ho
  ihave ⟨Hp1, Hp2⟩ := (ghostVar_split_half (GF := GF) _ (1 : Qp) (none : Option Bcast)).1 $$ Hp
  ihave ⟨Hc1, Hc2⟩ := (ghostVar_split_half (GF := GF) _ (1 : Qp)
    (([] : List InstId), (0 : Nat))).1 $$ Hc
  isplitl [Hr1 Ho1 Hp1 Hc1 Hm]
  · iunfold sysAuthRepB
    isplitl [Hr1]
    · iexists [RState.init i]; rw [h1]; iframe Hr1; ipureintro; rfl
    isplitl [Ho1]
    · iapply BigSepL.bigSepL_mono ?_ $$ Ho1
      intro _ _ _; exact .rfl
    rw [show Sys.init.pending i = none from rfl, show Sys.init.execCur i = [] from rfl,
      show Sys.init.execIdx i = 0 from rfl, show Sys.init.proposeChan i = [] from rfl]
    isplitl [Hp1]; · rw [h3]; iexact Hp1
    isplitl [Hc1]; · rw [h4]; iexact Hc1
    iunfold chanAuthB
    iexists ∅, []
    rw [h5]
    iframe Hm
    ipureintro
    exact ⟨fun _ => rfl, List.nodup_nil, List.nil_subperm⟩
  isplitl [Hr2]
  · iunfold repFragB
    isplitr; · ipureintro; exact hi
    iexists [RState.init i]; rw [h1]; iframe Hr2
    ipureintro; exact ⟨rfl, fun σ0 h q => by simp at h; subst h; exact Int.le_refl _⟩
  iunfold repIdleB
  iframe Ho2
  isplitl [Hp2]
  · iunfold pendFragB; isplitr; · ipureintro; exact hi
    rw [h3]; iexact Hp2
  · iunfold curFragB; isplitr; · ipureintro; exact hi
    rw [h4]; iexact Hc2

theorem sys_allocB :
    ⊢ |==> ∃ pn : ProtoNames, ∀ γ : EpNames, ⌜γ.proto = pn⌝ -∗
      sysAuthB (GF := GF) γ Sys.init ∗
      ([∗list] i ∈ List.range nR, repFragB γ i (RState.init i) ∗ repIdleB γ i) := by
  imod allocFun (0, fun _ => 0, 0, 0, 0) repRaw repRaw_alloc (List.range nR) List.nodup_range
    with ⟨%g, H⟩
  imodintro
  iexists ⟨fun i => (g i).1, fun i to => (g i).2.1 to, fun i => (g i).2.2.1,
    fun i => (g i).2.2.2.1, fun i => (g i).2.2.2.2⟩
  iintro %γ %hγ
  ihave H := BigSepL.bigSepL_mono (Ψ := fun _ i =>
      iprop(sysAuthRepB γ Sys.init i ∗ (repFragB γ i (RState.init i) ∗ repIdleB γ i)))
    (fun {k i} hk => by
      obtain ⟨rfl, hk'⟩ := range_getElem?_eq hk
      exact repRaw_split γ i hk' (g i) (by rw [hγ]; exact ⟨rfl, fun _ => rfl, rfl, rfl, rfl⟩)) $$ H
  ihave ⟨H1, H2⟩ := BigSepL.bigSepL_sep_eqv.1 $$ H
  iframe H2
  iunfold sysAuthB
  iexact H1

theorem Sys_init_kv : Sys.init.kv = (kvScan w8).init := by
  funext k; simp [Sys.kv, Sys.init, Sys.lastPut, kvScan]

theorem epInv_initB (γ : EpNames) :
    sysAuthB (GF := GF) γ Sys.init -∗ kvHalf γ (kvScan w8).init -∗ firedAuth γ ∅ -∗
      ([∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
        if fr = to then iprop(True) else sentHalf γ fr to []) -∗
      epInvB γ := by
  iintro Ha Hkv HF Hs
  iunfold epInvB
  iexists Sys.init
  iframe Ha
  isplitr; · ipureintro; exact inv_init
  isplitr; · ipureintro; exact InvX_init
  rw [Sys_init_kv]
  iframe Hkv
  isplitl [HF]
  · iexists ∅
    iframe HF
    isplitr; · ipureintro; intro cid; rfl
    iapply BigSepM.bigSepM_empty.2; iempintro
  isplitl [Hs]
  · iapply BigSepL.bigSepL_mono ?_ $$ Hs
    intro _ fr _
    exact .rfl
  rw [show Sys.init.delivered = [] from rfl, show Sys.init.ops = [] from rfl]
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  · iapply BigSepL.bigSepL_nil.2; iempintro

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
