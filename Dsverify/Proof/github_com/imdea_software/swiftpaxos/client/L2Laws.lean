/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/L2Laws.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2's laws over `sp.inv`'s part `sp.l2Inv` (notes/prove-s2-e.md): the registration of a node's
prediction (`pred_register`, the claim's `sp.inv` step), a client's invocation (`l2_invoke`) and
acceptance (`l2_accept`) at their last word's resolution (the node's half of its future words
`γ.pred` loses the event's words, which `sp.inv`'s half agrees are its head).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.LinHelp
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.LinCut
import all Spec.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-! ## Pure helpers -/

theorem cfgPNodes_cl {N k : Nat} (hk : k < 6) : PNode.cl k ∈ cfgPNodes N := by
  unfold cfgPNodes; simp [hk]

theorem cfgPNodes_rep {N k : Nat} (hk : k < N) : PNode.rep k ∈ cfgPNodes N := by
  unfold cfgPNodes; simp [hk]

/-- The predictions do not change when a node outside the configuration registers. -/
theorem predsOf_insert {N : Nat} {mW : GMap PNode (List w64)} {l : List GoString} {n : PNode}
    {W : List w64} (hreg : ∀ m ∈ cfgPNodes N, (mW.lookup m).isSome)
    (hn : mW.lookup n = none) (hl : ∀ r k, r < N → nodeOf l r = some k → k < N) :
    predsOf N (mW.insert n W) l = predsOf N mW l := by
  have hne : ∀ m ∈ cfgPNodes N, n ≠ m := by
    intro m hm e; subst e; have := hreg n hm; rw [hn] at this; cases this
  funext d
  cases d with
  | cl k =>
    simp only [predsOf]
    by_cases hk : k < 6
    · rw [if_pos hk, if_pos hk, GMap.lookup_insert_ne _ _ (hne _ (cfgPNodes_cl hk))]
    · rw [if_neg hk, if_neg hk]
  | rep r =>
    simp only [predsOf]
    by_cases hr : r < N
    · rw [if_pos hr, if_pos hr]
      cases h : nodeOf l r with
      | none => rfl
      | some k =>
        simp only
        rw [GMap.lookup_insert_ne _ _ (hne _ (cfgPNodes_rep (hl r k hr h)))]
    · rw [if_neg hr, if_neg hr]


theorem slotOk_invoke {sh : SHist} {mSl : GMap CmdId (Cmd × GName)} {x : CmdId} {c : Cmd}
    {S : PState} {γΨ : GName} (hS : SlotOk sh mSl) (hf : ∀ c', Ev.inv x c' ∉ SHist.hist sh)
    (hnr : ∀ v, Ev.resp x v ∉ SHist.hist sh) :
    SlotOk (sh ++ [(Ev.inv x c, S)]) (mSl.insert x (c, γΨ)) := by
  have hxS : mSl.lookup x = none := by
    cases h : mSl.lookup x with
    | none => rfl
    | some cg => exact absurd (hS.1 x cg h).1 (hf _)
  rw [SlotOk, SHist.hist_snoc]
  refine ⟨fun y cg h => ?_, fun y c' h hr => ?_⟩
  · rw [GMap.lookup_insert_eq_iff] at h
    by_cases e : x = y
    · subst e; rw [if_pos rfl] at h; cases h
      refine ⟨by simp, fun v hv => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | hv
      · exact hnr v hv
      · cases hv
    · rw [if_neg e] at h
      obtain ⟨h1, h2⟩ := hS.1 y cg h
      refine ⟨List.mem_append_left _ h1, fun v hv => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | hv
      · exact h2 v hv
      · cases hv
  · simp only [List.mem_append, List.mem_singleton, Ev.inv.injEq] at h
    rw [GMap.lookup_insert_eq_iff]
    rcases h with h | ⟨rfl, rfl⟩
    · have e : x ≠ y := fun e => hf c' (e ▸ h)
      rw [if_neg e]
      exact hS.2 y c' h (fun v hv => hr v (List.mem_append_left _ hv))
    · exact ⟨γΨ, by simp⟩

theorem slotOk_accept {sh : SHist} {mSl : GMap CmdId (Cmd × GName)} {x : CmdId} {v : List w8}
    {S : PState} {cg : Cmd × GName} (hS : SlotOk sh mSl) (hx : mSl.lookup x = some cg) :
    SlotOk (sh ++ [(Ev.resp x v, S)]) (mSl.delete x) := by
  rw [SlotOk, SHist.hist_snoc]
  have hlk : ∀ y, (mSl.delete x).lookup y = if x = y then none else mSl.lookup y := fun y => by
    simp [GMap.lookup_delete_iff]
  refine ⟨fun y cg' h => ?_, fun y c' h hr => ?_⟩
  · rw [hlk] at h
    by_cases e : x = y
    · rw [if_pos e] at h; cases h
    · rw [if_neg e] at h
      obtain ⟨h1, h2⟩ := hS.1 y cg' h
      refine ⟨List.mem_append_left _ h1, fun w hw => ?_⟩
      simp only [List.mem_append, List.mem_singleton, Ev.resp.injEq] at hw
      rcases hw with hw | ⟨rfl, -⟩
      · exact h2 w hw
      · exact e rfl
  · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
    rw [hlk]
    by_cases e : x = y
    · subst e; exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) (hr v)
    · rw [if_neg e]
      exact hS.2 y c' h (fun w hw => hr w (List.mem_append_left _ hw))

theorem predsOf_head {N : Nat} {mW : GMap PNode (List w64)} {l : List GoString} {k : Nat}
    {e : PEv} {W' : List w64} (hk : k < 6) (hW : mW.lookup (PNode.cl k) = some (encP e ++ W'))
    (he : PEvWf e) : predsOf N mW l (.cl k) = e :: decodeP W' := by
  simp only [predsOf, if_pos hk, hW, Option.getD_some]
  exact decodeP_enc he W'

theorem predsOf_upd {N : Nat} {mW : GMap PNode (List w64)} {l : List GoString} {k : Nat}
    {W' : List w64} (hk : k < 6) :
    Cut.upd (predsOf N mW l) (.cl k) (decodeP W') = predsOf N (mW.insert (PNode.cl k) W') l := by
  funext d
  unfold Cut.upd
  cases d with
  | cl k' =>
    by_cases e : k' = k
    · subst e; simp [predsOf, hk]
    · have e' : PNode.cl k ≠ PNode.cl k' := fun h => e (by cases h; rfl)
      simp only [Nd.cl.injEq, e, if_false, predsOf]
      rw [GMap.lookup_insert_ne _ _ e']
  | rep r =>
    simp only [reduceCtorEq, if_false, predsOf]
    split
    · cases h : nodeOf l r with
      | none => rfl
      | some k'' =>
        simp only
        rw [GMap.lookup_insert_ne _ _ (by simp)]
    · rfl

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
variable {γ : Names} {γc γm γl : GName}

attribute [local instance] cfg_timeless_acc

/-- **The membership is the configured replica nodes** (REQUEST R-E2, D90: `cfg` carries it,
`cfg_nodeOf`; the master supplies it, Proof/master/Defs.lean's `master.regOk_nodeOf`). -/
theorem cfg_members (N : Nat) (fr : Bool) (l : List GoString) :
    cfg γc γm N fr l ⊢ ⌜∀ r k, r < N → nodeOf l r = some k → k < N⌝ := by
  iintro #H
  ihave %Hm := cfg_nodeOf N fr l $$ H
  ipureintro; exact fun r k _ h => Hm r k h

/-- **A node registers its prediction** (the claim's `sp.inv` step; `client.claimGhost.spec`):
with its registration token, once, with its future words `W` (its ghost's prophecy's): `n` is
registered (`predReg`) and the node gets its half of `W`. -/
theorem pred_register (E : CoPset) (hE : ↑spN ⊆ E) (n : PNode) (W : List w64) :
    inv γ γc γm γl ∗ predTok γ n ⊢
      |={E}=> predReg γ n ∗ ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W := by
  unfold inv
  iintro ⟨#Hinv, Ht⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, HRepr, Hnodes, Hproto, HQs, HCl, HDom, Hcmds, Hconns, HNu⟩
  unfold l2Inv
  icases Hown with ⟨%mG, %mW, %mRg, %G, %mSl, >HG, >%HmG, >HGs, >HRg, >HW, >%HRgW, >HWs, HH2, Hlin, HSl, HSls, Hph⟩
  unfold predTok
  ihave %HlkG := ghost_map_lookup $$ HG Ht
  cases hW : mW.lookup n with
  | some W0 =>
    ihave Hn := BigSepM.bigSepM_lookup (show Iris.Std.PartialMap.get? mW n = some W0 from hW) $$ HWs
    icases Hn with ⟨Hn1, -, -⟩
    ihave Hn2 := BigSepM.bigSepM_lookup (show Iris.Std.PartialMap.get? mG n = some () from HlkG) $$ HGs
    ihave ⟨Hn12, -⟩ := ghostMapElem_combine n γ.preg _ _ () () $$ Hn1 Hn2
    ihave %Hv := ghostMapElem_valid_2 n γ.preg _ _ () () $$ Hn12 Ht
    exfalso
    rw [← dfrac_own_half_half] at Hv
    exact dfrac_own_one_op_invalid _ Hv.1
  | none =>
    have hRg : mRg.lookup n = none := by rw [HRgW, hW]; rfl
    imod ghost_map_insert n W hW $$ HW with ⟨HW, HWn⟩
    icases (ghostMapElem_halves γ.pred n W).1 $$ HWn with ⟨HWn1, HWn2⟩
    imod ghost_map_insert_persist n () hRg $$ HRg with ⟨HRg, #Hreg⟩
    ihave HWs := (BigSepM.bigSepM_insert (Φ := fun n W => iprop(ghostMapElem γ.preg n (DFrac.own (1 : Qp).half) () ∗
        ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W ∗ predReg γ n))
      (show Iris.Std.PartialMap.get? mW n = none from hW)).2 $$ [Ht HWn1 HWs]
    · iframe Ht HWn1 HWs
      unfold predReg; iexact Hreg
    -- the phase: unchanged (a registered configuration's predictions are unchanged)
    ihave Hph : ▷ (⌜sh = [] ∧ G = [] ∧ mSl = ∅⌝ ∨
      ∃ c : Conf, confIs γc c ∗
        ⌜(∀ m ∈ cfgPNodes c.n, ((mW.insert n W).lookup m).isSome) ∧ SlotOk sh mSl⌝ ∗
        (⌜S.empty ∧ G = [] ∧ ∀ x v, Ev.resp x v ∉ SHist.hist sh⌝ ∨
          ∃ (fr : Bool) (l : List GoString), cfg γc γm c.n fr l ∗
            ⌜StratOk c.n fr (l2Nodes c.n) S sh (predsOf c.n (mW.insert n W) l) G⌝)) $$ [Hph]
    · inext
      icases Hph with (%H | ⟨%c, #Hc, %H, (%H2 | ⟨%fr, %l, #Hcfg, %H2⟩)⟩)
      · ileft; ipureintro; exact H
      · iright; iexists c; iframe Hc
        isplitr
        · ipureintro
          refine ⟨fun m hm => ?_, H.2⟩
          rw [GMap.lookup_insert_eq_iff]; split
          · rfl
          · exact H.1 m hm
        · ileft; ipureintro; exact H2
      · iright; iexists c; iframe Hc
        ihave %Hmem := cfg_members c.n fr l $$ Hcfg
        isplitr
        · ipureintro
          refine ⟨fun m hm => ?_, H.2⟩
          rw [GMap.lookup_insert_eq_iff]; split
          · rfl
          · exact H.1 m hm
        · iright; iexists fr, l; iframe Hcfg
          ipureintro
          rw [predsOf_insert H.1 hW Hmem]; exact H2
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HG HGs HRg HW HWs HH2 Hlin HSl HSls Hph HQ HK HPa HRepr Hnodes Hproto HQs HCl HDom Hcmds Hconns HNu] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe HC HL HS HA HP HCo HRp HN HH HD HQ HK HPa HRepr Hnodes Hproto HQs HCl HDom Hcmds Hconns HNu
      iexists mG, mW.insert n W, mRg.insert n (), G, mSl
      iframe
      ipureintro
      refine ⟨HmG, fun m => ?_⟩
      rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff, HRgW]
      split <;> rfl
    imodintro
    iframe HWn2
    unfold predReg; iexact Hreg

/-- A tracked client's index (`clOf`) is below 6. -/
theorem clOf_lt {x : CmdId} (h1 : 1 ≤ x.cl.toInt) (h2 : x.cl.toInt ≤ 6) : clOf x < 6 := by
  unfold clOf
  have h := BitVec.toInt_eq_toNat_cond x.cl
  split at h <;> omega

/-- The registered nodes of a list of `predReg`s. -/
theorem regs_lookup {A : Type} (f : A → PNode) (mRg : GMap PNode Unit) :
    ∀ l : List A, ghostMapAuth γ.regd 1 mRg ∗ ([∗list] a ∈ l, predReg γ (f a)) ⊢
      ghostMapAuth γ.regd 1 mRg ∗ ⌜∀ a ∈ l, mRg.lookup (f a) = some ()⌝
  | [] => by
    iintro ⟨H, -⟩; iframe H; ipureintro; simp
  | a :: l => by
    iintro ⟨H, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Ha, Hl⟩
    unfold predReg
    ihave %Hla := ghost_map_lookup $$ H Ha
    icases regs_lookup f mRg l $$ [H Hl] with ⟨H, %Hl⟩
    · iframe H; unfold predReg; iexact Hl
    iframe H
    ipureintro
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Hla
    · exact Hl b hb

/-- `allPredsReg`'s nodes are registered. -/
theorem allPredsReg_lookup (mRg : GMap PNode Unit) :
    ghostMapAuth γ.regd 1 mRg ∗ allPredsReg γ γc ⊢
      ghostMapAuth γ.regd 1 mRg ∗ ∃ c : Conf, confIs γc c ∗
        ⌜∀ n ∈ cfgPNodes c.n, mRg.lookup n = some ()⌝ := by
  unfold allPredsReg
  iintro ⟨H, %c, #Hc, Hr, Hcl⟩
  icases regs_lookup PNode.rep mRg (List.range c.n) $$ [H Hr] with ⟨H, %H1⟩
  · iframe
  icases regs_lookup PNode.cl mRg (List.range 6) $$ [H Hcl] with ⟨H, %H2⟩
  · iframe
  iframe H
  iexists c
  iframe Hc
  ipureintro
  intro n hn
  unfold cfgPNodes at hn
  simp only [List.mem_append, List.mem_map] at hn
  rcases hn with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact H2 a ha
  · exact H1 a ha

/-- **A client's invocation** (L2; `Ghost.Invoke`'s last resolution): client `x.cl` (predicted
node `cl (clOf x)`), whose node's future words start with the invocation's, invokes its next
command `x` (`c`, a put or a get) with its atomic update (its continuation's saved predicate
`γΨ`): `x` is registered, the update deposited in `x`'s slot (the client's ticket `pend`), the
node's future words lose the invocation's. -/
theorem l2_invoke (E : CoPset) (hE : ↑spN ⊆ E) (x : CmdId) (c : Cmd)
    (Ψ : List w8 → IProp netDistGF) (γΨ : GName) (W' : List w64) :
    ⌜x.cl.toInt ≥ 1 ∧ (c.isPut ∨ c.isGet) ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
      x.seq.toNat < 2 ^ 25⌝ ∗
    inv γ γc γm γl ∗ allPredsReg γ γc ∗ clientSeq γ x.cl x.seq.toNat ∗ cmdAU γl c Ψ ∗
    savedPredOwn γΨ .discard Ψ ∗
    ghostMapElem γ.pred (PNode.cl (clOf x)) (DFrac.own (1 : Qp).half) (encP (.inv x c) ++ W') ⊢
    |={E}=> cmdIs γ x c ∗ clientSeq γ x.cl (x.seq.toNat + 1) ∗ pend γ x Ψ ∗
      ghostMapElem γ.pred (PNode.cl (clOf x)) (DFrac.own (1 : Qp).half) W' := by
  unfold inv clientSeq
  iintro ⟨%Hpre, #Hinv, #Hreg, Hs, HAU, #HΨ, Hw⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, >HH, HD, Hown, >HQ, HK, HPa, >%Hrepr, Hnodes, #Hproto, >HQs, >%Hcl, >%Hdom, Hcmds, Hconns, HNu⟩
  unfold l2Inv
  icases Hown with ⟨%mG, %mW, %mRg, %G, %mSl, HG, HmG, HGs, >HRg, >HW, >%HRgW, >HWs, >HH2, >Hlin, >HSl, HSls, #Hph⟩
  ihave %HlkQ := ghost_map_lookup $$ HQ Hs
  have hk6 : clOf x < 6 := clOf_lt (Hdom.2 x.cl _ HlkQ).1 (Hdom.2 x.cl _ HlkQ).2
  -- the client's command is new
  have hxC : mC.lookup x = none := by
    cases h : mC.lookup x with
    | none => rfl
    | some c' =>
      obtain ⟨⟨n, hn, hlt⟩, -⟩ := Hcl x c' h
      rw [HlkQ] at hn; cases hn; omega
  have hxS : S.cmds x = none := by rw [← Hrepr.cmds x]; exact hxC
  have hfresh : ∀ c', Ev.inv x c' ∉ SHist.hist sh := fun c' h => by
    rw [Hdom.1 x c' h] at hxC; cases hxC
  have hnew : ∀ c' S', (Ev.inv x c', S') ∉ sh := fun c' S' h =>
    hfresh c' (SHist.mem_hist.mpr ⟨S', h⟩)
  have hpg : c.isPut = true ∨ c.isGet = true := by
    rcases Hpre.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hwf : PEvWf (.inv x c) := by
    refine ⟨?_, by unfold CmdWf; have := Hpre.2.2.1; omega⟩
    rcases hpg with h | h
    · left; simpa [Cmd.isPut] using h
    · right; simpa [Cmd.isGet] using h
  -- the history's facts (before the invocation)
  ihave Hnr : ▷ ⌜∀ v, Ev.resp x v ∉ SHist.hist sh⌝ $$ [Hproto]
  · inext
    icases Hproto with (%H | ⟨%N, %fr, %l, -, %H⟩)
    · ipureintro; exact fun v hv => empty_no_resp H.1 H.2.2.1 x v hv
    · ipureintro
      intro v hv
      obtain ⟨S', hm⟩ := SHist.mem_hist.mp hv
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      obtain ⟨j, c', S'', -, hj⟩ := H.2.2.2.1.resp_inv i x v S' hi
      exact hnew c' S'' (List.mem_of_getElem? hj)
  icases Hnr with >%Hnr
  -- the node's future words: both halves to `W'`
  ihave %HlkW := ghost_map_lookup $$ HW Hw
  icases (BigSepM.bigSepM_insert_acc
    (show Iris.Std.PartialMap.get? mW (PNode.cl (clOf x)) = some (encP (.inv x c) ++ W') from HlkW))
    $$ HWs with ⟨⟨Ht, Hw2, #Hr⟩, HWs⟩
  ihave Hwf := (ghostMapElem_halves γ.pred (PNode.cl (clOf x)) (encP (.inv x c) ++ W')).2 $$ [Hw Hw2]
  · isplitl [Hw]
    · iexact Hw
    · iexact Hw2
  imod ghost_map_update W' $$ HW Hwf with ⟨HW, Hwf⟩
  icases (ghostMapElem_halves γ.pred (PNode.cl (clOf x)) W').1 $$ Hwf with ⟨Hw, Hw2⟩
  ihave HWs := HWs $$ %W' [Ht Hw2]
  · iframe Ht Hw2 Hr
  -- the registrations
  icases allPredsReg_lookup mRg $$ [HRg Hreg] with ⟨HRg, %cf, #Hcf, %Hcfr⟩
  · iframe HRg Hreg
  have hreg' : ∀ n ∈ cfgPNodes cf.n, ((mW.insert (PNode.cl (clOf x)) W').lookup n).isSome := by
    intro n hn
    rw [GMap.lookup_insert_eq_iff]; split
    · rfl
    · have := Hcfr n hn; rw [HRgW] at this
      cases h : mW.lookup n with
      | none => rw [h] at this; cases this
      | some _ => rfl
  -- the slot
  ihave HxSl : ▷ ⌜mSl.lookup x = none⌝ $$ []
  · inext
    icases Hph with (%H | ⟨%c0, -, %H, -⟩)
    · ipureintro; rw [H.2.2]; rfl
    · ipureintro
      cases h : mSl.lookup x with
      | none => rfl
      | some cg => exact absurd (H.2.1 x cg h).1 (hfresh _)
  icases HxSl with >%HxSl
  ihave HxG : ▷ ⌜x ∉ G.map Prod.fst⌝ $$ []
  · inext
    icases Hph with (%H | ⟨%c0, -, -, (%H | ⟨%fr, %l, -, %H⟩)⟩)
    · ipureintro; rw [H.2.1]; simp
    · ipureintro; rw [H.2.1]; simp
    · ipureintro
      intro hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact hfresh _ (H.invG p hp)
  icases HxG with >%HxG
  imod ghost_map_insert x (c, γΨ) HxSl $$ HSl with ⟨HSl, Hx⟩
  ihave HSls : ▷ ([∗map] y ↦ cg ∈ mSl.insert x (c, γΨ), slotL γl G y cg) $$ [HSls HAU]
  · inext
    iapply (BigSepM.bigSepM_insert (Φ := fun y cg => slotL γl G y cg) (i := x) (x := (c, γΨ))
      (show Iris.Std.PartialMap.get? mSl x = none from HxSl)).2
    iframe HSls
    unfold slotL
    iexists Ψ
    iframe HΨ
    ileft
    iframe HAU
    ipureintro; exact HxG
  -- the new phase
  have hhd := predsOf_head (N := cf.n) (l := []) hk6 HlkW hwf
  ihave Hph' : ▷ (∃ cc : Conf, confIs γc cc ∗
        ⌜(∀ n ∈ cfgPNodes cc.n, ((mW.insert (PNode.cl (clOf x)) W').lookup n).isSome) ∧
          SlotOk (sh ++ [(Ev.inv x c, S)]) (mSl.insert x (c, γΨ))⌝ ∗
        (⌜(S.register x c).empty ∧ G = [] ∧
            ∀ y v, Ev.resp y v ∉ SHist.hist (sh ++ [(Ev.inv x c, S)])⌝ ∨
          ∃ (fr : Bool) (l : List GoString), cfg γc γm cc.n fr l ∗
            ⌜StratOk cc.n fr (l2Nodes cc.n) (S.register x c) (sh ++ [(Ev.inv x c, S)])
              (predsOf cc.n (mW.insert (PNode.cl (clOf x)) W') l) G⌝)) $$ []
  · have hn : Nd.cl (clOf x) ∈ l2Nodes cf.n := by unfold l2Nodes; simp [hk6]
    have hok : ∀ N, okE N S (.cl (clOf x)) (.inv x c) := fun N => ⟨hxS, rfl, hpg⟩
    have hemp : S.empty → (S.register x c).empty := fun h => by
      simpa [PState.empty, PState.register] using h
    have hnr' : (∀ y v, Ev.resp y v ∉ SHist.hist sh) →
        ∀ y v, Ev.resp y v ∉ SHist.hist (sh ++ [(Ev.inv x c, S)]) := by
      intro h y v hy
      rw [SHist.hist_snoc] at hy
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hy
      exact h y v hy
    inext
    iexists cf
    iframe Hcf
    icases Hph with (%Ha | ⟨%c0, #Hc0, %Hb, (%Hb1 | ⟨%fr0, %l0, #Hcfg0, %Hb2⟩)⟩)
    · obtain ⟨rfl, rfl, rfl⟩ := Ha
      isplitr
      · ipureintro
        exact ⟨hreg', slotOk_invoke ⟨fun y cg h => by simp at h, fun y c' h => by
          simp [SHist.hist] at h⟩ hfresh Hnr⟩
      icases Hproto with (%H | ⟨%N, %fr, %l, #Hcfg, %H⟩)
      · ileft; ipureintro
        exact ⟨hemp H.1, rfl, hnr' (fun y v h => by simp [SHist.hist] at h)⟩
      · ihave %Hcc := cfg_conf N fr l cf $$ [Hcfg Hcf]
        · iframe Hcfg Hcf
        obtain ⟨hN, -⟩ := Hcc
        subst hN
        iright; iexists fr, l; iframe Hcfg
        ipureintro
        have h0 : StratOk cf.n fr (l2Nodes cf.n) S [] (predsOf cf.n mW l) [] :=
          StratOk.init H.1 (fun y => by
            cases h : S.cmds y with
            | none => rfl
            | some c' => exact absurd (H.2.2.2.1.reg y c' h) (by simp [SHist.hist]))
        have := StratOk.inv h0 hn (predsOf_head hk6 HlkW hwf) (hok _)
        rw [predsOf_upd hk6] at this
        simpa using this
    · ihave %Hcc := confIs_agree γc c0 cf $$ [Hc0 Hcf]
      · iframe Hc0 Hcf
      subst Hcc
      isplitr
      · ipureintro; exact ⟨hreg', slotOk_invoke Hb.2 hfresh Hnr⟩
      ileft; ipureintro
      exact ⟨hemp Hb1.1, Hb1.2.1, hnr' Hb1.2.2⟩
    · ihave %Hcc := confIs_agree γc c0 cf $$ [Hc0 Hcf]
      · iframe Hc0 Hcf
      subst Hcc
      isplitr
      · ipureintro; exact ⟨hreg', slotOk_invoke Hb.2 hfresh Hnr⟩
      iright; iexists fr0, l0; iframe Hcfg0
      ipureintro
      have := StratOk.inv Hb2 hn (predsOf_head hk6 HlkW hwf) (hok _)
      rw [predsOf_upd hk6] at this
      exact this
  -- the protocol disjunct (stage 1's `proto_invoke`)
  icases (BI.later_mono (proto_invoke (γc := γc) (γm := γm) S mN mD sh x c hxS hnew hpg)) $$ Hproto
    with ⟨Hproto, -⟩
  -- the client's sequence number: both halves, updated
  icases (BigSepM.bigSepM_insert_acc
    (show Iris.Std.PartialMap.get? mQ x.cl = some x.seq.toNat from HlkQ)) $$ HQs with ⟨Hs2, HQs⟩
  ihave Hfull := (ghostMapElem_halves γ.seqs x.cl x.seq.toNat).2 $$ [Hs Hs2]
  · isplitl [Hs]
    · iexact Hs
    · iexact Hs2
  imod ghost_map_update (x.seq.toNat + 1) $$ HQ Hfull with ⟨HQ, Hfull⟩
  icases (ghostMapElem_halves γ.seqs x.cl (x.seq.toNat + 1)).1 $$ Hfull with ⟨Hs, Hs2⟩
  ihave HQs := HQs $$ %(x.seq.toNat + 1) Hs2
  -- the history: both halves, appended
  ihave HHf := (monoList_halves γ.hist (SHist.hist sh)).2 $$ [HH HH2]
  · isplitl [HH]
    · iexact HH
    · iexact HH2
  imod monoListAuthOwn_update_app [Ev.inv x c] $$ HHf with ⟨HHf, -⟩
  icases (monoList_halves γ.hist (SHist.hist sh ++ [Ev.inv x c])).1 $$ HHf with ⟨HH, HH2⟩
  -- the registration
  imod ghost_map_insert_persist x c hxC $$ HC with ⟨HC, #Hc⟩
  have hh : SHist.hist (sh ++ [(Ev.inv x c, S)]) = SHist.hist sh ++ [Ev.inv x c] := by
    simp [SHist.hist]
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls Hph' HQ HK HPa Hnodes Hproto HQs Hcmds Hconns HNu] with -
  · inext
    iexists S.register x c, mC.insert x c, mL, mS, mA, mP, mCo, mR, mN,
      sh ++ [(Ev.inv x c, S)], mD, mQ.insert x.cl (x.seq.toNat + 1), mK, mPa
    rw [hh]
    iframe HL HS HA HP HCo HRp HN HH HD HQ HK HPa Hnodes Hproto HQs Hconns HC
    rw [show (S.register x c).loc = S.loc from rfl]
    iframe HNu
    isplitl [HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls Hph']
    · iexists mG, mW.insert (PNode.cl (clOf x)) W', mRg, G, mSl.insert x (c, γΨ)
      iframe HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls
      isplitr
      · ipureintro
        intro n
        rw [HRgW, GMap.lookup_insert_eq_iff]
        split
        · next e => subst e; rw [HlkW]; rfl
        · rfl
      iright; iexact Hph'
    isplitr
    · ipureintro
      refine ⟨fun y => ?_, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, Hrepr.com,
        Hrepr.rep⟩
      rw [GMap.lookup_insert_eq_iff]
      by_cases hy : x = y
      · subst hy; simp [PState.register]
      · simp [PState.register, hy, Ne.symm hy, Hrepr.cmds y]
    isplitr
    · ipureintro
      intro y c' h
      rw [GMap.lookup_insert_eq_iff] at h
      by_cases hy : x = y
      · subst hy
        rw [if_pos rfl] at h
        cases h
        exact ⟨⟨x.seq.toNat + 1, GMap.lookup_insert _ _ _, by omega⟩, Hpre.2.1, Hpre.1,
          Hpre.2.2.1, Hpre.2.2.2.1, Hpre.2.2.2.2⟩
      · rw [if_neg hy] at h
        obtain ⟨⟨n, hn, hlt⟩, rest⟩ := Hcl y c' h
        refine ⟨?_, rest⟩
        by_cases hcl : x.cl = y.cl
        · rw [← hcl, HlkQ] at hn
          cases hn
          exact ⟨x.seq.toNat + 1, by rw [← hcl]; exact GMap.lookup_insert _ _ _, by omega⟩
        · exact ⟨n, by rw [GMap.lookup_insert_ne _ _ hcl]; exact hn, hlt⟩
    isplitr
    · ipureintro
      refine ⟨fun y c' hy => ?_, fun cl n h => ?_⟩
      · rw [List.mem_append] at hy
        rcases hy with hy | hy
        · have := Hdom.1 y c' hy
          have hne : x ≠ y := fun e => by subst e; rw [hxC] at this; cases this
          rw [GMap.lookup_insert_ne _ _ hne]; exact this
        · simp at hy; obtain ⟨rfl, rfl⟩ := hy; exact GMap.lookup_insert _ _ _
      · by_cases hcl : x.cl = cl
        · subst hcl; exact Hdom.2 x.cl _ HlkQ
        · rw [GMap.lookup_insert_ne _ _ hcl] at h; exact Hdom.2 cl n h
    iapply (BigSepM.bigSepM_insert (show Iris.Std.PartialMap.get? mC x = none from hxC)).2
    isplitr
    · unfold cmdIs; iexact Hc
    · iexact Hcmds
  imodintro
  unfold cmdIs pend
  iframe Hc Hs Hw
  iexists c, γΨ
  iframe Hx HΨ

/-- **A client's acceptance** (L2; `Ghost.Accept`'s last resolution; mask `⊤`: the commits run
other clients' updates): client `x.cl`, whose node's future words start with the acceptance's,
accepts `x` with its decided result `v` (`doneRes`); the strategy commits the linearization up
to `x` (`StratOk.resp`, each commit from its slot), and the client's ticket gives its
continuation applied to `v`. -/
theorem l2_accept (x : CmdId) (v : List w8) (Ψ : List w8 → IProp netDistGF) (W' : List w64)
    (hv : v.length < 2 ^ 64) :
    inv γ γc γm γl ∗ doneRes γ x v ∗ pend γ x Ψ ∗ £ 1 ∗
    ghostMapElem γ.pred (PNode.cl (clOf x)) (DFrac.own (1 : Qp).half) (encP (.resp x v) ++ W') ⊢
    |={⊤}=> ▷ Ψ v ∗ ghostMapElem γ.pred (PNode.cl (clOf x)) (DFrac.own (1 : Qp).half) W' := by
  unfold inv doneRes pend
  iintro ⟨#Hinv, #Hd, ⟨%c, %γΨ, Hx, #HΨ⟩, Hlc, Hw⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, >HH, ⟨>HD, HDs⟩, Hown, HQ, HK, HPa, HRepr, Hnodes, Hproto, HQs, >%Hcl, >%Hdom, Hcmds, Hconns, HNu⟩
  unfold l2Inv
  icases Hown with ⟨%mG, %mW, %mRg, %G, %mSl, HG, HmG, HGs, HRg, >HW, >%HRgW, >HWs, >HH2, >Hlin, >HSl, HSls, #Hph⟩
  ihave %HlkD := ghost_map_lookup $$ HD Hd
  ihave %HlkSl := ghost_map_lookup $$ HSl Hx
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, >#Hcfg, >%Hp⟩)
  · exfalso; rw [Hemp.2.2.2 x] at HlkD; cases HlkD
  obtain ⟨hI, hN, hR, hH, hDok⟩ := Hp
  obtain ⟨b, hpc, hres⟩ := hDok x v HlkD
  have hH' := HistOk_resp hH hI hpc hres
  -- the phase: a configured strategy
  ihave Hph2 : ▷ ⌜∃ (cc : Conf) (fr0 : Bool) (l0 : List GoString),
      (∀ n ∈ cfgPNodes cc.n, (mW.lookup n).isSome) ∧ SlotOk sh mSl ∧ cc.n = N ∧ fr0 = fr ∧ l0 = l ∧
      StratOk cc.n fr0 (l2Nodes cc.n) S sh (predsOf cc.n mW l0) G⌝ $$ []
  · inext
    icases Hph with (%Ha | ⟨%c0, #Hc0, %Hb, (%Hb1 | ⟨%fr0, %l0, #Hcfg0, %Hb2⟩)⟩)
    · exfalso; rw [Ha.2.2] at HlkSl; cases HlkSl
    · exfalso
      have := Hb1.1.1 (leaderOf N b) b
      have hx := hpc.1
      unfold PState.ord at hx
      rw [this] at hx; cases hx
    · ihave %Hag := cfg_agree (γc := γc) (γm := γm) c0.n N fr0 fr l0 l $$ [Hcfg0 Hcfg]
      · iframe Hcfg0 Hcfg
      ipureintro
      exact ⟨c0, fr0, l0, Hb.1, Hb.2, Hag.1, Hag.2.1, Hag.2.2, Hb2⟩
  icases Hph2 with >%Hph2
  obtain ⟨cc, fr0, l0, hreg, hslot, hN', hfr', hl', hS⟩ := Hph2
  subst hN' hfr' hl'
  have hk6 : clOf x < 6 := by
    obtain ⟨⟨n, hn, -⟩, -⟩ := Hcl x c (Hdom.1 x c (hslot.1 x _ HlkSl).1)
    exact clOf_lt (Hdom.2 x.cl n hn).1 (Hdom.2 x.cl n hn).2
  have hwf : PEvWf (.resp x v) := hv
  have hn : Nd.cl (clOf x) ∈ l2Nodes cc.n := by unfold l2Nodes; simp [hk6]
  -- the node's future words: both halves to `W'`
  ihave %HlkW := ghost_map_lookup $$ HW Hw
  obtain ⟨D, hS', hCm, hxD, hxv⟩ := StratOk.resp hS hn (predsOf_head hk6 HlkW hwf) hpc hres
  rw [predsOf_upd hk6] at hS'
  icases (BigSepM.bigSepM_insert_acc
    (show Iris.Std.PartialMap.get? mW (PNode.cl (clOf x)) = some (encP (.resp x v) ++ W') from HlkW))
    $$ HWs with ⟨⟨Ht, Hw2, #Hr⟩, HWs⟩
  ihave Hwf := (ghostMapElem_halves γ.pred (PNode.cl (clOf x)) (encP (.resp x v) ++ W')).2 $$ [Hw Hw2]
  · isplitl [Hw]
    · iexact Hw
    · iexact Hw2
  imod ghost_map_update W' $$ HW Hwf with ⟨HW, Hwf⟩
  icases (ghostMapElem_halves γ.pred (PNode.cl (clOf x)) W').1 $$ Hwf with ⟨Hw, Hw2⟩
  ihave HWs := HWs $$ %W' [Ht Hw2]
  · iframe Ht Hw2 Hr
  -- the commits
  have hDslot : ∀ p ∈ D, ∃ γ', mSl.lookup p.1 = some (p.2, γ') := fun p hp =>
    hslot.2 p.1 p.2 (hCm.invoked p hp) (hCm.pending p hp)
  have hDcmd : ∀ p ∈ D, p.2.isPut ∨ p.2.isGet := by
    intro p hp
    obtain ⟨S', hm⟩ := SHist.mem_hist.mp (hCm.invoked p hp)
    rcases hH.pg p.1 p.2 S' hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  imod lc_fupd_elim_later (E := ⊤ \ ↑spN) $$ Hlc HSls with HSls
  imod slots_commit γl mSl D G hDslot hCm.fresh hCm.nodup hDcmd $$ [HSls Hlin] with ⟨HSls, Hlin⟩
  · iframe
  ihave ⟨Hxs, HSls⟩ := (BigSepM.bigSepM_delete (Φ := fun y cg => slotL γl (G ++ D) y cg)
    (show Iris.Std.PartialMap.get? mSl x = some (c, γΨ) from HlkSl)).1 $$ HSls
  imod ghost_map_delete $$ HSl Hx with HSl
  iunfold slotL at Hxs
  icases Hxs with ⟨%Ψ', #HΨ', (⟨%hn, -⟩ | ⟨%_, HΨv⟩)⟩
  · exact absurd hxD hn
  ihave HΨv : Ψ' v $$ [HΨv]
  · rw [← hxv]; iexact HΨv
  ihave Hag := saved_pred_agree γΨ _ _ Ψ Ψ' v $$ HΨ HΨ'
  -- the history: both halves, appended
  ihave HHf := (monoList_halves γ.hist (SHist.hist sh)).2 $$ [HH HH2]
  · isplitl [HH]
    · iexact HH
    · iexact HH2
  imod monoListAuthOwn_update_app [Ev.resp x v] $$ HHf with ⟨HHf, -⟩
  icases (monoList_halves γ.hist (SHist.hist sh ++ [Ev.resp x v])).1 $$ HHf with ⟨HH, HH2⟩
  have hh : SHist.hist (sh ++ [(Ev.resp x v, S)]) = SHist.hist sh ++ [Ev.resp x v] := by
    simp [SHist.hist]
  ihave Hcf := cfg_confIs cc.n fr0 l0 $$ Hcfg
  icases Hcf with ⟨%c1, #Hc1, %Hc1n⟩
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HDs HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls HQ HK HPa HRepr Hnodes HQs Hcmds Hconns HNu] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh ++ [(Ev.resp x v, S)], mD, mQ, mK, mPa
    rw [hh]
    iframe HC HL HS HA HP HCo HRp HN HH HD HDs HQ HK HPa HRepr Hnodes HQs Hcmds Hconns HNu
    isplitl [HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls]
    · iexists mG, mW.insert (PNode.cl (clOf x)) W', mRg, G ++ D, mSl.delete x
      iframe HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls
      isplitr
      · ipureintro
        intro n
        rw [HRgW, GMap.lookup_insert_eq_iff]
        split
        · next e => subst e; rw [HlkW]; rfl
        · rfl
      iright
      iexists c1
      iframe Hc1
      rw [Hc1n.1]
      isplitr
      · ipureintro
        refine ⟨fun n hn => ?_, slotOk_accept hslot HlkSl⟩
        rw [GMap.lookup_insert_eq_iff]; split
        · rfl
        · exact hreg n hn
      iright
      iexists fr0, l0
      iframe Hcfg
      ipureintro
      exact hS'
    isplitr
    · iright
      iexists cc.n, fr0, l0
      iframe Hcfg
      ipureintro; exact ⟨hI, hN, hR, hH', hDok⟩
    ipureintro
    refine ⟨Hcl, fun y c' hy => ?_, Hdom.2⟩
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact Hdom.1 y c' hy
    · simp at hy
  imodintro
  iframe Hw
  inext
  iapply internal_eq_rewrite_wand $$ Hag HΨv

end laws

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
