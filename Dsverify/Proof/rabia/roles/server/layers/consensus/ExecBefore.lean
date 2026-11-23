/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecBefore.lean`, run `rabia-r1wake-1`.)

The executor's message builders and the messages sent before each wait (`getRequest`,
`genProposalMsg`, `genBinConMsg`, `genDecMsgType2`, `phase0Round1BeforeWait`, the state/vote
BeforeWaits), against `ExecDefs.lean`'s statements.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecDefs
public import Dsverify.Proof.rabia.internal.ledger.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-- Discharge the bounds check of an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

section basics
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

/-- (A missing law of `message`: unfolds `objRep`.) Setting a represented object's `SvrSeq`. -/
theorem cons_objRep_svrSeq (v : ConsensusObj) (o : ObjV) (s : w32) :
    objRep (GF := GF) v o ⊢ objRep { v with SvrSeq' := s } { o with svrSeq := s } := by
  unfold objRep
  iintro ⟨%h, H⟩
  iframe H
  ipureintro
  obtain ⟨h1, h2, _, h4⟩ := h
  simp [h1, h2, h4]

instance cons_histFacts_persistent (γ : Names) (k : Nat) (H : List (ObjV × DVal)) :
    Persistent (histFacts (GF := GF) γ k H) := by unfold histFacts; infer_instance

/-- Slot `n`'s fresh part out of the fresh slots from `n`. -/
theorem freshSlots_take (γl : SrvNames) (γc : ConsNames) (n : Nat) (e : SlotV)
    (he : γl.slots[n]? = some e) :
    freshSlots (GF := GF) γl γc n ⊢ slotExecPart γl γc n e ∗ freshSlots γl γc (n + 1) := by
  unfold freshSlots
  refine (BigSepL.bigSepL_mono (Ψ := fun s e => iprop(
      (if s = n then slotExecPart (GF := GF) γl γc s e else iprop(emp)) ∗
      (if n + 1 ≤ s then slotExecPart γl γc s e else iprop(emp)))) ?_).trans ?_
  · intro s x _
    by_cases h1 : s = n
    · subst h1; simp only [Nat.le_refl, ↓reduceIte, show ¬ s + 1 ≤ s by omega]
      iintro H; iframe H
    · by_cases h2 : n ≤ s
      · simp only [h2, h1, ↓reduceIte, show n + 1 ≤ s by omega]
        iintro H; iframe H
      · simp only [h2, h1, ↓reduceIte, show ¬ n + 1 ≤ s by omega]
        iintro H; iframe H
  · refine BigSepL.bigSepL_sep_eqv.1.trans ?_
    refine sep_mono ?_ .rfl
    refine (BigSepL.bigSepL_lookup (Φ := fun s e => iprop(if s = n then slotExecPart (GF := GF)
      γl γc s e else iprop(emp))) he).trans ?_
    simp

instance exb_bcastInv_timeless (γ : Names) (X : Nat) : Timeless (bcastInv (GF := GF) γ X) := by
  unfold bcastInv; infer_instance

/-- (Unfolds Ghost's `cfgIs`.) The recorded configuration is one `choose` picks. -/
theorem cfgIs_ok (γ : RabiaNames) (c : RCfg) : cfgIs (GF := GF) γ c ⊢ ⌜c.Ok⌝ := by
  unfold cfgIs; iintro ⟨-, %h⟩; ipureintro; exact h

theorem cfOk_maxS {c : RCfg} (hc : c.Ok) : c.n ≤ maxS := by
  unfold RCfg.Ok at hc; unfold maxS; omega

/-- Two pending objects (each with the receipt of its client request) are distinct objects. -/
theorem pendOk_ne (hc : cf.Ok) (γ : Names) (γl : SrvNames) (o o' : ObjV) :
    shared (GF := GF) γ ∗ pendOk γ cf γl o ∗ pendOk γ cf γl o' ⊢
      |={⊤}=> ⌜objId o ≠ objId o'⌝ ∗ pendOk γ cf γl o ∗ pendOk γ cf γl o' := by
  iintro ⟨#Hsh, Ho, Ho'⟩
  by_cases hid : objId o = objId o'
  · unfold pendOk
    icases Ho with ⟨#Hoo, %X, %j, %l, #Hl, Hr, %hX, %m, %hl, %hmt, %hmo⟩
    icases Ho' with ⟨-, %X', %j', %l', #Hl', Hr', %hX', %m', %hl', %hmt', %hmo'⟩
    unfold objId at hid
    simp only [Prod.mk.injEq] at hid
    have hXX : X' = X := by rw [hX, hX', hid.1]
    subst hXX
    unfold objOk
    icases Hoo with ⟨%rs0, -, -, %hok⟩
    have hXn : X' < cf.n := by rw [hX]; exact hok.2.2.2.2.2.2.1
    unfold shared
    icases Hsh with ⟨-, #Hbc, -, -⟩
    have hr : (List.range maxS)[X']? = some X' := by
      have := cfOk_maxS hc; exact List.getElem?_range (by omega)
    ihave #Hi := (BigSepL.bigSepL_lookup
      (Φ := fun _ X => iprop(inv (bcastN X) (bcastInv (GF := GF) γ X))) hr) $$ Hbc
    imod inv_acc (by exact fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hb, -⟩
    imod Hb with Hb
    unfold bcastInv bcastLb
    icases Hb with ⟨%B, HA, -, %hro⟩
    ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ HA Hl
    ihave %hv' := mono_list_auth_lb_valid _ _ _ _ $$ HA Hl'
    have hB := prefix_getElem? hv.2 hl
    have hB' := prefix_getElem? hv'.2 hl'
    have hseq : o.proSeq = o'.proSeq := BitVec.eq_of_toNat_eq hid.2
    have hjj := hro.2.2 j j' m m' o o' hB hB' hmt hmt' hmo hmo' hseq
    subst hjj
    unfold rcpt
    ihave %hv2 := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hr Hr'
    have := DFrac.valid_op_own hv2.1
    simp at this
  · imodintro
    iframe
    ipureintro; exact hid

/-- My matched proposals are not a pending object. -/
theorem matched_ne (hc : cf.Ok) (γ : Names) (γl : SrvNames) (o : ObjV) :
    ∀ H : List (ObjV × DVal), shared (GF := GF) γ ∗ matchedToks γ cf γl H ∗ pendOk γ cf γl o ⊢
      |={⊤}=> ⌜∀ x ∈ H, x.2 = .obj (objId x.1) → objId x.1 ≠ objId o⌝ ∗
        matchedToks γ cf γl H ∗ pendOk γ cf γl o
  | [] => by
    iintro ⟨-, Hm, Ho⟩
    imodintro
    iframe
    ipureintro; simp
  | x :: H => by
    have ih := matched_ne hc γ γl o H
    unfold matchedToks at ih ⊢
    iintro ⟨#Hsh, Hm, Ho⟩
    icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨Hx, Hm⟩
    imod ih $$ [$Hsh $Hm $Ho] with ⟨%h, Hm, Ho⟩
    by_cases hx : x.2 = .obj (objId x.1)
    · simp only [hx, ↓reduceIte]
      imod pendOk_ne hc γ γl x.1 o $$ [$Hsh $Hx $Ho] with ⟨%hne, Hx, Ho⟩
      imodintro
      iframe Ho
      isplitr
      · ipureintro
        intro y hy hy2
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hne
        · exact h y hy hy2
      iapply BigSepL.bigSepL_cons.2
      iframe Hm
      rw [if_pos hx]; iexact Hx
    · simp only [hx, ↓reduceIte]
      imodintro
      iframe Ho
      isplitr
      · ipureintro
        intro y hy hy2
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hy2 hx
        · exact h y hy hy2
      iapply BigSepL.bigSepL_cons.2
      iframe Hm
      rw [if_neg hx]; iexact Hx

instance cons_factJust_persistent (γ : Names) (key : FKey) (val : FVal) :
    Persistent (factJust (GF := GF) γ key val) := by unfold factJust; infer_instance

instance cons_nextJust_persistent (γ : Names) (k t : Nat) (pv : PrivSt) :
    Persistent (nextJust (GF := GF) γ k t pv) := by
  unfold nextJust; split
  · infer_instance
  · split <;> infer_instance

theorem slotOf_isObj {key : FKey} {t : Nat} (h : key.slotOf = some t) : key.isObj = false := by
  cases key <;> simp_all [FKey.slotOf, model.FKey.isObj]

theorem rabia_keys_sub (k : Nat) : (↑rabiaN : CoPset) ⊆ ⊤ \ ↑(srvKeysN k) := by
  have hd : (↑(ndot rabiaR "inv") : CoPset) ## ↑(ndot rabiaR "keys") :=
    ndot_ne_disjoint rabiaR (by decide)
  have h1 : (↑rabiaN : CoPset) ## ↑(srvKeysN k) := by
    unfold rabiaN srvKeysN
    exact ndot_preserve_disjoint_r _ hd
  intro x hx
  exact LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h => h1 x ⟨hx, h⟩⟩

/-- The executor records its fact of slot `t` (a key not written this slot). -/
theorem insertMine (γ : Names) (k : Nat) (γl : SrvNames) (t : Nat) (cur Ke : List FKey)
    (key : FKey) (val : FVal) (hslot : key.slotOf = some t) (hcur : key ∉ cur)
    (hw : key.writer = some (.srv k))
    (hkind : ∀ r id X s, key ≠ .reg r ∧ key ≠ .pobj id ∧ key ≠ .robj X r ∧ key ≠ .mydec X s ∧
      key ≠ .cfg)
    (hKe : KeysEx t cur Ke) :
    shared (GF := GF) γ ∗ isSrvKeys γ k γl ∗ keysPart γl false Ke ∗ factJust γ key val ⊢
      |={⊤}=> keysPart γl false (key :: Ke) ∗ ⌜KeysEx t (key :: cur) (key :: Ke)⌝ ∗
        fact γ.rab key val := by
  iintro ⟨#Hsh, #Hks, Hkp, #Hj⟩
  unfold factJust
  icases Hj with ⟨%S, #HS, %hJ⟩
  unfold shared
  icases Hsh with ⟨#Hrab, -, -, -⟩
  imod srvKeys_acc γ k γl false ⊤ (fun _ _ => CoPset.mem_full) Ke $$ [$Hks $Hkp]
    with ⟨%K, %Ko, HK, ⟨%hperm, %hKo⟩, Hclose⟩
  have hnot : key ∉ K := by
    intro hk
    rcases List.mem_append.mp (hperm.mem_iff.mp hk) with h | h
    · obtain ⟨s, hs, h2⟩ := hKe.1 key h
      rw [hslot] at hs; cases hs
      rcases h2 with h2 | ⟨-, h2⟩
      · omega
      · exact hcur h2
    · have := hKo key h
      rw [slotOf_isObj hslot] at this; simp at this
  imod fact_insert γ.rab _ (rabia_keys_sub k) (.srv k) K key val S hw hnot hkind hJ
    $$ [$Hrab $HK $HS] with ⟨HK, #Hf⟩
  imod Hclose $$ %(key :: K) %(key :: Ke) [$HK] with Hkp
  · ipureintro
    refine ⟨List.Perm.cons key hperm, fun key' hk' => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact slotOf_isObj hslot
    · obtain ⟨s, hs, -⟩ := hKe.1 key' hk'
      exact slotOf_isObj hs
  imodintro
  iframe Hkp Hf
  ipureintro
  refine ⟨fun key' hk' => ?_, fun key' hk' => ?_⟩
  · rcases List.mem_cons.mp hk' with rfl | hk'
    · exact ⟨t, hslot, Or.inr ⟨rfl, List.mem_cons_self⟩⟩
    · obtain ⟨s, hs, h2⟩ := hKe.1 key' hk'
      exact ⟨s, hs, h2.imp id (fun h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩)⟩
  · rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hslot
    · exact hKe.2 key' hk'

/-- `E_k` grows by the executor's next round message of slot `t`. -/
theorem exLog_snoc {L : List MsgV} {t ρ : Nat} {m : MsgV} (hok : ExLogOk L) (hpos : ExLogPos L t ρ)
    (hm : msgRound m = some (t, ρ)) (hty : m.ty ≠ tyClientRequest) :
    ExLogOk (L ++ [m]) ∧ ExLogPos (L ++ [m]) t (ρ + 1) := by
  have hget : ∀ (i : Nat) (x : MsgV), (L ++ [m])[i]? = some x →
      (i < L.length ∧ L[i]? = some x) ∨ (i = L.length ∧ x = m) := by
    intro i x h
    by_cases hi : i < L.length
    · left; rw [List.getElem?_append_left hi] at h; exact ⟨hi, h⟩
    · right
      rw [List.getElem?_append_right (by omega)] at h
      cases hk : i - L.length with
      | zero => rw [hk] at h; simp at h; exact ⟨by omega, h.symm⟩
      | succ n => rw [hk] at h; simp at h
  have hleft : ∀ (i : Nat) (x : MsgV), L[i]? = some x → (L ++ [m])[i]? = some x := by
    intro i x h
    have hi : i < L.length := (List.getElem?_eq_some_iff.mp h).1
    rw [List.getElem?_append_left hi]; exact h
  have hlast : (L ++ [m])[L.length]? = some m := by simp
  obtain ⟨⟨h1, h2, h3⟩, hcr⟩ := hok
  obtain ⟨p1, p2⟩ := hpos
  -- `m`'s round is new
  have hnew : ∀ (i : Nat) (x : MsgV), L[i]? = some x → msgRound x ≠ some (t, ρ) := by
    intro i x hx hr
    have := p1 x (List.mem_of_getElem? hx) t ρ hr
    omega
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro i x sl r hx hr
    rcases hget i x hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj, y, hy, hyr⟩ := h1 i x sl r hx hr
      exact ⟨j, hj, y, hleft j y hy, hyr⟩
    · rw [hm] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, hr⟩ := hr
      obtain ⟨y, hy, hyr⟩ := p2 r (by omega)
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
      exact ⟨j, (List.getElem?_eq_some_iff.mp hj).1, y, hleft j y hj, hyr⟩
  · intro i j x y sr hx hy hxr hyr
    rcases hget i x hx with ⟨hi, hx'⟩ | ⟨hi, hx'⟩ <;> rcases hget j y hy with ⟨hj, hy'⟩ | ⟨hj, hy'⟩
    · exact h2 i j x y sr hx' hy' hxr hyr
    · subst hy'; rw [hm] at hyr; rw [← hyr] at hxr; exact absurd hxr (hnew i x hx')
    · subst hx'; rw [hm] at hxr; rw [← hxr] at hyr; exact absurd hyr (hnew j y hy')
    · omega
  · intro i j x y o o' hx hy hxt hyt _ _ _
    rcases hget i x hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩
    · rcases hget j y hy with ⟨hj, hy⟩ | ⟨rfl, rfl⟩
      · exact h3 i j x y o o' hx hy hxt hyt ‹_› ‹_› ‹_›
      · exact absurd hyt hty
    · exact absurd hxt hty
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hcr x hx
    · simp at hx; subst hx; exact hty
  · intro x hx sl r hr
    rcases List.mem_append.mp hx with hx | hx
    · have := p1 x hx sl r hr; omega
    · simp at hx; subst hx; rw [hm] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      omega
  · intro r hr
    by_cases hr' : r < ρ
    · obtain ⟨y, hy, hyr⟩ := p2 r hr'
      exact ⟨y, List.mem_append_left _ hy, hyr⟩
    · have : r = ρ := by omega
      subst this
      exact ⟨m, by simp, hm⟩

/-- The history's facts as a list (from slot `off`). -/
def histL (k : Nat) : Nat → List (ObjV × DVal) → List (FKey × FVal)
  | _, [] => []
  | off, x :: H => (.prop k off, .obj (objId x.1)) :: (.mydec k off, .dval x.2) :: histL k (off + 1) H

theorem histL_mem (k : Nat) : ∀ (H : List (ObjV × DVal)) (off i : Nat) (x : ObjV × DVal),
    H[i]? = some x → (FKey.prop k (off + i), FVal.obj (objId x.1)) ∈ histL k off H ∧
      (FKey.mydec k (off + i), FVal.dval x.2) ∈ histL k off H
  | [], _, _, _, h => by simp at h
  | y :: H, off, 0, x, h => by simp at h; subst h; simp [histL]
  | y :: H, off, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    have := histL_mem k H (off + 1) i x h
    rw [show off + 1 + i = off + (i + 1) by omega] at this
    simp only [histL]
    exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this.1),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this.2)⟩

theorem histL_facts (γ : Names) (k : Nat) : ∀ (H : List (ObjV × DVal)) (off : Nat),
    ([∗list] i ↦ x ∈ H, fact (GF := GF) γ.rab (.prop k (off + i)) (.obj (objId x.1)) ∗
      fact γ.rab (.mydec k (off + i)) (.dval x.2)) ⊢
    [∗list] kv ∈ histL k off H, fact γ.rab kv.1 kv.2
  | [], off => by simp [histL]
  | x :: H, off => by
    have ih := histL_facts γ k H (off + 1)
    have hmono : ([∗list] i ↦ y ∈ H, fact (GF := GF) γ.rab (.prop k (off + (i + 1)))
        (.obj (objId y.1)) ∗ fact γ.rab (.mydec k (off + (i + 1))) (.dval y.2)) ⊢
        [∗list] i ↦ y ∈ H, fact (GF := GF) γ.rab (.prop k (off + 1 + i)) (.obj (objId y.1)) ∗
          fact γ.rab (.mydec k (off + 1 + i)) (.dval y.2) :=
      BigSepL.bigSepL_mono (fun {i y} _ => by
        rw [show off + (i + 1) = off + 1 + i by omega])
    simp only [histL]
    iintro Hb
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨⟨H1, H2⟩, Hr⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply BigSepL.bigSepL_cons.2
    iframe H2
    iapply ih
    iapply hmono $$ Hr

theorem histFacts_list (γ : Names) (k : Nat) (H : List (ObjV × DVal)) :
    histFacts (GF := GF) γ k H ⊢ [∗list] kv ∈ histL k 0 H, fact γ.rab kv.1 kv.2 := by
  refine .trans ?_ (histL_facts γ k H 0)
  unfold histFacts
  refine BigSepL.bigSepL_mono (fun {i y} _ => ?_)
  rw [Nat.zero_add]

/-- (A missing law of `Proto.lean`: unfolds `objOk`.) An object's facts do not depend on its slot. -/
theorem cons_objOk_svrSeq (γ : Names) (o : ObjV) (s : w32) :
    objOk (GF := GF) γ cf o ⊢ objOk γ cf { o with svrSeq := s } := by
  unfold objOk; iintro H; iexact H

/-- The justification of my proposal of slot `t` (`PropOk`, from my history and my matched
proposals' tokens). -/
theorem propJust (γ : Names) (k : Nat) (γl : SrvNames) (H : List (ObjV × DVal)) (o : ObjV)
    (t : Nat) (hHt : H.length = t) (hk : k < cf.n) (hc : cf.Ok) :
    shared (GF := GF) γ ∗ cfgIs γ.rab cf ∗ histFacts γ k H ∗ matchedToks γ cf γl H ∗
      pendOk γ cf γl o ⊢
      |={⊤}=> factJust γ (.prop k t) (.obj (objId o)) ∗ matchedToks γ cf γl H ∗
        pendOk γ cf γl o := by
  subst hHt
  iintro ⟨#Hsh, #Hcf, #Hh, Hm, Ho⟩
  ihave #Hcff : fact γ.rab FKey.cfg (FVal.cfgv cf) $$ [Hcf]
  · unfold cfgIs; icases Hcf with ⟨#H, -⟩; iexact H
  imod matched_ne hc γ γl o H $$ [$Hsh $Hm $Ho] with ⟨%hne, Hm, Ho⟩
  ihave #Hoo : objOk γ cf o $$ [Ho]
  · unfold pendOk; icases Ho with ⟨#H, -⟩; iexact H
  imodintro
  iframe Hm Ho
  unfold objOk
  icases Hoo with ⟨%rs0, #Hpo, -, %hok⟩
  ihave #HL := histFacts_list γ k H $$ Hh
  unfold factJust
  iexists (FKey.cfg, FVal.cfgv cf) :: (FKey.pobj (objId o), FVal.reqs rs0) :: histL k 0 H
  isplitl
  · iapply BigSepL.bigSepL_cons.2
    iframe Hcff
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · simp only [objId]; iexact Hpo
    · iexact HL
  ipureintro
  intro M hM hS0 hfree
  have hc := cfgOf_of hS0
  have hS := facts_tail hS0
  have hpo : M (.pobj (objId o)) = some (.reqs rs0) := hS _ List.mem_cons_self
  have hH : ∀ i x, H[i]? = some x → M (.prop k i) = some (.obj (objId x.1)) ∧
      M (.mydec k i) = some (.dval x.2) := by
    intro i x hx
    have := histL_mem k H 0 i x hx
    rw [Nat.zero_add] at this
    exact ⟨hS _ (List.mem_cons_of_mem _ this.1), hS _ (List.mem_cons_of_mem _ this.2)⟩
  refine Valid.insert M hc hM _ _ hfree ?_ ⟨by simp, fun id X r => ⟨by simp, by simp⟩⟩ (by simp)
    (by simp) (by simp) (by simp)
  simp only [Justified]
  refine ⟨hk, ⟨_, hpo⟩, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx⟩ : ∃ x, H[s]? = some x := Option.isSome_iff_exists.mp (by simp; omega)
    obtain ⟨h1, h2⟩ := hH s x hx
    exact ⟨_, _, h1, h2⟩
  · intro s hs hp hd
    obtain ⟨x, hx⟩ : ∃ x, H[s]? = some x := Option.isSome_iff_exists.mp (by simp; omega)
    obtain ⟨h1, h2⟩ := hH s x hx
    rw [h1] at hp; rw [h2] at hd
    simp only [Option.some.injEq, FVal.obj.injEq, FVal.dval.injEq] at hp hd
    exact hne x (List.mem_of_getElem? hx) (by rw [hd, hp]) hp

theorem bm_prop (γ : Names) (k : Nat) (o : ObjV) (t : Nat) (ht : t < 10000) :
    fact (GF := GF) γ.rab (.prop k t) (.obj (objId o)) ∗ objOk γ cf o ⊢ bmsgOk γ cf k (propMsg o t) := by
  have hw : (W32 (t : Int)).toNat = t := by word
  unfold bmsgOk
  simp only [propMsg, show ¬ (tyProposal = tyClientRequest) by decide, ↓reduceIte]
  iintro ⟨#Hf, #Ho⟩
  iexists { o with svrSeq := W32 (t : Int) }
  isplitr
  · ipureintro; simp
  isplitl
  · iapply cons_objOk_svrSeq $$ Ho
  simp only [hw, objId]
  iexact Hf

theorem pendOk_objOk (γ : Names) (γl : SrvNames) (o : ObjV) :
    pendOk (GF := GF) γ cf γl o ⊢ objOk γ cf o ∗ pendOk γ cf γl o := by
  unfold pendOk; iintro ⟨#H1, H2⟩; iframe H1 H2

/-- The key and value of my message of round `exRound pv`'s state (round 1) or vote (round 2). -/
def binKey (k t : Nat) (pv : PrivSt) : FKey :=
  if pv.round = 1 then .st k t pv.phase.toNat else .vt k t pv.phase.toNat
def binVal (pv : PrivSt) : FVal := .bit (pv.my pv.phase.toNat pv.round.toNat).toNat

theorem nextJust_bin (γ : Names) (k t : Nat) (pv : PrivSt)
    (hr : (pv.round = 1 ∧ pv.phase ≠ 0) ∨ pv.round = 2) :
    nextJust (GF := GF) γ k t pv ⊢ factJust γ (binKey k t pv) (binVal pv) := by
  have e1 : (1 : w32).toNat = 1 := rfl
  have e2 : (2 : w32).toNat = 2 := rfl
  have n21 : ((2 : w32) = 1) = False := by decide
  unfold nextJust binKey binVal
  rcases hr with ⟨h1, h2⟩ | h1
  · simp only [h1, h2, ne_eq, not_false_eq_true, and_self, ↓reduceIte, e1]
    iintro H; iexact H
  · simp only [h1, n21, _root_.false_and, ↓reduceIte, e2]
    iintro H; iexact H

theorem bm_bc (γ : Names) (k t : Nat) (pv : PrivSt) (ht : t < 10000)
    (hr : (pv.round = 1 ∧ pv.phase ≠ 0) ∨ pv.round = 2) :
    fact (GF := GF) γ.rab (binKey k t pv) (binVal pv) ⊢
      bmsgOk γ cf k (bcMsg t pv.phase pv.round (pv.my pv.phase.toNat pv.round.toNat)) := by
  have hw : (W32 (t : Int)).toNat = t := by word
  have e1 : (1 : w32).toNat = 1 := rfl
  have e2 : (2 : w32).toNat = 2 := rfl
  have n21 : ((2 : w32) = 1) = False := by decide
  unfold bmsgOk binKey binVal bcMsg
  rcases hr with ⟨h1, h2⟩ | h1
  · simp only [h1, ↓reduceIte, show ¬ (tyState = tyClientRequest) by decide,
      show ¬ (tyState = tyProposal) by decide]
    iintro #Hf
    iexists { (default : ObjV) with svrSeq := W32 (t : Int) }
    isplitr
    · ipureintro
      refine ⟨rfl, ?_, rfl⟩
      have : pv.phase.toNat ≠ 0 := fun h => h2 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    simp only [hw]
    iexact Hf
  · simp only [h1, n21, ↓reduceIte, show ¬ (tyVote = tyClientRequest) by decide,
      show ¬ (tyVote = tyProposal) by decide, show ¬ (tyVote = tyState) by decide]
    iintro #Hf
    iexists { (default : ObjV) with svrSeq := W32 (t : Int) }
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    simp only [hw]
    iexact Hf

end basics

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS] [math.rand.Hyps GF]

theorem exLog_append (γl : SrvNames) (L : List MsgV) (m : MsgV) :
    exAuth (GF := GF) γl L ⊢ |==> (exAuth γl (L ++ [m]) ∗ exLb γl (L ++ [m])) := by
  unfold exAuth exLb
  iintro H
  imod monoListAuthOwn_update (L ++ [m]) (List.prefix_append L [m]) $$ H with ⟨H, #Hlb⟩
  imodintro
  iframe H Hlb

/-- The object `ConsensusObj{SvrSeq: s}` represents `{ default with svrSeq := s }`. -/
theorem cons_objRep_slotOnly (s : w32) (v : ConsensusObj)
    (hv : v = { (Perennial.zero_val ConsensusObj) with SvrSeq' := s }) :
    ⊢ objRep (GF := GF) v { (default : ObjV) with svrSeq := s } := by
  subst hv
  exact (rabia.internal.ledger.objRep_zero (GF := GF)).trans
    (cons_objRep_svrSeq (Perennial.zero_val ConsensusObj) default s)

variable (D : ExDeps (GF := GF))
include D
variable (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
  (ch : SrvChans) (c : Loc)

theorem wp_genProposalMsg_proof (s : Nat) (e : SlotV) (pv : PrivSt) (hs : s < lenLedger) :
    {{ exPre (GF := GF) γ cf ∗ consRO γ cf k γl γc ch c ∗ ⌜γl.slots[s]? = some e⌝ ∗ slotPriv e.loc pv }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"genProposalMsg"))
        (Val #(W32 s)))
    {{ (v : Msg), RET #v; slotPriv e.loc pv ∗
        msgRep v (propMsg pv.myProp s) }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, #Hro, %he, Hpv⟩
  wp_auto
  have hs' : (W32 (s : Int)).toNat < lenLedger := by unfold lenLedger at hs ⊢; word
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c _ hs' $$ [$Hpkg $Hconf $Hro]
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hro2 := Hro
  unfold consRO
  icases Hro2 with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ [Hpkg]
  · iPkgInit
  unfold lenLedger at hs Hl
  wp_auto
  have hmod : W32 (s : Int) % W32 10000 = W32 (s : Int) := by word
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (s : Int))))) _ _ e.loc (by word) $$ [Hsl]
    with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (s : Int))))).toNat = s by word]
    simp [he]
  iapply wp_fupd
  wp_apply D.getMyProposal e.loc pv $$ [$Hlp $Hpv] as %v ⟨Hpv, #Hv⟩
  ipersist obj
  imodintro
  iapply HΦ
  iframe Hpv
  iapply cons_msgRep_intro
  · simp [propMsg, tyProposal, Proposal]
  simp only [propMsg]
  iexists { v with SvrSeq' := W32 (s : Int) }
  iframe obj
  iapply cons_objRep_svrSeq $$ Hv

theorem wp_genDecMsgType2_proof (s : Nat) (v : ConsensusObj) (o : ObjV) :
    {{ exPre (GF := GF) γ cf ∗ objRep v o }}
      (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"genDecMsgType2"))
        (Val #(W32 s))) (Val #v))
    {{ (w : Msg), RET #w; msgRep w (decMsg o s) }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, #Hv⟩
  iapply wp_fupd
  wp_auto
  ipersist obj
  imodintro
  iapply HΦ
  iapply cons_msgRep_intro
  · simp [decMsg, tyDecision, Decision]
  simp only [decMsg]
  iexists { v with SvrSeq' := W32 (s : Int) }
  iframe obj
  iapply cons_objRep_svrSeq $$ Hv

theorem wp_genBinConMsg_proof (s : Nat) (e : SlotV) (pv : PrivSt) (pse rod : w32) (hs : s < lenLedger)
    (hr : rod = 1 ∨ rod = 2) (hp : pse.toNat < pv.myBC.length) :
    {{ exPre (GF := GF) γ cf ∗ consRO γ cf k γl γc ch c ∗ ⌜γl.slots[s]? = some e⌝ ∗ slotPriv e.loc pv }}
      (App (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"genBinConMsg"))
        (Val #(W32 s))) (Val #pse)) (Val #rod))
    {{ (v : Msg), RET #v; slotPriv e.loc pv ∗
        msgRep v (bcMsg s pse rod (pv.my pse.toNat rod.toNat)) }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, #Hro, %he, Hpv⟩
  wp_auto
  have hs' : (W32 (s : Int)).toNat < lenLedger := by unfold lenLedger at hs ⊢; word
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c _ hs' $$ [$Hpkg $Hconf $Hro]
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hro2 := Hro
  unfold consRO
  icases Hro2 with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ [Hpkg]
  · iPkgInit
  unfold lenLedger at hs Hl
  wp_auto
  have hmod : W32 (s : Int) % W32 10000 = W32 (s : Int) := by word
  rw [hmod]
  iapply wp_fupd
  wp_if_destruct
  · slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (s : Int))))) _ _ e.loc (by word) $$ [Hsl]
      with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 (s : Int))))).toNat = s by word]
      simp [he]
    wp_apply D.getMyBC e.loc pv pse (W32 1) (Or.inl (by decide)) hp $$ [$Hlp $Hpv] as Hpv
    ipersist «$r0»
    imodintro
    iapply HΦ
    iframe Hpv
    iapply cons_msgRep_intro
    · simp [bcMsg, tyState, tyVote, State, Vote]
    simp only [bcMsg]
    iexists _
    iframe «$r0»
    iapply cons_objRep_slotOnly _ _ rfl
  · wp_if_destruct
    · slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (s : Int))))) _ _ e.loc (by word) $$ [Hsl]
        with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 (s : Int))))).toNat = s by word]
        simp [he]
      wp_apply D.getMyBC e.loc pv pse (W32 2) (Or.inr (by decide)) hp $$ [$Hlp $Hpv] as Hpv
      ipersist «$r0»
      imodintro
      iapply HΦ
      iframe Hpv
      iapply cons_msgRep_intro
      · simp [bcMsg, tyState, tyVote, State, Vote]
      simp only [bcMsg]
      iexists _
      iframe «$r0»
      iapply cons_objRep_slotOnly _ _ rfl
    · exfalso; rcases hr with h | h <;> simp_all

omit D in
theorem wp_idSeqKey (l : Loc) (v : ConsensusObj) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ l ↦ v }}
      (App (Val #(functions idSeqKey [])) (Val #l))
    {{ (key : w64), RET #key; l ↦ v }} := by
  wp_start as Hl
  wp_auto
  iapply HΦ $$ Hl

set_option maxHeartbeats 2000000 in
theorem wp_getRequest_proof (σ : ExSt) :
    {{ exPre (GF := GF) γ cf ∗ exIdle γ cf k γl γc ch c σ }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"getRequest")) (Val #()))
    {{ (b : Bool), RET #b;
        if b then ∃ x : ExSlot, exRun γ cf k γl γc ch c σ x ∗
          ⌜x.pv.phase = 0 ∧ x.pv.round = 1 ∧ x.pv.myBC = [] ∧ x.recv = [] ∧ x.ql = [] ∧
            x.ρs = 0 ∧ x.cur = []⌝
        else exIdle γ cf k γl γc ch c σ }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hidle⟩
  unfold exIdle
  icases Hidle with ⟨Hcom, Hcoin, Hseq, %ht⟩
  unfold exCommon
  icases Hcom with ⟨#Hro, Hfields, #Hhist, Hmt, %HHl, #Hpf, Hkp, %HKe, Hex, Hprod, %Hlog, Hfresh⟩
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  unfold lenLedger at ht
  wp_auto
  have hseq : W64 ((σ.t : Int) - 1) + W64 1 = W64 (σ.t : Int) := by word
  rw [hseq]
  wp_if_destruct
  · -- the scope guard: nothing
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    try unfold exIdle exCommon
    iframe
    iframe Hro Hhist Hpf
    ipureintro
    exact ⟨⟨HHl, HKe, Hlog⟩, by unfold lenLedger; omega⟩
  wp_apply wp_QPop D.pop D.len γ k γl γc ch c $$ [$Hpkg $Hro] as %v %ok Hv
  wp_if_destruct
  · iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    try unfold exIdle exCommon
    iframe
    iframe Hro Hhist Hpf
    ipureintro
    exact ⟨⟨HHl, HKe, Hlog⟩, by unfold lenLedger; omega⟩
  · icases Hv with ⟨%o, #Hov, Hok⟩
    unfold exFields
    icases Hfields with ⟨⟨%mp, %dm, HD, Hmap⟩, Hnulls, Htr, Hdist⟩
    wp_apply wp_idSeqKey obj_ptr v $$ [$Hpkg $obj] as %key obj
    wp_apply wp_map_lookup1 go.uint64 go.bool mp dm key (DFrac.own 1) $$ [$Hmap] as Hmap
    generalize (dm !! key).getD (zero_val Bool) = bd
    wp_if_destruct
    · have htl : σ.t < 10000 := by word
      rw [hseq]
      have hs' : (W32 (sint.Z (W64 (σ.t : Int)))).toNat < lenLedger := by unfold lenLedger; word
      wp_apply wp_UpdateTermIfNecessary γ k γl γc ch c _ true hs' $$ [$Hpkg $Hconf $Hro]
      ihave #Hro2 := Hro
      unfold consRO
      icases Hro2 with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
        #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
      unfold ledgerRO
      icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
      ihave %Hl := ownSlice_len _ _ _ $$ Hsl
      rw [List.length_map, Hlen] at Hl
      unfold lenLedger at Hl Hlen
      obtain ⟨e, he⟩ : ∃ e, γl.slots[σ.t]? = some e :=
        Option.isSome_iff_exists.mp (by simp [Hlen]; exact htl)
      ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ [Hpkg]
      · iPkgInit
      ihave ⟨Hpart, Hfresh⟩ := freshSlots_take γl γc σ.t e he $$ Hfresh
      unfold slotExecPart
      icases Hpart with ⟨Hpv, Hcons, Hexn⟩
      wp_auto
      have hmod : W32 (sint.Z (W64 (σ.t : Int))) % W32 10000 = W32 (σ.t : Int) := by word
      try rw [hmod]
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc (by word) $$ [Hsl]
        with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyProposal e.loc _ v o $$ [$Hlp $Hpv $Hov] as Hpv
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc (by word) $$ [Hsl]
        with Hsl3
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
        simp [he]
      ihave ⟨Hph, Hrd, ⟨%mv, Hmpv, #Hmo⟩, %rest, Hrest, Hclose⟩ := (slotPriv_fields e.loc _).1 $$ Hpv
      wp_auto
      ihave Hpv := Hclose $$ %_ %(W32 1) %mv [$Hph $Hrd $Hmpv $Hmo $Hrest]
      iapply wp_fupd
      wp_apply wp_ResetCommonCoin c $$ [$Hpkg $Hcoin] as Hcoin
      imod (monoListLbOwn_nil (γc.qlog σ.t) (A := Option Nat)) with #Hqlb
      imodintro
      iapply HΦ
      simp only [↓reduceIte]
      iexists (ExSlot.mk o { phase := 0, round := W32 1, myProp := o, myBC := [] } [] [] 0 [])
      isplitl
      · unfold exRun exCommon exSlotRes exFields exCoinOk qLb consRO ledgerRO
        iunfold coinOk at Hcoin
        simp only
        iframe Hro Hhist Hpf Hqlb
        iframe
        ipureintro
        exact ⟨⟨HHl, HKe, Hlog⟩, by unfold lenLedger; omega, he, by simp⟩
      ipureintro
      simp
    · wp_apply wp_idSeqKey obj_ptr v $$ [$Hpkg $obj] as %key' obj
      wp_apply wp_mapDelete mp dm key' go.uint64 go.bool $$ [$Hmap] as Hmap
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      try unfold exIdle exCommon
      try unfold exFields
      iframe
      iframe Hro Hhist Hpf
      ipureintro
      exact ⟨⟨HHl, HKe, Hlog⟩, by unfold lenLedger; omega⟩


/-- The executor's message of round `ρs` of slot `t` into `E_k`: its fact recorded, the log
extended. -/
theorem mineMsg (σ : ExSt) (cur : List FKey) (ρs : Nat) (key : FKey) (val : FVal) (m : MsgV)
    (P : IProp GF) [Persistent P]
    (hslot : key.slotOf = some σ.t) (hcur : key ∉ cur) (hw : key.writer = some (.srv k))
    (hkind : ∀ r id X s, key ≠ .reg r ∧ key ≠ .pobj id ∧ key ≠ .robj X r ∧ key ≠ .mydec X s ∧
      key ≠ .cfg)
    (hKe : KeysEx σ.t cur σ.Ke) (hlog : ExLogOk σ.L ∧ ExLogPos σ.L σ.t ρs)
    (hm : msgRound m = some (σ.t, ρs)) (hty : m.ty ≠ tyClientRequest)
    (hbm : fact γ.rab key val ∗ P ⊢ bmsgOk γ cf k m) :
    shared (GF := GF) γ ∗ isSrvKeys γ k γl ∗ keysPart γl false σ.Ke ∗ factJust γ key val ∗
      exAuth γl σ.L ∗ P ⊢
      |={⊤}=> keysPart γl false (key :: σ.Ke) ∗ ⌜KeysEx σ.t (key :: cur) (key :: σ.Ke)⌝ ∗
        exAuth γl (σ.L ++ [m]) ∗ exLb γl (σ.L ++ [m]) ∗ bmsgOk γ cf k m ∗
        ⌜ExLogOk (σ.L ++ [m]) ∧ ExLogPos (σ.L ++ [m]) σ.t (ρs + 1)⌝ ∗ fact γ.rab key val := by
  iintro ⟨#Hsh, #Hks, Hkp, #Hj, Hex, #HP⟩
  imod insertMine γ k γl σ.t cur σ.Ke key val hslot hcur hw hkind hKe $$ [$Hsh $Hks $Hkp $Hj]
    with ⟨Hkp, %hKe', #Hf⟩
  imod exLog_append γl σ.L m $$ Hex with ⟨Hex, #Hlb⟩
  ihave #Hbm := hbm $$ [$Hf $HP]
  imodintro
  iframe Hkp Hex Hlb Hbm Hf
  ipureintro
  exact ⟨hKe', exLog_snoc hlog.1 hlog.2 hm hty⟩

theorem consRO_keys : consRO (GF := GF) γ cf k γl γc ch c ⊢ isSrvKeys γ k γl := by
  unfold consRO
  iintro ⟨%ledger, %ql, %wg, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HK⟩
  iexact HK

theorem consRO_ledger : consRO (GF := GF) γ cf k γl γc ch c ⊢ ∃ ledger : GoSlice,
    structFieldRef Consensus go!"Ledger" c ↦□ ledger ∗ ledgerRO γl ledger := by
  unfold consRO
  iintro ⟨%ledger, %ql, %wg, -, -, -, -, -, -, -, -, #HL, -, -, -, #HLro, -, -, -⟩
  iexists ledger
  iframe HL HLro

theorem consRO_e2n : consRO (GF := GF) γ cf k γl γc ch c ⊢ isSpsc γl.e2n ch.e2n (e2nP γ cf k γl)
    (fun _ => iprop(False)) := by
  unfold consRO srvChans
  iintro ⟨%ledger, %ql, %wg, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, #He, -, -⟩, -, -, -, -⟩
  iexact He

/-- `phase0Round1BeforeWait(seq)` (needs `k < cf.n`: `Justified` of a proposal). -/
theorem wp_phase0Round1BeforeWait_proof (hk : k < cf.n) (σ : ExSt) (x : ExSlot)
    (hx : x.pv.phase = 0 ∧ x.pv.round = 1 ∧ x.ρs = 0 ∧ x.cur = []) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phase0Round1BeforeWait"))
        (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = 1 ∧ x'.cur = [.prop k σ.t]⌝ ∗
        fact γ.rab (.prop k σ.t) (.obj (objId x.o)) }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hrun⟩
  unfold exRun exCommon exSlotRes
  icases Hrun with ⟨⟨#Hro, Hfields, #Hhist, Hmt, %HHl, #Hpf, Hkp, %HKe, Hex, Hprod, %Hlog, Hfresh⟩,
    Hcoin, Hseq, %ht, %e, %he, Hpv, %hmy, Hpo, Hcons, #Hql, %hq, Hexn⟩
  obtain ⟨hph, hrd, hρ, hcur⟩ := hx
  wp_auto
  wp_apply wp_genProposalMsg_proof D γ k γl γc ch c σ.t e x.pv ht $$ [Hpv]
    as %v ⟨Hpv, #Hv⟩
  · iframe Hpv Hro
    isplitl []
    · unfold exPre; iframe Hconf Hsh Hcfg; iexact Hpkg
    · ipureintro; exact he
  have hto : (W32 (σ.t : Int)).toNat = σ.t := by unfold lenLedger at ht; word
  ihave #HK := consRO_keys D γ k γl γc ch c $$ Hro
  ihave %hcok := cfgIs_ok γ.rab cf $$ Hcfg
  imod propJust γ k γl σ.H x.o σ.t HHl hk hcok $$ [$Hsh $Hcfg $Hhist $Hmt $Hpo] with ⟨#Hj, Hmt, Hpo⟩
  ihave ⟨#Hoo, Hpo⟩ := pendOk_objOk γ γl x.o $$ Hpo
  have hm : msgRound (propMsg x.pv.myProp σ.t) = some (σ.t, x.ρs) := by
    simp [msgRound, roundOf, propMsg, hρ]; unfold lenLedger at ht; omega
  imod mineMsg (cf := cf) D γ k γl σ x.cur x.ρs (.prop k σ.t) (.obj (objId x.o))
    (propMsg x.pv.myProp σ.t) (objOk γ cf x.o) (by simp [FKey.slotOf]) (by simp [hcur])
    (by simp [model.FKey.writer]) (by intro r id X s; simp) HKe
    ⟨Hlog.2.1, Hlog.2.2⟩ hm (by simp [propMsg]; decide) (by rw [hmy]; exact bm_prop γ k x.o σ.t (by unfold lenLedger at ht; omega))
    $$ [$Hsh $HK $Hkp $Hj $Hex $Hoo] with ⟨Hkp, %hKe', Hex, #Hlb, #Hbm, %hlog', #Hfct⟩
  wp_apply wp_toNet γ k γl γc ch c v σ.sent $$ [Hprod]
    as Hprod
  · iframe Hro Hprod
    unfold e2nP
    iexists propMsg x.pv.myProp σ.t, σ.L ++ [propMsg x.pv.myProp σ.t]
    iframe Hv Hbm Hlb
    ipureintro
    refine ⟨?_, hlog'.1⟩
    rw [Hlog.1]; simp
  iapply HΦ
  iexists (ExSt.mk σ.t σ.H σ.cmds (.prop k σ.t :: σ.Ke) (σ.L ++ [propMsg x.pv.myProp σ.t])
    (σ.sent ++ [v]))
  iexists (ExSlot.mk x.o x.pv x.recv x.ql 1 [.prop k σ.t])
  simp only
  iframe
  iframe Hro Hhist Hpf Hql
  rw [hcur] at hKe'; rw [hρ] at hlog'
  isplitr
  · ipureintro
    exact ⟨⟨HHl, hKe', by simp [Hlog.1], hlog'.1, hlog'.2⟩, ht, he, hmy, hq⟩
  isplitr
  · ipureintro
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, trivial, trivial⟩
  · rw [hmy]; iexact Hfct

/-- `phase0Round2BeforeWait(seq)` (with `hnew`: this round's key not written yet). -/
theorem wp_phase0Round2BeforeWait_proof (σ : ExSt) (x : ExSlot)
    (hph : x.pv.phase = 0) (hrd : x.pv.round = 2)
    (hρ : x.ρs = exRound x.pv) (hp : x.pv.phase.toNat < x.pv.myBC.length)
    (hnew : binKey k σ.t x.pv ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗ nextJust γ k σ.t x.pv }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phase0Round2BeforeWait"))
        (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs + 1 ∧
          x'.cur = binKey k σ.t x.pv :: x.cur⌝ }} := by
  have hr12 : (x.pv.round = 1 ∧ x.pv.phase ≠ 0) ∨ x.pv.round = 2 := Or.inr hrd
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hrun, #Hj⟩
  unfold exRun exCommon exSlotRes
  icases Hrun with ⟨⟨#Hro, Hfields, #Hhist, Hmt, %HHl, #Hpf, Hkp, %HKe, Hex, Hprod, %Hlog, Hfresh⟩,
    Hcoin, Hseq, %ht, %e, %he, Hpv, %hmy, Hpo, Hcons, #Hql, %hq, Hexn⟩
  wp_auto
  have hgen := wp_genBinConMsg_proof (cf := cf) D γ k γl γc ch c σ.t e x.pv (W32 0) (W32 2) ht
    (Or.inr rfl) (by rw [show (W32 0 : w32) = x.pv.phase by rw [hph]; rfl]; exact hp)
  have hv' : bcMsg σ.t (W32 0) (W32 2) (x.pv.my (W32 0 : w32).toNat (W32 2 : w32).toNat) =
      bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat) := by
    rw [hph, hrd]; rfl
  rw [hv'] at hgen
  wp_apply hgen $$ [Hpv] as %v ⟨Hpv, #Hv⟩
  · iframe Hpv Hro
    isplitl []
    · unfold exPre; iframe Hconf Hsh Hcfg; iexact Hpkg
    · ipureintro; exact he
  have hto : (W32 (σ.t : Int)).toNat = σ.t := by unfold lenLedger at ht; word
  ihave #HK := consRO_keys D γ k γl γc ch c $$ Hro
  ihave #Hj2 := nextJust_bin γ k σ.t x.pv hr12 $$ Hj
  have hm : msgRound (bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)) =
      some (σ.t, x.ρs) := by
    rw [hρ]; unfold exRound
    rcases hr12 with ⟨h1, h2⟩ | h1 <;>
      simp [msgRound, roundOf, bcMsg, h1, tyState, tyVote, tyProposal] <;>
      (unfold lenLedger at ht; first | omega | (simp [h1] at *; omega) | decide)
  imod mineMsg (cf := cf) D γ k γl σ x.cur x.ρs (binKey k σ.t x.pv) (binVal x.pv)
    (bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)) iprop(True)
    (by unfold binKey; split <;> simp [FKey.slotOf]) hnew
    (by unfold binKey; split <;> simp [model.FKey.writer]) (by intro r id X s; unfold binKey; split <;> simp) HKe
    ⟨Hlog.2.1, Hlog.2.2⟩ hm (by unfold bcMsg; split <;> (simp only; decide))
    (by iintro ⟨H, -⟩; iapply bm_bc γ k σ.t x.pv (by unfold lenLedger at ht; omega) hr12 $$ H)
    $$ [$Hsh $HK $Hkp $Hj2 $Hex] with ⟨Hkp, %hKe', Hex, #Hlb, #Hbm, %hlog', #Hfct⟩
  wp_apply wp_toNet γ k γl γc ch c v σ.sent $$ [Hprod]
    as Hprod
  · iframe Hro Hprod
    unfold e2nP
    iexists bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat),
      σ.L ++ [bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)]
    iframe Hv Hbm Hlb
    ipureintro
    refine ⟨?_, hlog'.1⟩
    rw [Hlog.1]; simp
  iapply HΦ
  iexists (ExSt.mk σ.t σ.H σ.cmds (binKey k σ.t x.pv :: σ.Ke)
    (σ.L ++ [bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)])
    (σ.sent ++ [v]))
  iexists (ExSlot.mk x.o x.pv x.recv x.ql (x.ρs + 1) (binKey k σ.t x.pv :: x.cur))
  simp only
  iframe
  iframe Hro Hhist Hpf Hql
  ipureintro
  exact ⟨⟨⟨HHl, hKe', by simp [Hlog.1], hlog'.1, hlog'.2⟩, ht, he, hmy, hq⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, trivial, trivial⟩

/-- `phaseNRound1BeforeWait(seq)` (with `hnew`: this round's key not written yet). -/
theorem wp_phaseNRound1BeforeWait_proof (σ : ExSt) (x : ExSlot)
    (hph : x.pv.phase ≠ 0) (hrd : x.pv.round = 1)
    (hρ : x.ρs = exRound x.pv) (hp : x.pv.phase.toNat < x.pv.myBC.length)
    (hnew : binKey k σ.t x.pv ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗ nextJust γ k σ.t x.pv }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phaseNRound1BeforeWait"))
        (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs + 1 ∧
          x'.cur = binKey k σ.t x.pv :: x.cur⌝ }} := by
  have hr12 : (x.pv.round = 1 ∧ x.pv.phase ≠ 0) ∨ x.pv.round = 2 := Or.inl ⟨hrd, hph⟩
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hrun, #Hj⟩
  unfold exRun exCommon exSlotRes
  icases Hrun with ⟨⟨#Hro, Hfields, #Hhist, Hmt, %HHl, #Hpf, Hkp, %HKe, Hex, Hprod, %Hlog, Hfresh⟩,
    Hcoin, Hseq, %ht, %e, %he, Hpv, %hmy, Hpo, Hcons, #Hql, %hq, Hexn⟩
  wp_auto
  have hs' : (W32 (σ.t : Int)).toNat < lenLedger := by unfold lenLedger at ht ⊢; word
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c _ hs' $$ [$Hpkg $Hconf $Hro]
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave ⟨%ledger, #HL, #HLro⟩ := consRO_ledger D γ k γl γc ch c $$ Hro
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl
  wp_auto
  have hmod : W32 (σ.t : Int) % W32 10000 = W32 (σ.t : Int) := by unfold lenLedger at ht; word
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc (by unfold lenLedger at ht; word) $$ [Hsl]
    with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by unfold lenLedger at ht; word]
    simp [he]
  ihave ⟨Hph, Hrd, ⟨%mv, Hmpv, #Hmo⟩, %rest, Hrest, Hclose⟩ := (slotPriv_fields e.loc _).1 $$ Hpv
  wp_auto
  ihave Hpv := Hclose $$ %x.pv.phase %x.pv.round %mv [$Hph $Hrd $Hmpv $Hmo $Hrest]
  have hgen := wp_genBinConMsg_proof (cf := cf) D γ k γl γc ch c σ.t e x.pv x.pv.phase (W32 1) ht
    (Or.inl rfl) hp
  have hv' : bcMsg σ.t x.pv.phase (W32 1) (x.pv.my x.pv.phase.toNat (W32 1 : w32).toNat) =
      bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat) := by
    rw [hrd]; rfl
  rw [hv'] at hgen
  wp_apply hgen $$ [Hpv] as %v ⟨Hpv, #Hv⟩
  · iframe Hpv Hro
    isplitl []
    · unfold exPre; iframe Hconf Hsh Hcfg; iexact Hpkg
    · ipureintro; exact he
  have hto : (W32 (σ.t : Int)).toNat = σ.t := by unfold lenLedger at ht; word
  ihave #HK := consRO_keys D γ k γl γc ch c $$ Hro
  ihave #Hj2 := nextJust_bin γ k σ.t x.pv hr12 $$ Hj
  have hm : msgRound (bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)) =
      some (σ.t, x.ρs) := by
    rw [hρ]; unfold exRound
    rcases hr12 with ⟨h1, h2⟩ | h1 <;>
      simp [msgRound, roundOf, bcMsg, h1, tyState, tyVote, tyProposal] <;>
      (unfold lenLedger at ht; first | omega | (simp [h1] at *; omega) | decide)
  imod mineMsg (cf := cf) D γ k γl σ x.cur x.ρs (binKey k σ.t x.pv) (binVal x.pv)
    (bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)) iprop(True)
    (by unfold binKey; split <;> simp [FKey.slotOf]) hnew
    (by unfold binKey; split <;> simp [model.FKey.writer]) (by intro r id X s; unfold binKey; split <;> simp) HKe
    ⟨Hlog.2.1, Hlog.2.2⟩ hm (by unfold bcMsg; split <;> (simp only; decide))
    (by iintro ⟨H, -⟩; iapply bm_bc γ k σ.t x.pv (by unfold lenLedger at ht; omega) hr12 $$ H)
    $$ [$Hsh $HK $Hkp $Hj2 $Hex] with ⟨Hkp, %hKe', Hex, #Hlb, #Hbm, %hlog', #Hfct⟩
  wp_apply wp_toNet γ k γl γc ch c v σ.sent $$ [Hprod]
    as Hprod
  · iframe Hro Hprod
    unfold e2nP
    iexists bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat),
      σ.L ++ [bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)]
    iframe Hv Hbm Hlb
    ipureintro
    refine ⟨?_, hlog'.1⟩
    rw [Hlog.1]; simp
  iapply HΦ
  iexists (ExSt.mk σ.t σ.H σ.cmds (binKey k σ.t x.pv :: σ.Ke)
    (σ.L ++ [bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)])
    (σ.sent ++ [v]))
  iexists (ExSlot.mk x.o x.pv x.recv x.ql (x.ρs + 1) (binKey k σ.t x.pv :: x.cur))
  simp only
  iframe
  iframe Hro Hhist Hpf Hql
  ipureintro
  exact ⟨⟨⟨HHl, hKe', by simp [Hlog.1], hlog'.1, hlog'.2⟩, ht, he, hmy, hq⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, trivial, trivial⟩

/-- `phaseNRound2BeforeWait(seq)` (with `hnew`: this round's key not written yet). -/
theorem wp_phaseNRound2BeforeWait_proof (σ : ExSt) (x : ExSlot)
    (hrd : x.pv.round = 2)
    (hρ : x.ρs = exRound x.pv) (hp : x.pv.phase.toNat < x.pv.myBC.length)
    (hnew : binKey k σ.t x.pv ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗ nextJust γ k σ.t x.pv }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phaseNRound2BeforeWait"))
        (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs + 1 ∧
          x'.cur = binKey k σ.t x.pv :: x.cur⌝ }} := by
  have hr12 : (x.pv.round = 1 ∧ x.pv.phase ≠ 0) ∨ x.pv.round = 2 := Or.inr hrd
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hrun, #Hj⟩
  unfold exRun exCommon exSlotRes
  icases Hrun with ⟨⟨#Hro, Hfields, #Hhist, Hmt, %HHl, #Hpf, Hkp, %HKe, Hex, Hprod, %Hlog, Hfresh⟩,
    Hcoin, Hseq, %ht, %e, %he, Hpv, %hmy, Hpo, Hcons, #Hql, %hq, Hexn⟩
  wp_auto
  have hs' : (W32 (σ.t : Int)).toNat < lenLedger := by unfold lenLedger at ht ⊢; word
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c _ hs' $$ [$Hpkg $Hconf $Hro]
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave ⟨%ledger, #HL, #HLro⟩ := consRO_ledger D γ k γl γc ch c $$ Hro
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl
  wp_auto
  have hmod : W32 (σ.t : Int) % W32 10000 = W32 (σ.t : Int) := by unfold lenLedger at ht; word
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc (by unfold lenLedger at ht; word) $$ [Hsl]
    with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by unfold lenLedger at ht; word]
    simp [he]
  ihave ⟨Hph, Hrd, ⟨%mv, Hmpv, #Hmo⟩, %rest, Hrest, Hclose⟩ := (slotPriv_fields e.loc _).1 $$ Hpv
  wp_auto
  ihave Hpv := Hclose $$ %x.pv.phase %x.pv.round %mv [$Hph $Hrd $Hmpv $Hmo $Hrest]
  have hgen := wp_genBinConMsg_proof (cf := cf) D γ k γl γc ch c σ.t e x.pv x.pv.phase (W32 2) ht
    (Or.inr rfl) hp
  have hv' : bcMsg σ.t x.pv.phase (W32 2) (x.pv.my x.pv.phase.toNat (W32 2 : w32).toNat) =
      bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat) := by
    rw [hrd]; rfl
  rw [hv'] at hgen
  wp_apply hgen $$ [Hpv] as %v ⟨Hpv, #Hv⟩
  · iframe Hpv Hro
    isplitl []
    · unfold exPre; iframe Hconf Hsh Hcfg; iexact Hpkg
    · ipureintro; exact he
  have hto : (W32 (σ.t : Int)).toNat = σ.t := by unfold lenLedger at ht; word
  ihave #HK := consRO_keys D γ k γl γc ch c $$ Hro
  ihave #Hj2 := nextJust_bin γ k σ.t x.pv hr12 $$ Hj
  have hm : msgRound (bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)) =
      some (σ.t, x.ρs) := by
    rw [hρ]; unfold exRound
    rcases hr12 with ⟨h1, h2⟩ | h1 <;>
      simp [msgRound, roundOf, bcMsg, h1, tyState, tyVote, tyProposal] <;>
      (unfold lenLedger at ht; first | omega | (simp [h1] at *; omega) | decide)
  imod mineMsg (cf := cf) D γ k γl σ x.cur x.ρs (binKey k σ.t x.pv) (binVal x.pv)
    (bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)) iprop(True)
    (by unfold binKey; split <;> simp [FKey.slotOf]) hnew
    (by unfold binKey; split <;> simp [model.FKey.writer]) (by intro r id X s; unfold binKey; split <;> simp) HKe
    ⟨Hlog.2.1, Hlog.2.2⟩ hm (by unfold bcMsg; split <;> (simp only; decide))
    (by iintro ⟨H, -⟩; iapply bm_bc γ k σ.t x.pv (by unfold lenLedger at ht; omega) hr12 $$ H)
    $$ [$Hsh $HK $Hkp $Hj2 $Hex] with ⟨Hkp, %hKe', Hex, #Hlb, #Hbm, %hlog', #Hfct⟩
  wp_apply wp_toNet γ k γl γc ch c v σ.sent $$ [Hprod]
    as Hprod
  · iframe Hro Hprod
    unfold e2nP
    iexists bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat),
      σ.L ++ [bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)]
    iframe Hv Hbm Hlb
    ipureintro
    refine ⟨?_, hlog'.1⟩
    rw [Hlog.1]; simp
  iapply HΦ
  iexists (ExSt.mk σ.t σ.H σ.cmds (binKey k σ.t x.pv :: σ.Ke)
    (σ.L ++ [bcMsg σ.t x.pv.phase x.pv.round (x.pv.my x.pv.phase.toNat x.pv.round.toNat)])
    (σ.sent ++ [v]))
  iexists (ExSlot.mk x.o x.pv x.recv x.ql (x.ρs + 1) (binKey k σ.t x.pv :: x.cur))
  simp only
  iframe
  iframe Hro Hhist Hpf Hql
  ipureintro
  exact ⟨⟨⟨HHl, hKe', by simp [Hlog.1], hlog'.1, hlog'.2⟩, ht, he, hmy, hq⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, trivial, trivial⟩

/-- `wp_binBeforeWait`'s statement (with `hnew`). -/
theorem wp_binBeforeWait_proof (fn : GoString) (σ : ExSt) (x : ExSlot)
    (hfn : (fn = go!"phase0Round2BeforeWait" ∧ x.pv.phase = 0 ∧ x.pv.round = 2) ∨
      (fn = go!"phaseNRound1BeforeWait" ∧ x.pv.phase ≠ 0 ∧ x.pv.round = 1) ∨
      (fn = go!"phaseNRound2BeforeWait" ∧ x.pv.round = 2))
    (hρ : x.ρs = exRound x.pv) (hp : x.pv.phase.toNat < x.pv.myBC.length)
    (hnew : binKey k σ.t x.pv ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗ nextJust γ k σ.t x.pv }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! fn)) (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs + 1 ∧
          x'.cur = binKey k σ.t x.pv :: x.cur⌝ }} := by
  rcases hfn with ⟨rfl, hph, hrd⟩ | ⟨rfl, hph, hrd⟩ | ⟨rfl, hrd⟩
  · exact wp_phase0Round2BeforeWait_proof D γ k γl γc ch c σ x hph hrd hρ hp hnew
  · exact wp_phaseNRound1BeforeWait_proof D γ k γl γc ch c σ x hph hrd hρ hp hnew
  · exact wp_phaseNRound2BeforeWait_proof D γ k γl γc ch c σ x hrd hρ hp hnew

end proof

end Perennial.rabia.roles.server.layers.consensus
