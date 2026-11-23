/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/Base.lean`, run `rabia-r1wake-1`.)

The proxy's proof helpers: a receive (blocking or not) on a channel nobody sends on and nobody
closes (a bag of `False`); the agreement of two `prefixFacts` of a slot; the store relation's
steps.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia

/-! ## The store relation -/

theorem storeRel_empty : StoreRel (∅ : GMap GoString GoString) (stateOfCmds []) := by
  intro key; rfl

/-- `naiveExecuteCmd`'s write: the map's insert is the model's write. -/
theorem storeRel_put {m : GMap GoString GoString} {s : KStore} (h : StoreRel m s)
    (key val : GoString) :
    StoreRel (GMap.insert key val m) (fun k => if k = key then some val else s k) := by
  intro k
  by_cases hk : k = key
  · subst hk
    show ((GMap.insert k val m) !! k).getD [] = _
    rw [GMap.lookup_insert]; simp
  · show ((GMap.insert key val m) !! k).getD [] = _
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; simp only [hk, ↓reduceIte]; exact h k

theorem cmdOf_length {i : model.KvInput GoString GoString} (hi : inputOk i) :
    1 + keyLen ≤ (cmdOf i).length := by
  cases i with
  | put k v => simp only [inputOk] at hi; simp [cmdOf, putCmd, hi.1]; omega
  | get k => simp only [inputOk] at hi; simp [cmdOf, getCmd, hi]; omega

theorem cmd_lt_encCmd {q : CmdV} {cmd : GoString} (h : q.commands = [cmd]) :
    cmd.length < (encCmd q).length := by
  simp only [encCmd, h, List.flatMap_cons, List.flatMap_nil, List.append_nil, encBytes,
    List.length_append, List.length_cons]
  omega

/-! ## Facts -/

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

omit [HasExt Net.netExt] go_gctx sem in
/-- A request's registered command, from `regFacts`. -/
theorem regFacts_lookup (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) (i : Nat)
    (r : ReqId) (h : rs[i]? = some r) :
    regFacts (GF := GF) γ rs bc ⊢ ∃ cm, ⌜bc[i]? = some cm⌝ ∗ fact γ (.reg r) (.cmd cm) := by
  unfold regFacts
  iintro ⟨-, H⟩
  iapply (BigSepL.bigSepL_lookup (Φ := fun i r =>
    iprop(∃ cm, ⌜bc[i]? = some cm⌝ ∗ fact (GF := GF) γ (.reg r) (.cmd cm))) h) $$ H

omit [HasExt Net.netExt] go_gctx sem in
theorem regFacts_length (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) :
    regFacts (GF := GF) γ rs bc ⊢ ⌜rs.length = bc.length⌝ := by
  unfold regFacts
  iintro ⟨%h, -⟩
  ipureintro; exact h

omit [HasExt Net.netExt] go_gctx sem in
/-- Two `regFacts` of the same requests have the same commands. -/
theorem regFacts_agree (γ : RabiaNames) (rs : List ReqId) (bc1 bc2 : List GoString) :
    regFacts (GF := GF) γ rs bc1 ∗ regFacts γ rs bc2 ⊢ ⌜bc1 = bc2⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave %hl1 := regFacts_length γ rs bc1 $$ H1
  ihave %hl2 := regFacts_length γ rs bc2 $$ H2
  ihave %hall : ⌜∀ i : Nat, bc1[i]? = bc2[i]?⌝ $$ [H1 H2]
  · iapply pure_forall.2
    iintro %i
    cases hr : rs[i]? with
    | none =>
      ipureintro
      have : rs.length ≤ i := List.getElem?_eq_none_iff.mp hr
      rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]
    | some r =>
      ihave ⟨%c1, %h1, Hf1⟩ := regFacts_lookup γ rs bc1 i r hr $$ H1
      ihave ⟨%c2, %h2, Hf2⟩ := regFacts_lookup γ rs bc2 i r hr $$ H2
      ihave %hc := fact_agree γ (.reg r) (.cmd c1) (.cmd c2) $$ [Hf1 Hf2]
      · isplit <;> iassumption
      cases hc
      ipureintro; rw [h1, h2]
  ipureintro
  exact List.ext_getElem? hall

omit [HasExt Net.netExt] go_gctx sem in
/-- A request appended to a batch's `regFacts`. -/
theorem regFacts_snoc (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) (r : ReqId)
    (cm : GoString) :
    regFacts (GF := GF) γ rs bc ∗ fact γ (.reg r) (.cmd cm) ⊢ regFacts γ (rs ++ [r]) (bc ++ [cm]) := by
  unfold regFacts
  iintro ⟨⟨%hl, #H⟩, #Hf⟩
  isplitr
  · ipureintro; simp [hl]
  iapply BigSepL.bigSepL_snoc.2
  isplitl
  · iapply BigSepL.bigSepL_mono (Φ := fun i r =>
      iprop(∃ cm, ⌜bc[i]? = some cm⌝ ∗ fact (GF := GF) γ (.reg r) (.cmd cm))) ?_ $$ H
    intro i x hx
    iintro ⟨%c, %hc, Hc⟩
    iexists c
    iframe Hc
    ipureintro
    have : i < bc.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; exact this
    rw [List.getElem?_append_left this]; exact hc
  iexists cm
  iframe Hf
  ipureintro
  rw [List.getElem?_append_right (by omega)]; simp [hl]

omit [HasExt Net.netExt] go_gctx sem in
theorem regFacts_nil (γ : RabiaNames) : ⊢ regFacts (GF := GF) γ [] [] := by
  unfold regFacts
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_nil.2; itrivial

omit [HasExt Net.netExt] go_gctx sem in
/-- Two `prefixFacts` of the same slot have the same commands. -/
theorem prefixFacts_agree (γ : RabiaNames) (s : Nat) :
    ∀ (c1 c2 : List GoString), prefixFacts (GF := GF) γ s c1 ∗ prefixFacts γ s c2 ⊢ ⌜c1 = c2⌝ := by
  induction s with
  | zero =>
    intro c1 c2
    simp only [prefixFacts]
    iintro ⟨%h1, %h2⟩
    ipureintro; rw [h1, h2]
  | succ s ih =>
    intro c1 c2
    simp only [prefixFacts]
    iintro ⟨⟨%a1, %d1, H1, Hd1, Hm1⟩, ⟨%a2, %d2, H2, Hd2, Hm2⟩⟩
    ihave %ha := ih a1 a2 $$ [$H1 $H2]
    ihave %hd := fact_agree γ _ _ _ $$ [$Hd1 $Hd2]
    cases hd
    subst ha
    cases d1 with
    | null =>
      icases Hm1 with %e1
      icases Hm2 with %e2
      ipureintro; rw [e1, e2]
    | obj id =>
      icases Hm1 with ⟨%r1, %bc1, Hp1, Hr1, %e1⟩
      icases Hm2 with ⟨%r2, %bc2, Hp2, Hr2, %e2⟩
      ihave %hr := fact_agree γ _ _ _ $$ [$Hp1 $Hp2]
      cases hr
      ihave %hc := regFacts_agree γ _ _ _ $$ [$Hr1 $Hr2]
      ipureintro; rw [e1, e2, hc]

omit [HasExt Net.netExt] go_gctx sem in
instance prefixFacts_timeless (γ : RabiaNames) (s : Nat) (cmds : List GoString) :
    Timeless (prefixFacts (GF := GF) γ s cmds) := by
  induction s generalizing cmds with
  | zero => simp only [prefixFacts]; infer_instance
  | succ s ih =>
    simp only [prefixFacts]
    refine @exists_timeless _ _ _ _ (fun c0 => ?_)
    refine @exists_timeless _ _ _ _ (fun d => ?_)
    cases d <;> dsimp only <;> infer_instance

/-- `objOk` is timeless (unfolds Proto's `objOk`). -/
instance objOk_timeless (γ : Names) (cf : RCfg) (o : ObjV) :
    Timeless (objOk (GF := GF) γ cf o) := by
  unfold objOk; infer_instance

/-- `decObjOk` is timeless (unfolds Proto's `decObjOk`). -/
instance decObjOk_timeless (γ : Names) (cf : RCfg) (s : Nat) (d : DVal) (o : ObjV) :
    Timeless (decObjOk (GF := GF) γ cf s d o) := by
  unfold decObjOk; cases d <;> dsimp only <;> infer_instance

/-- `decInfo` is timeless (unfolds consensus's `decInfo`). -/
instance decInfo_timeless (γ : Names) (cf : RCfg) (s : Nat) (st : rabia.internal.ledger.SlotSt) :
    Timeless (decInfo (GF := GF) γ cf s st) := by
  unfold decInfo; split <;> infer_instance

/-- `isRabia` is persistent (an invariant; unfolds Ghost's `isRabia`). -/
instance isRabia_persistent' (γ : RabiaNames) : Persistent (isRabia (GF := GF) γ) := by
  unfold isRabia; infer_instance

/-- `isSrvKeys` is persistent (an invariant; unfolds Chans's `isSrvKeys`). -/
instance isSrvKeys_persistent (γ : Names) (k : Nat) (γl : SrvNames) :
    Persistent (isSrvKeys (GF := GF) γ k γl) := by
  unfold isSrvKeys; infer_instance

/-- `slotSt` is timeless (unfolds ledger's `slotSt`). -/
instance slotSt_timeless' (γ : GName) (st : rabia.internal.ledger.SlotSt) :
    Timeless (rabia.internal.ledger.slotSt (GF := GF) γ st) := by
  unfold rabia.internal.ledger.slotSt; infer_instance

end facts

/-! ## Receives on a channel of `False` -/

section bag
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- A nonblocking receive on a bag channel whose elements are `False` (nobody sends, nobody
closes) never fires. -/
theorem bag_false_nonblocking_recv_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF)
    (hP : ∀ v, P v ⊢ False) (Φ : V → Bool → IProp GF) :
    ⊢ isChanBag γ ch P -∗ nonblockingRecvAuInner γ V Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
  iintro ⟨#Hch, #Hinv⟩
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | (_ | ⟨v1, rest⟩)
  all_goals dsimp only
  case Buffered.cons =>
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, -⟩
    iexfalso; iapply hP $$ HP
  case SndPending =>
    iexfalso; iapply hP $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- A blocking receive on a bag channel whose elements are `False`. -/
theorem bag_false_recv_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF)
    (hP : ∀ v, P v ⊢ False) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isChanBag γ ch P -∗ recvAu γ V Φ := by
  iintro Hlc #Hb
  iapply bag_recv_au γ ch P Φ $$ Hlc Hb
  inext
  iintro %v HP
  iexfalso; iapply hP $$ HP

end bag

end Perennial.rabia.roles.server.layers.proxy
