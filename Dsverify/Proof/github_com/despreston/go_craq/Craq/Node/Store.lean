module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.StoreLemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section store
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

instance storeOwn_timeless (γs : GName) (q : Qp) (S : StoreS) :
    Timeless (storeOwn (hG := hG) γs q S) := by
  unfold storeOwn; infer_instance

instance nlogAuth_timeless (γ : CraqNames) (a : GoString) (L : CLog) :
    Timeless (nlogAuth (GF := GF) γ a L) := by
  unfold nlogAuth; infer_instance

theorem itemFacts_lookup (γ : CraqNames) (S : StoreS) (e : StoreS.Ent) (h : e ∈ S) :
    itemFacts (GF := GF) γ S ⊢ itemFact γ e := by
  unfold itemFacts
  exact BI.BigSepL.bigSepL_mem (Φ := fun e => itemFact (GF := GF) γ e) h

/-- A store's keys are keys the protocol handles (its items are versions, `valsElem`). -/
theorem itemFacts_keysOk (γ : CraqNames) : ∀ S : StoreS,
    itemFacts (GF := GF) γ S ⊢ ⌜∀ e ∈ S, keyOk e.1⌝
  | [] => by iintro -; ipureintro; intro e he; simp at he
  | e :: S => by
    have IH := itemFacts_keysOk γ S
    unfold itemFacts at IH ⊢
    iintro #H
    icases BI.BigSepL.bigSepL_cons.1 $$ H with ⟨#Hf, #Hr⟩
    ihave %h2 := IH $$ Hr
    unfold itemFact
    icases Hf with ⟨#Hve, -⟩
    ihave %h1 := valsElem_kvOk γ _ _ _ $$ Hve
    ipureintro
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | h
    · exact h1.1
    · exact h2 e' h

/-- An item of `k` is an entry of key `k`. -/
theorem StoreS.mem_items_key (S : StoreS) (k : GoString) (it : w64 × GoString × Bool)
    (h : it ∈ S.items k) : ∃ e ∈ S, e.1 = k := by
  simp only [StoreS.items, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨e, ⟨he, hk⟩, -⟩ := h
  exact ⟨e, he, hk⟩

/-- The store half's keys are keys the protocol handles (from the node's invariant). -/
theorem store_keysOk (cfg : Cfg GF) (a : GoString) (γs : GName) (S : StoreS) (E : CoPset)
    (hE : ↑nodeN ⊆ E) :
    inv nodeN (nodeInv cfg a γs) ∗ storeOwn γs (1 : Qp).half S ={E}=∗
      storeOwn γs (1 : Qp).half S ∗ ⌜∀ e ∈ S, keyOk e.1⌝ := by
  iintro ⟨#Hinv, HS⟩
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S', %Ln, HS', Hln, %HLn, #Hf⟩
  unfold storeOwn
  ihave %Heq := ghostVar_agree γs S _ S' _ $$ HS HS'
  subst Heq
  ihave %Hk := itemFacts_keysOk cfg.γ S $$ Hf
  imod Hclose $$ [HS' Hln] with -
  · inext
    iexists S, Ln
    iframe; iframe #
    ipureintro; exact HLn
  imodintro
  iframe HS
  ipureintro; exact Hk

theorem itemFacts_write (γ : CraqNames) (S : StoreS) (k x : GoString) (v : w64) :
    itemFacts (GF := GF) γ S ∗ valsElem γ v k x ⊢ itemFacts γ (S.write k x v) := by
  iintro ⟨#H, #Hv⟩
  unfold itemFacts StoreS.write
  iapply (BI.BigSepL.bigSepL_append (Φ := fun _ e => itemFact (GF := GF) γ e)).2
  iframe H
  iapply (BI.BigSepL.bigSepL_singleton (Φ := fun _ e => itemFact (GF := GF) γ e)).2
  unfold itemFact
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe Hv

theorem itemFacts_commit (γ : CraqNames) (S : StoreS) (k : GoString) (v : w64) :
    itemFacts (GF := GF) γ S ∗ cvLb γ k v ⊢ itemFacts γ (S.commit k v) := by
  have key : ∀ (i : Nat) (e : StoreS.Ent), (S.commit k v)[i]? = some e →
      iprop(□ (itemFacts (GF := GF) γ S ∗ cvLb γ k v)) ⊢ itemFact γ e := by
    intro i e he
    have hmem : e ∈ S.commit k v := List.mem_of_getElem? he
    rcases (StoreS.mem_commit S k v e).1 hmem with ⟨_, h⟩ | ⟨⟨k0, v0, x0, c0⟩, he0, hk, _, heq⟩
    · iintro #⟨H, -⟩
      iapply itemFacts_lookup γ S e h $$ H
    · iintro #⟨H, Hc⟩
      ihave #H0 := itemFacts_lookup γ S _ he0 $$ H
      subst heq
      simp only at hk
      subst hk
      by_cases hv : v0 = v
      · subst hv
        simp only [↓reduceIte]
        unfold itemFact
        icases H0 with ⟨#Hve, -⟩
        simp only [↓reduceIte]
        iframe Hve Hc
      · simp only [hv, ↓reduceIte]
        iexact H0
  refine Entails.trans ?_ (BI.BigSepL.bigSepL_intro key)
  iintro ⟨#H, #Hc⟩
  imodintro; iframe H Hc

/-- `Write(k, x, v)` under the lock: the lock's half and the invariant's make the whole. -/
theorem wp_store_Write (cfg : Cfg GF) (a : GoString) (γs : GName) (e : GoInterfaceOk)
    (S : StoreS) (k : GoString) (sl : GoSlice) (x : GoString) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ inv nodeN (nodeInv cfg a γs) ∗ storeOwn γs (1 : Qp).half S ∗
        sl ↦*□ x ∗ valsElem cfg.γ v k x) -∗
      (storeOwn γs (1 : Qp).half (S.write k x v) -∗ Φ #interface.nil) -∗
      WP (App (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #sl)) (Val #v)) {{ Φ }} := by
  iintro %Φ ⟨#Hst, #Hinv, HS, #Hsl, #Hve⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨Hw, -⟩
  ihave Hw := Hw $$ %k %sl %x %v Hsl
  iunfold atomic_wp at Hw
  iapply Hw
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S', %Ln, HS', Hln, %HLn, #Hf⟩
  unfold storeOwn
  ihave %Heq := ghostVar_agree γs S _ S' _ $$ HS HS'
  subst Heq
  ihave Hfull := (ghostVar_split_half γs (1 : Qp).half S).2 $$ [HS HS']
  · iframe
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨S, ⟨⟩⟩ : (Tele.cons fun _ : StoreS => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hfull
  isplit
  · iintro Hfull
    icases (ghostVar_split_half γs (1 : Qp).half S).1 $$ Hfull with ⟨HS, HS'⟩
    imod Hmask with -
    imod Hclose $$ [HS' Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iframe
  · iintro Hfull
    icases (ghostVar_split_half γs (1 : Qp).half (S.write k x v)).1 $$ Hfull with ⟨HS, HS'⟩
    ihave #Hf' := itemFacts_write cfg.γ S k x v $$ [Hf Hve]
    · iframe Hf Hve
    imod Hmask with -
    imod Hclose $$ [HS' Hln] with -
    · inext
      iexists (S.write k x v), Ln
      iframe; iframe #
      ipureintro
      intro k'
      rw [StoreS.maxCommitted_write]
      exact HLn k'
    imodintro
    iintro -
    iapply HΦ
    iexact HS

/-- `Commit(k, v)` under the lock. On success (the store has version `v` of `k`), the caller's
update `W` (run with the invariant open, at `⊤ ∖ nodeN`) gives `cvLb k v` (what the committed
item's facts need) from `P`; the node's log logs the commit. -/
theorem wp_store_Commit (HL : Laws (GF := GF)) (cfg : Cfg GF) (a : GoString) (γs : GName)
    (e : GoInterfaceOk) (S : StoreS) (k : GoString) (v : w64) (P P' : IProp GF) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ inv nodeN (nodeInv cfg a γs) ∗ storeOwn γs (1 : Qp).half S ∗
        P ∗ (∀ (x : GoString) (c : Bool), ⌜(k, v, x, c) ∈ S⌝ -∗ valsElem cfg.γ v k x -∗ P
          ={⊤ \ ↑nodeN}=∗ cvLb cfg.γ k v ∗ P')) -∗
      (∀ err : GoInterface,
        (if S.hasVer k v then
          iprop(⌜err = interface.nil⌝ ∗ ⌜keyOk k⌝ ∗ storeOwn γs (1 : Qp).half (S.commit k v) ∗
            cvLb cfg.γ k v ∗ P')
        else iprop(errNotFound err ∗ storeOwn γs (1 : Qp).half S ∗ P)) -∗ Φ #err) -∗
      WP (App (App (Val #(methods e.ty go!"Commit" e.v)) (Val #k)) (Val #v)) {{ Φ }} := by
  iintro %Φ ⟨#Hst, #Hinv, HS, HP, HW⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, Hc, -⟩
  ihave Hc' := Hc $$ %k %v
  iclear Hc
  iunfold atomic_wp at Hc'
  iapply Hc'
  iclear Hc'
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S', %Ln, HS', Hln, %HLn, #Hf⟩
  unfold storeOwn
  ihave %Heq := ghostVar_agree γs S _ S' _ $$ HS HS'
  subst Heq
  ihave Hfull := (ghostVar_split_half γs (1 : Qp).half S).2 $$ [HS HS']
  · iframe
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨S, ⟨⟩⟩ : (Tele.cons fun _ : StoreS => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hfull
  isplit
  · iintro Hfull
    icases (ghostVar_split_half γs (1 : Qp).half S).1 $$ Hfull with ⟨HS, HS'⟩
    imod Hmask with -
    imod Hclose $$ [HS' Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iframe
  · iintro Hfull
    imod Hmask with -
    cases hv : S.hasVer k v
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases (ghostVar_split_half γs (1 : Qp).half S).1 $$ Hfull with ⟨HS, HS'⟩
      imod Hclose $$ [HS' Hln] with -
      · inext
        iexists S, Ln
        iframe; iframe #
        ipureintro; exact HLn
      imodintro
      iintro %err Herr
      iapply HΦ
      iframe
    · simp only [↓reduceIte]
      obtain ⟨x, c, hmem⟩ := (StoreS.hasVer_iff S k v).1 hv
      ihave #Hx := itemFacts_lookup cfg.γ S _ hmem $$ Hf
      unfold itemFact
      icases Hx with ⟨#Hve, -⟩
      ihave %Hkx := valsElem_kvOk cfg.γ v k x $$ Hve
      imod HW $$ %x %c %hmem Hve HP with ⟨#Hcv, HP'⟩
      icases (ghostVar_split_half γs (1 : Qp).half (S.commit k v)).1 $$ Hfull with ⟨HS, HS'⟩
      imod (HL.nlog_append cfg.γ a Ln k v) $$ Hln with Hln
      ihave #Hf' := itemFacts_commit cfg.γ S k v $$ [Hf Hcv]
      · iframe Hf Hcv
      imod Hclose $$ [HS' Hln] with -
      · inext
        iexists (S.commit k v), (Ln ++ [(k, v)])
        iframe; iframe #
        ipureintro
        intro k'
        rw [HL.cvOf_append, StoreS.maxCommitted_commit S k v hv, HLn k]
        by_cases hk : k' = k
        · subst hk; simp [HLn k']
        · simp [hk, HLn k']
      imodintro
      iintro %err %Herr
      iapply HΦ
      simp only [↓reduceIte]
      iframe; iframe #
      ipureintro; exact ⟨Herr, Hkx.1⟩

/-- `ReadVersion(k, v)`, unlocked (the invariant's half): the item read is a version. -/
theorem wp_store_ReadVersion (cfg : Cfg GF) (a : GoString) (γs : GName) (e : GoInterfaceOk)
    (k : GoString) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ inv nodeN (nodeInv cfg a γs)) -∗
      (∀ (p : Loc) (err : GoInterface),
        ((∃ x : GoString, ⌜err = interface.nil⌝ ∗ itemPtr p k v x ∗ valsElem cfg.γ v k x) ∨
          errNotFound err) -∗ Φ (PairV #p #err)) -∗
      WP (App (App (Val #(methods e.ty go!"ReadVersion" e.v)) (Val #k)) (Val #v)) {{ Φ }} := by
  iintro %Φ ⟨#Hst, #Hinv⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, -, Hc, -⟩
  ihave Hc' := Hc $$ %k %v
  iclear Hc
  iunfold atomic_wp at Hc'
  iapply Hc'
  iclear Hc'
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S, %Ln, HS, Hln, %HLn, #Hf⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨(1 : Qp).half, ⟨S, ⟨⟩⟩⟩ : (Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM,
    BI.texist_cons, BI.texist_nil]
  unfold storeOwn
  iframe HS
  isplit
  · iintro HS
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iframe
  · iintro %r ⟨HS, %Hr1, %Hr2⟩
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iintro %p %err Hpost
    iapply HΦ
    cases r with
    | none =>
      iright; iexact Hpost
    | some x =>
      ileft
      icases Hpost with ⟨%Herr, Hp⟩
      obtain ⟨c, hc⟩ := Hr1 x rfl
      ihave #Hx := itemFacts_lookup cfg.γ S (k, v, x, c) ((StoreS.mem_items S k _).1 hc) $$ Hf
      unfold itemFact
      icases Hx with ⟨#Hve, -⟩
      iexists x
      iframe Hp Hve
      ipureintro; exact Herr

/-- `AllCommitted()` with a share of the store's contents (under the lock: its half). -/
theorem wp_store_AllCommitted_own (γs : GName) (e : GoInterfaceOk) (q : Qp) (S : StoreS) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ storeOwn γs q S) -∗
      (∀ sl : GoSlice, storeOwn γs q S -∗ itemsIn sl S (fun _ _ _ c => c = true) -∗
        Φ (PairV #sl #interface.nil)) -∗
      WP (App (Val #(methods e.ty go!"AllCommitted" e.v)) (Val #())) {{ Φ }} := by
  iintro %Φ ⟨#Hst, HS⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, -, -, Hc, -⟩
  ihave Hw := (atomic_wp_seq (TA := Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil)) $$ Hc
    %Φ %(⟨q, ⟨S, ⟨⟩⟩⟩ : (Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil).Arg)
  iclear Hc
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM,
    BI.texist_cons, BI.texist_nil]
  iapply Hw $$ HS
  iintro HS %sl Hsl
  iapply HΦ $$ HS Hsl

/-- `AllDirty()` with a share of the store's contents. -/
theorem wp_store_AllDirty_own (γs : GName) (e : GoInterfaceOk) (q : Qp) (S : StoreS) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ storeOwn γs q S) -∗
      (∀ sl : GoSlice, storeOwn γs q S -∗ itemsIn sl S (fun _ _ _ c => c = false) -∗
        Φ (PairV #sl #interface.nil)) -∗
      WP (App (Val #(methods e.ty go!"AllDirty" e.v)) (Val #())) {{ Φ }} := by
  iintro %Φ ⟨#Hst, HS⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, -, -, -, Hc, -⟩
  ihave Hw := (atomic_wp_seq (TA := Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil)) $$ Hc
    %Φ %(⟨q, ⟨S, ⟨⟩⟩⟩ : (Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil).Arg)
  iclear Hc
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM,
    BI.texist_cons, BI.texist_nil]
  iapply Hw $$ HS
  iintro HS %sl Hsl
  iapply HΦ $$ HS Hsl

/-- `AllCommitted()`, unlocked: a snapshot `S0`, with the node log's cover of its newest
committed versions. -/
theorem wp_store_AllCommitted_inv (HL : Laws (GF := GF)) (cfg : Cfg GF) (a : GoString)
    (γs : GName) (e : GoInterfaceOk) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ inv nodeN (nodeInv cfg a γs)) -∗
      (∀ (sl : GoSlice) (S0 : StoreS) (L0 : CLog), itemsIn sl S0 (fun _ _ _ c => c = true) -∗
        covers cfg.γ a L0 -∗ ⌜∀ k, cvOf L0 k = S0.maxCommitted k⌝ -∗
        Φ (PairV #sl #interface.nil)) -∗
      WP (App (Val #(methods e.ty go!"AllCommitted" e.v)) (Val #())) {{ Φ }} := by
  iintro %Φ ⟨#Hst, #Hinv⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, -, -, Hc, -⟩
  iunfold atomic_wp at Hc
  iapply Hc
  iclear Hc
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S, %Ln, HS, Hln, %HLn, #Hf⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨(1 : Qp).half, ⟨S, ⟨⟩⟩⟩ : (Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM,
    BI.texist_cons, BI.texist_nil]
  unfold storeOwn
  iframe HS
  isplit
  · iintro HS
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iframe
  · iintro HS
    ihave ⟨Hln, #Hcov⟩ := HL.nlog_covers cfg.γ a Ln $$ Hln
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iintro %sl Hsl
    iapply HΦ $$ Hsl Hcov
    ipureintro; exact HLn

/-- `AllNewerCommitted(req)`, unlocked: each key's newest committed item if newer than the
request's, with the items' facts and (from a cover of the node's log) the bound of `L`. -/
theorem wp_store_AllNewerCommitted (HL : Laws (GF := GF)) (cfg : Cfg GF) (a : GoString)
    (γs : GName) (e : GoInterfaceOk) (mp : Loc) (req : GMap GoString w64) (dq : DFrac)
    (L : CLog) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ inv nodeN (nodeInv cfg a γs) ∗ ownMap mp dq req ∗
        covers cfg.γ a L) -∗
      (∀ (sl : GoSlice) (S0 : StoreS), ownMap mp dq req -∗ newestIn sl S0 req -∗
        itemFacts cfg.γ S0 -∗ ⌜∀ k, uint.Z (cvOf L k) ≤ uint.Z (S0.maxCommitted k)⌝ -∗
        Φ (PairV #sl #interface.nil)) -∗
      WP (App (Val #(methods e.ty go!"AllNewerCommitted" e.v)) (Val #mp)) {{ Φ }} := by
  iintro %Φ ⟨#Hst, #Hinv, Hmp, #Hcov⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, -, -, -, -, -, Hc⟩
  ihave Hc' := Hc $$ %mp %req %dq Hmp
  iclear Hc
  iunfold atomic_wp at Hc'
  iapply Hc'
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S, %Ln, HS, Hln, %HLn, #Hf⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨(1 : Qp).half, ⟨S, ⟨⟩⟩⟩ : (Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM,
    BI.texist_cons, BI.texist_nil]
  unfold storeOwn
  iframe HS
  isplit
  · iintro HS
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iframe
  · iintro HS
    ihave %Hle := HL.nlog_covers_le cfg.γ a Ln L $$ [Hln Hcov]
    · iframe Hln Hcov
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iintro %sl ⟨Hmp, Hsl⟩
    iapply HΦ $$ Hmp Hsl Hf
    ipureintro
    intro k
    rw [← HLn k]; exact Hle k

/-- `AllNewerDirty(req)`, unlocked: dirty items, with the items' facts. -/
theorem wp_store_AllNewerDirty (cfg : Cfg GF) (a : GoString)
    (γs : GName) (e : GoInterfaceOk) (mp : Loc) (req : GMap GoString w64) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF,
      (isStore (interface.ok e) γs ∗ inv nodeN (nodeInv cfg a γs) ∗ ownMap mp dq req) -∗
      (∀ (sl : GoSlice) (S0 : StoreS), ownMap mp dq req -∗
        itemsIn sl S0 (fun _ _ _ c => c = false) -∗ itemFacts cfg.γ S0 -∗
        Φ (PairV #sl #interface.nil)) -∗
      WP (App (Val #(methods e.ty go!"AllNewerDirty" e.v)) (Val #mp)) {{ Φ }} := by
  iintro %Φ ⟨#Hst, #Hinv, Hmp⟩ HΦ
  unfold isStore
  icases Hst with ⟨%e', %he, #Hspec⟩
  cases he
  icases Hspec with ⟨-, -, -, -, -, Hc, -⟩
  ihave Hc' := Hc $$ %mp %req %dq Hmp
  iclear Hc
  iunfold atomic_wp at Hc'
  iapply Hc'
  rw [Std.LawfulSet.diff_empty]
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S, %Ln, HS, Hln, %HLn, #Hf⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨(1 : Qp).half, ⟨S, ⟨⟩⟩⟩ : (Tele.cons fun _ : Qp => Tele.cons fun _ : StoreS => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM,
    BI.texist_cons, BI.texist_nil]
  unfold storeOwn
  iframe HS
  isplit
  · iintro HS
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iframe
  · iintro HS
    imod Hmask with -
    imod Hclose $$ [HS Hln] with -
    · inext
      iexists S, Ln
      iframe; iframe #
      ipureintro; exact HLn
    imodintro
    iintro %sl ⟨Hmp, Hsl⟩
    iapply HΦ $$ Hmp Hsl Hf

end store

end NodeP

end github_com.despreston.go_craq

end Perennial
