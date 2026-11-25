module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.UpdSpecs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Conn
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.ConnPS
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.UpdGhost

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section update
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- Put the lock invariant back after a failure: both role halves (the node's and the
coordinator's) are set to the node's state; one goes back to the lock. -/
theorem relock (HL : Laws (GF := GF)) (cfg : Cfg GF) (a : GoString) (γs : GName) (n nbM latM : Loc)
    (h t : Bool) (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS) (r : Role) :
    ⊢ roleHalf cfg.γ a r -∗ roleHalf cfg.γ a r -∗ lockedState cfg γs n nbM latM h t nbrs lat S -∗
      |==> lockInv cfg a γs n nbM latM := by
  iintro H1 H2 Hls
  imod HL.roleHalf_update cfg.γ a r r ((t, nextAddr nbrs) : Role) $$ [H1 H2] with ⟨H1, -⟩
  · iframe
  imodintro
  unfold lockInv
  iexists h, t, nbrs, lat, S
  iframe

/-- Every fraction is the sum of two (to lend one part and keep the other). -/
theorem dfrac_halves (dq : DFrac) : ∃ dq1 dq2 : DFrac, dq = dq1 • dq2 := by
  cases dq with
  | own q => exact ⟨.own q.half, .own q.half, by show _ = DFrac.own _; rw [Qp.half_add_half]⟩
  | discard => exact ⟨.discard, .discard, rfl⟩
  | ownDiscard q =>
    exact ⟨.own q.half, .ownDiscard q.half, by show _ = DFrac.ownDiscard _; rw [Qp.half_add_half]⟩

/-- The metadata's points-to from its fields. -/
theorem metaPtr_join (ptr : Loc) (dq : DFrac) (mh mt : Bool) (mp mn mtl : GoString)
    (hnn : ptr ≠ null) :
    structFieldRef transport.NodeMeta go!"IsHead" ptr ↦{dq} mh ∗
      structFieldRef transport.NodeMeta go!"IsTail" ptr ↦{dq} mt ∗
      structFieldRef transport.NodeMeta go!"Prev" ptr ↦{dq} mp ∗
      structFieldRef transport.NodeMeta go!"Next" ptr ↦{dq} mn ∗
      structFieldRef transport.NodeMeta go!"Tail" ptr ↦{dq} mtl ⊢
    (ptr ↦{dq} (transport.NodeMeta.mk mh mt mp mn mtl) : IProp GF) := by
  iintro ⟨H1, H2, H3, H4, H5⟩
  iapply typedPointsto_combine ptr _ dq hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- `Unlock` in wand form (for the macros below). -/
theorem wp_Unlock' (m : Loc) (R : IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync -∗ sync.isMutex m R -∗
      sync.ownMutex m -∗ ▷ R -∗ Φ #() -∗
      WP (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hpkg #Hm Hl HR HΦ
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hl $HR]
  iexact HΦ

set_option hygiene false in
/-- Branch "not the tail" (`m.isTail = false`), from `if becomesTail` on: connect to the successor,
then return. Expects the lock state's pieces `Hh Ht Hnbm Hlatm Hnbrs2 HS` (at `nbrs2 lat S1`, IsTail
false), `HlatS1`, the fence's result `Hfence`, the role halves `Hr Hrole`, the metadata's fields. -/
macro "upd_succ_F" : tactic => `(tactic| (
  wp_apply (wp_connectToSuccessor HL Hback cfg n a _ γs nbM latM mh false _ lat S1 mn Hmeta.2.1)
    $$ [Hh Ht Hnbm Hlatm HS] as %err3 ⟨%nbrs3, %lat3, %S3, Hls, %Hnext3⟩ Herr3
  · iframe; iframe #
    unfold lockedState tailRes
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe; iframe #
    ipureintro; exact ⟨HlatS1, trivial⟩
  icases Herr3 with (%Herr3 | #Herr3)
  · subst Herr3
    wp_auto
    iapply fupd_wp
    imod HL.roleHalf_update cfg.γ a _ _ ((false, mn) : Role) $$ [Hr Hrole] with ⟨Hr, Hrole⟩
    · iframe
    imodintro
    have Hn3 := Hnext3 rfl
    wp_apply wp_Unlock' $$ Hsync Hmu Hlocked [Hls Hrole]
    · unfold lockInv; iexists mh, false, nbrs3, lat3, S3; rw [Hn3]; iframe
    iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Hr Hfence]
    · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
    ileft
    isplitr
    · ipureintro; rfl
    unfold updPost
    simp only [_root_.true_and]
    iframe
  · ihave %Hok := errPlain_ok err3 $$ Herr3
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    iapply fupd_wp
    imod (relock HL cfg a γs n nbM latM mh false nbrs3 lat3 S3 _) $$ Hr Hrole Hls with Hli
    imodintro
    wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
    iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr3]
    · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
    iright; iexact Herr3))

set_option hygiene false in
/-- From `if becomesTail` on (it is false, or done), with the lock state `Hls` folded at IsTail
`tt`: connect to the successor, then return (`Hfence`: what updPost's second part needs). -/
macro "upd_succ " tt:term : tactic => `(tactic| (
  wp_apply (wp_connectToSuccessor HL Hback cfg n a _ γs nbM latM mh $tt _ _ _ mn Hmeta.2.1)
    $$ [Hls] as %err3 ⟨%nbrs3, %lat3, %S3, Hls, %Hnext3⟩ Herr3
  · iframe; iframe #
  icases Herr3 with (%Herr3 | #Herr3)
  · subst Herr3
    wp_auto
    iapply fupd_wp
    imod HL.roleHalf_update cfg.γ a _ _ (($tt, mn) : Role) $$ [Hr Hrole] with ⟨Hr, Hrole⟩
    · iframe
    imodintro
    have Hn3 := Hnext3 rfl
    wp_apply wp_Unlock' $$ Hsync Hmu Hlocked [Hls Hrole]
    · unfold lockInv; iexists mh, $tt, nbrs3, lat3, S3; rw [Hn3]; iframe
    iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Hr Hfence]
    · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
    ileft
    isplitr
    · ipureintro; rfl
    unfold updPost
    simp only [_root_.true_and, Bool.true_eq_false, _root_.false_and, ↓reduceIte]
    iframe
  · ihave %Hok := errPlain_ok err3 $$ Herr3
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    iapply fupd_wp
    imod (relock HL cfg a γs n nbM latM mh $tt nbrs3 lat3 S3 _) $$ Hr Hrole Hls with Hli
    imodintro
    wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
    iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr3]
    · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
    iright; iexact Herr3))

set_option hygiene false in
/-- The activation after the catch-up: the dirty items committed (each through the commit law),
their commits sent to the predecessor, then the successor. The lock state's pieces are at
IsTail `true`, latest map `latX`, store `SX` (`HX : ∀ k, latOf latX k = SX.maxCommitted k`). -/
macro "act_rest " latX:term:max SX:term:max HX:term:max : tactic => `(tactic| (
  wp_apply (wp_store_AllDirty_own γs e (1 : Qp).half $SX) $$ [Hstore HS] as %sld HS Hsld
  · iframe; iframe #
  wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
  rw [nbrAt_zero]
  ihave #Hprv := nbrAt_ok cfg nbrs1 (W64 0) $$ Hnbrs1
  rename_i ivar_ptr
  irename : (ivar_ptr ↦ (zero_val w64 : w64) : IProp GF) => ivar
  unfold itemsIn
  icases Hsld with ⟨%ps, %es, Hsl, %Hes, #Hps⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (j j' : w64) (lat2 : GMap GoString w64) (S2 : StoreS),
      "i" ∷ i_ptr ↦ j ∗ "ivar" ∷ ivar_ptr ↦ j' ∗
      "Hh" ∷ n.[node.Node, go!"IsHead"] ↦ mh ∗ "Ht" ∷ n.[node.Node, go!"IsTail"] ↦ true ∗
      "Hlatm" ∷ latM ↦$ lat2 ∗ "HS" ∷ storeOwn γs (1 : Qp).half S2 ∗
      "Htail" ∷ tailRes cfg true lat2 ∗
      "%HlatS2" ∷ ⌜∀ k, latOf lat2 k = S2.maxCommitted k⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (ps.length : Int)⌝) $$ [i ivar Hh Ht Hlatm HS Htail]
  · iexists _, _, $latX, $SX
    iframe
    ipureintro
    exact ⟨$HX, by word, by word⟩
  irename «meta» => Hmetacell
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < ps.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, ps[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_pures
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sld.len from ⟨Hj.1, Hif⟩, ↓reduceIte]
    wp_apply wp_load_slice_index sld (sint.Z j) ps (DFrac.own 1) p Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hp
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sld.len from ⟨Hj.1, Hif⟩, ↓reduceIte]
    wp_apply (lc := 1) wp_load_slice_index sld (sint.Z j) ps (DFrac.own 1) p Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hp
    ihave #Hip := BI.BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ e, ⌜es[i]? = some e⌝ ∗
        itemPtr (hG := hG) p e.1 e.2.1 e.2.2.1)) Hp $$ Hps
    icases Hip with ⟨%ent, %Hent, #Hip⟩
    ihave #Hip' := Hip
    unfold itemPtr
    icases Hip' with ⟨#Hk, #Hv, -⟩
    wp_auto
    wp_apply (wp_commitM HL cfg n a _ γs nbM latM mh true nbrs1 lat2 S2 ent.1 ent.2.1)
      $$ [Hh Ht Hnbm Hlatm HS Htail Hlc1] as %err Hres
    · iframe; iframe #
      isplitr [Hlc1]
      · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS2
      iright; iframe; ipureintro; rfl
    cases hv : S2.hasVer ent.1 ent.2.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hres with ⟨#Herr, Hls⟩
      ihave #Hem := errNotFound_errMsg err $$ Herr
      ihave %Hok := errMsg_ok err _ $$ Hem
      obtain ⟨ei, rfl⟩ := Hok
      wp_auto
      wp_log [interface.mkOk (go.GoType.PointerType store.Item.ty) #p, GoInterface.ok ei]
      · iapply argOks2
        isplitr
        · iapply argOk_item p ent.1 ent.2.1 ent.2.2.1; unfold itemPtr; iexact Hip
        iapply argOk_errPlain; iapply errNotFound_errPlain $$ Herr
      wp_for_post
      iunfold lockedState at Hls
      icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, -, HS, %HlatS3, Htail⟩
      iframe
      iexists _, _, lat2, S2
      iframe
      ipureintro
      exact ⟨HlatS3, by word, by word⟩
    · simp only [↓reduceIte]
      icases Hres with ⟨%Herr, %Hko, #Hcv, Hls⟩
      subst Herr
      wp_auto
      wp_apply wp_fork
      · wp_apply (Hsend cfg n a _ γs nbM latM (nbrAt nbrs1 (W64 0)) ent.1 ent.2.1 Hko) $$ []
        · iframe; iframe #
        iintro %err2
        itrivial
      wp_for_post
      iunfold lockedState at Hls
      icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, -, HS, %HlatS3, Htail⟩
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      exact ⟨HlatS3, by word, by word⟩
  · ihave Hls : lockedState cfg γs n nbM latM mh true nbrs1 lat2 S2 $$ [Hh Ht Hnbm Hlatm HS Htail]
    · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS2
    upd_succ true))

set_option hygiene false in
/-- The activation's catch-up from the source client `Hcl` (with `Hcov : covers γ ca L`), then
the rest; on failure, the error return. -/
macro "act_back " c:term:max ca:term:max : tactic => `(tactic| (
  wp_apply (Hback cfg n a _ γs nbM latM mh false nbrs1 lat S1 $c $ca L)
    $$ [Hh Ht Hnbm Hlatm HS Htail Hcov] as %err2 ⟨%lat', %S', Hls, -, %Hlb⟩ Herr2
  · iframe; iframe #
    unfold lockedState; iframe; iframe #; ipureintro; exact HlatS1
  icases Herr2 with (%Herr2 | #Herr2)
  · subst Herr2
    have Hlb' := Hlb rfl
    wp_auto
    iunfold lockedState at Hls
    icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, -, HS, %HlatS', -⟩
    wp_auto
    iapply fupd_wp
    imod (tail_ub HL cfg a γs L S') $$ Hinv HS HtokL with ⟨HS, HtokL, %Hub⟩
    imodintro
    have HlatL : ∀ k, latOf lat' k = cvOf L k := by
      intro k; have h1 := Hub k; have h2 := Hlb' k; rw [HlatS' k]; word
    ihave Htail : tailRes cfg true lat' $$ [HtokL]
    · unfold tailRes; simp only [↓reduceIte]; iexists L; iframe; ipureintro; exact HlatL
    act_rest lat' S' HlatS'
  · ihave %Hok := errPlain_ok err2 $$ Herr2
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    iapply fupd_wp
    imod (relock HL cfg a γs n nbM latM mh false nbrs1 lat' S' _) $$ Hr Hrole Hls with Hli
    imodintro
    wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
    iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr2]
    · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
    iright; iexact Herr2))

theorem wp_update (HL : Laws (GF := GF)) (Hsend : sendCommitToPrev.spec (GF := GF) (hG := hG))
    (Hfwd : requestFwdPropagation.spec (GF := GF) (hG := hG))
    (Hback : requestBackPropagation.spec (GF := GF) (hG := hG))
    (cfg : Cfg GF) (n : Loc) (a : GoString) (ptr : Loc) (dq0 : DFrac) (m : MetaV) (r : Role) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ isNode cfg n a ∗
        ⌜metaAddrsOk cfg.chain m⌝ ∗ metaPtr ptr dq0 m ∗ roleHalf cfg.γ a r ∗ updDep cfg.γ r m) -∗
      (∀ err : GoInterface, (∃ dq, metaPtr ptr dq m) -∗
        ((⌜err = interface.nil⌝ ∗ updPost cfg.γ a r m) ∨ models_lab.errPlain err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"update" #n)) (Val #ptr))
        {{ Φ }} := by
  -- the log call takes a part `dqL` of the metadata's points-to and gives back only some fraction
  -- (`argOk`'s `*NodeMeta` disjunct is existential in it), so the update keeps the part `dq`
  obtain ⟨dq, dqL, rfl⟩ := dfrac_halves dq0
  iintro %Φ ⟨#Hpkg, #Hn, %Hmeta, Hm, Hr, Hdep⟩ HΦ
  iunfold isNode at Hn
  icases Hn with ⟨#Hctx, %Ha, -, #Hn⟩
  iunfold isNodeDef at Hn
  icases Hn with ⟨%st, %γs, %nbM, %latM, #Hf⟩
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  ihave #Hctx' := Hctx
  iunfold craqCtx at Hctx'
  icases Hctx' with ⟨-, %Hcc, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  obtain ⟨mh, mt, mp, mn, mtl⟩ := m
  unfold metaPtr
  simp only at Hmeta ⊢
  wp_method_call
  wp_call
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  icases (typedPointsto_dfractional ptr _).dfractional dq dqL $$ Hm with ⟨Hm, HmL⟩
  ihave Hok := argOks1 _ $$ [HmL]
  · iapply argOk_meta $$ HmL
  wp_log_ok [interface.mkOk (go.GoType.PointerType transport.NodeMeta.ty) #ptr]
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] with ⟨Hlocked, Hlk⟩
  iunfold lockInv at Hlk
  icases Hlk with ⟨%h, %t, %nbrs, %lat, %S, Hls, Hrole⟩
  iunfold lockedState at Hls
  icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  ihave %Hreq := HL.roleHalf_agree cfg.γ a r _ $$ [Hr Hrole]
  · iframe
  subst Hreq
  ihave %Hnn := typedPointsto_not_null ptr _ dq $$ Hm
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨IsHead, IsTail, Prev, Next, Tail, -⟩
  wp_auto
  cases mt
  · -- not the tail: fence if it was
    wp_auto
    iapply fupd_wp
    ihave Hfn : (|={⊤}=> storeOwn γs (1 : Qp).half S ∗
        (if t then iprop(∃ L : CLog, tailTok cfg.γ L ∗ covers cfg.γ a L) else iprop(True))) $$ [HS Htail]
    · cases t
      · imodintro; iframe
        simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte]
        iapply fence_shift HL cfg a γs lat S HlatS $$ Hinv HS Htail
    imod Hfn with ⟨HS, Hfence⟩
    imodintro
    wp_apply (wp_connectToPredecessor Hfwd cfg n a _ γs nbM latM mh false nbrs lat S mp Hmeta.1)
      $$ [Hh Ht Hnbm Hlatm HS] as %err1 ⟨%nbrs1, %S1, Hls, %Hnext1, %Hprev1⟩ Herr1
    · iframe; iframe #
      unfold lockedState tailRes
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe; iframe #
      ipureintro; exact ⟨HlatS, trivial⟩
    icases Herr1 with (%Herr1 | #Herr1)
    · subst Herr1
      wp_auto
      iunfold lockedState at Hls
      icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs1, HS, %HlatS1, -⟩
      wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
      rw [nbrAt_zero]
      by_cases hta : (nbrAt nbrs1 (W64 2)).address' = mtl
      · simp only [hta, _root_.decide_true, Bool.not_true]
        wp_auto
        upd_succ_F
      · simp only [hta, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_if_destruct
        · upd_succ_F
        · -- connect to the tail
          have hmtl : mtl ∈ cfg.chain := by
            rcases List.mem_cons.1 Hmeta.2.2 with h' | h'
            · exact absurd h' Hif
            · exact h'
          wp_apply wp_connectToNode cfg n a _ γs nbM latM nbrs1 mtl (W64 2) (by simp)
            $$ [$Hpkg $Hf $Hnbm $Hnbrs1] as %err2 Hres2
          · ipureintro; exact hmtl
          icases Hres2 with (⟨%Herr2, %c2, Hnbm, #Hnbrs2, -⟩ | ⟨#Herr2, Hnbm, -⟩)
          · subst Herr2
            wp_auto
            upd_succ_F
          · ihave %Hok := errPlain_ok err2 $$ Herr2
            obtain ⟨ei, rfl⟩ := Hok
            wp_auto
            iapply fupd_wp
            imod (relock HL cfg a γs n nbM latM mh false nbrs1 lat S1 _) $$ Hr Hrole [Hh Ht Hnbm Hlatm HS]
              with Hli
            · unfold lockedState tailRes
              simp only [Bool.false_eq_true, ↓reduceIte]
              iframe; iframe #
              ipureintro; exact ⟨HlatS1, trivial⟩
            imodintro
            wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
            iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr2]
            · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
            iright; iexact Herr2
    · ihave %Hok := errPlain_ok err1 $$ Herr1
      obtain ⟨ei, rfl⟩ := Hok
      wp_auto
      iapply fupd_wp
      imod (relock HL cfg a γs n nbM latM mh false nbrs1 lat S1 _) $$ Hr Hrole Hls with Hli
      imodintro
      wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
      iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr1]
      · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
      iright; iexact Herr1
  · wp_auto
    cases t
    · -- activation
      simp only [Bool.not_false]
      ihave Hfence : (True : IProp GF) $$ []
      · itrivial
      unfold updDep
      simp only [_root_.true_and, ↓reduceIte]
      icases Hdep with ⟨%L, HtokL, Hsrc⟩
      wp_apply (wp_connectToPredecessor Hfwd cfg n a _ γs nbM latM mh false nbrs lat S mp Hmeta.1)
        $$ [Hh Ht Hnbm Hlatm HS Htail] as %err1 ⟨%nbrs1, %S1, Hls, %Hnext1, %Hprev1⟩ Herr1
      · iframe; iframe #
        unfold lockedState
        iframe; iframe #
        ipureintro; exact HlatS
      icases Herr1 with (%Herr1 | #Herr1)
      · subst Herr1
        have Hprev1' := Hprev1 rfl
        wp_auto
        iunfold lockedState at Hls
        icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs1, HS, %HlatS1, Htail⟩
        wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
        wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
        rw [nbrAt_zero]
        ihave #HN := nbrAt_ok cfg nbrs1 (W64 1) $$ Hnbrs1
        have hN : (nbrAt nbrs1 (W64 1)).address' = nextAddr nbrs := by rw [Hnext1]; rfl
        generalize nbrAt nbrs1 (W64 1) = nbN at hN ⊢
        obtain ⟨rpcN, addrN⟩ := nbN
        simp only at hN
        iunfold nbrOk at HN
        icases HN with (%HnilN | #HcN)
        · -- no successor: the source is the new predecessor
          obtain ⟨h1, h2⟩ := HnilN
          simp only at h1 h2
          subst h1 h2
          rw [← hN]
          unfold srcOk
          simp only [↓reduceIte]
          wp_auto
          wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
          rw [nbrAt_zero]
          ihave #HP := nbrAt_ok cfg nbrs1 (W64 0) $$ Hnbrs1
          generalize nbrAt nbrs1 (W64 0) = nbP at Hprev1' ⊢
          obtain ⟨rpcP, addrP⟩ := nbP
          simp only at Hprev1'
          subst Hprev1'
          iunfold nbrOk at HP
          icases HP with (%HnilP | #HcP)
          · -- no source: nothing is committed
            obtain ⟨h1, h2⟩ := HnilP
            simp only at h1 h2
            subst h1 h2
            simp only [↓reduceIte]
            icases Hsrc with %Hsrc
            wp_auto
            iapply fupd_wp
            imod (tail_ub HL cfg a γs L S1) $$ Hinv HS HtokL with ⟨HS, HtokL, %Hub⟩
            imodintro
            have HlatL : ∀ k, latOf lat k = cvOf L k := by
              intro k; have h1 := Hub k; rw [Hsrc k] at h1 ⊢; rw [HlatS1 k]; word
            ihave Htail : tailRes cfg true lat $$ [HtokL]
            · unfold tailRes; simp only [↓reduceIte]; iexists L; iframe; ipureintro; exact HlatL
            act_rest lat S1 HlatS1
          · -- the new predecessor (the tail it joins after) is the source
            ihave #HcP' := HcP
            iunfold isNodeClient at HcP'
            icases HcP' with ⟨%eP, ⟨%HeP, %HaP⟩, -⟩
            simp only at HeP HaP
            subst HeP
            have hne : addrP ≠ go!"" := fun h => Hcc.2.2.2.1 (h ▸ HaP)
            simp only [hne, ↓reduceIte]
            irename Hsrc => Hcov
            wp_auto
            act_back (GoInterface.ok eP) addrP
        · -- the successor (the removed tail) is the source
          ihave #HcN' := HcN
          iunfold isNodeClient at HcN'
          icases HcN' with ⟨%eN, ⟨%HeN, %HaN⟩, -⟩
          simp only at HeN HaN
          subst HeN
          have hne : addrN ≠ go!"" := fun h => Hcc.2.2.2.1 (h ▸ HaN)
          rw [← hN]
          unfold srcOk
          simp only [hne, ↓reduceIte]
          irename Hsrc => Hcov
          wp_auto
          act_back (GoInterface.ok eN) addrN
      · ihave %Hok := errPlain_ok err1 $$ Herr1
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        iapply fupd_wp
        imod (relock HL cfg a γs n nbM latM mh false nbrs1 lat S1 _) $$ Hr Hrole Hls with Hli
        imodintro
        wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
        iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr1]
        · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
        iright; iexact Herr1
    · -- already the active tail
      simp only [Bool.not_true]
      ihave Hfence : (True : IProp GF) $$ []
      · itrivial
      wp_apply (wp_connectToPredecessor Hfwd cfg n a _ γs nbM latM mh true nbrs lat S mp Hmeta.1)
        $$ [Hh Ht Hnbm Hlatm HS Htail] as %err1 ⟨%nbrs1, %S1, Hls, %Hnext1, %Hprev1⟩ Herr1
      · iframe; iframe #
        unfold lockedState
        iframe; iframe #
        ipureintro; exact HlatS
      icases Herr1 with (%Herr1 | #Herr1)
      · subst Herr1
        wp_auto
        iunfold lockedState at Hls
        icases Hls with ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs1, HS, %HlatS1, Htail⟩
        wp_apply wp_map_lookup1 $$ Hnbm with Hnbm
        ihave Hls : lockedState cfg γs n nbM latM mh true nbrs1 lat S1 $$ [Hh Ht Hnbm Hlatm HS Htail]
        · unfold lockedState; iframe; iframe #; ipureintro; exact HlatS1
        upd_succ true
      · ihave %Hok := errPlain_ok err1 $$ Herr1
        obtain ⟨ei, rfl⟩ := Hok
        wp_auto
        iapply fupd_wp
        imod (relock HL cfg a γs n nbM latM mh true nbrs1 lat S1 _) $$ Hr Hrole Hls with Hli
        imodintro
        wp_apply wp_Unlock' $$ Hsync Hmu Hlocked Hli
        iapply HΦ $$ [IsHead IsTail Prev Next Tail] [Herr1]
        · iexists dq; iapply metaPtr_join ptr dq _ _ _ _ _ Hnn; iframe
        iright; iexact Herr1

end update

end NodeP

end github_com.despreston.go_craq

end Perennial
