/-
`cdr.AddNode(address)`: the new node is connected, the last replica fenced (its token and cover
come back), the new node appended and activated from it, the others told the new tail.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Reps
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Log

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- `n.Connect()`. -/
theorem wp_node_Connect (cfg : Cfg GF) (n : Loc) (cl : GoInterface) (a : GoString) (b : Bool)
    (ha : a ∈ cfg.chain) :
    {{ structFieldRef coordinator.node go!"rpc" n ↦ cl ∗
        structFieldRef coordinator.node go!"address" n ↦ a ∗
        structFieldRef coordinator.node go!"connected" n ↦ b ∗ freshNodeClient cfg cl }}
      (App (Val (n @!! go.GoType.PointerType coordinator.node.ty @!! go!"Connect")) (Val #()))
    {{ (err : GoInterface), RET #err;
        structFieldRef coordinator.node go!"rpc" n ↦ cl ∗
        structFieldRef coordinator.node go!"address" n ↦ a ∗
        structFieldRef coordinator.node go!"connected" n ↦ decide (err = interface.nil) ∗
        ((⌜err = interface.nil⌝ ∗ isNodeClient cfg cl a) ∨ models_lab.errAny err) }} := by
  wp_start as ⟨Hrpc, Haddr, Hconn, Hfresh⟩
  unfold freshNodeClient
  icases Hfresh with ⟨%e, %He, HC⟩
  subst He
  wp_auto
  wp_apply HC $$ %a %_ %ha as %err Hres
  icases Hres with (⟨%Hnil, #Hcl⟩ | #Hany)
  · subst Hnil
    wp_auto
    iapply HΦ
    rw [decide_eq_true rfl]
    iframe
    ileft; iframe Hcl; ipureintro; rfl
  · ihave %Hne := models_lab.errAny_ne_nil $$ Hany
    obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    iapply HΦ
    rw [decide_eq_false Hne]
    iframe
    iright; iexact Hany

/-- A join ticket claims its address's role half `(false, "")` (the address is not a replica),
leaving the ticket in its place. -/
theorem join_claim (cfg : Cfg GF) (rs : List Rep) (a : GoString) (ha : a ∈ cfg.chain)
    (hnd : cfg.chain.Nodup) :
    ([∗list] b ∈ cfg.chain, joinRes (hG := hG) cfg rs b) ∗ joinTicket cfg.γ a ⊢
      ⌜a ∉ rs.map Rep.addr⌝ ∗ roleHalf cfg.γ a ((false, go!"") : Role) ∗
      ∀ rs' : List Rep, ⌜∀ b, b ∈ rs'.map Rep.addr → b = a ∨ b ∈ rs.map Rep.addr⌝ -∗
        [∗list] b ∈ cfg.chain, joinRes cfg rs' b := by
  iintro ⟨Hj, Ht⟩
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
  have hl : cfg.chain[i]? = some a := by rw [List.getElem?_eq_getElem hi, hia]
  ihave ⟨Ha, Hrest⟩ := BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ b => joinRes (hG := hG) cfg rs b) hl
    $$ Hj
  unfold joinRes
  icases Ha with (Ht' | ⟨%Hn, Hr⟩)
  · iexfalso
    unfold joinTicket
    iapply token_exclusive $$ Ht Ht'
  iframe Hr
  isplitr
  · ipureintro; exact Hn
  iintro %rs' %Hsub
  iapply Hrest
  · imodintro
    iintro %k %y %hk %hki Hy
    icases Hy with (Ht'' | ⟨%Hn', Hr'⟩)
    · ileft; iexact Ht''
    · iright; iframe Hr'
      ipureintro
      intro hm
      rcases Hsub y hm with h | h
      · apply hki
        subst h
        rw [List.getElem?_eq_some_iff] at hk
        obtain ⟨hk1, hk2⟩ := hk
        exact (List.Nodup.getElem_inj hnd).mp (hk2.trans hia.symm)
      · exact Hn' h
  · ileft; iexact Ht

theorem wp_addNode (cfg : Cfg GF) (c : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        isCoord cfg c ∗ joinTicket cfg.γ a }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"addNode")) (Val #a))
    {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
        (⌜err = interface.nil⌝ ∗ ∃ m : MetaV, metaPtr p (DFrac.own 1) m) ∨ models_lab.errAny err }} := by
  wp_start as ⟨#Hc, Hticket⟩
  unfold isCoord coordDef
  icases Hc with ⟨#Hctx, -, %Hbound, %f, #Htport, #Hfac, #Hmu⟩
  ihave ⟨#HerrE, #HerrL, #HerrD, #HerrV⟩ := coord_pkg_errs $$ Hpkg
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [interface.mkOk go.string #a]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args_sl ⟨Hargs, -⟩
  wp_apply log.Printf.wp_proof _ _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hargs]
  · iframe
  iintro -
  wp_auto
  ihave #Htime := coord_time_init $$ Hpkg
  wp_apply time.wp_Now $$ [$Htime] as %tnow -
  unfold isFactory
  wp_apply Hfac as %cl Hfresh
  generalize hnp : «$r0_ptr» = np
  iStructNamed «$r0»
  wp_apply wp_node_Connect cfg np cl a false ha $$ [rpc address connected Hfresh]
    as %errC ⟨Hrpc, Haddr, Hconn, HresC⟩
  · iframe
  icases HresC with (⟨%HerrC, #Hcl⟩ | #HerrC)
  · subst HerrC
    rw [decide_eq_true rfl]
    ipersist Hrpc
    ipersist Haddr
    ihave #HnfN : nodeFacts cfg np a $$ []
    · unfold nodeFacts; iframe Haddr; iexists cl; iframe Hrpc Hcl
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    iNamed Hlk
    unfold craqCtx
    icases Hctx with ⟨-, %Hctxp, -⟩
    ihave ⟨%Hnotin, HroleA, Hjoin⟩ := join_claim cfg rs a ha Hctxp.2.1 $$ [Hjoin Hticket]
    · iframe
    wp_auto
    rcases List.eq_nil_or_concat rs with rfl | ⟨pre, rL, rfl⟩
    · -- the first replica
      ihave %Hlen := ownSlice_len $$ Hsl
      simp only [List.map_nil, List.length_nil] at Hlen
      have hl0 : ¬ sint.Z (W64 0) < sint.Z sl.len := by word
      rw [decide_eq_false hl0]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.PointerType coordinator.node.ty)))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := Loc) (t := go.PointerType coordinator.node.ty) [np]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %nsl ⟨Hnsl, -⟩
      wp_apply wp_slice_append sl _ _ [np] (DFrac.own 1) $$ [Hsl Hcap Hnsl] as %sl' ⟨Hsl, Hcap, -⟩
      · iframe
      ihave %Hlen' := ownSlice_len $$ Hsl
      simp only [List.map_nil, List.nil_append, List.length_singleton] at Hlen'
      have hl1 : sl'.len = W64 1 := by word
      rw [decide_eq_true hl1]
      wp_auto
      -- the new node is activated, from no source (nothing committed)
      let N : Rep := ⟨np, a, true⟩
      have hN0 : [N][sint.nat (sl'.len - W64 1)]? = some N := by rw [hl1]; rfl
      have hm0 : metaOf [N] (sint.nat (sl'.len - W64 1)) = ⟨true, true, go!"", go!"", a⟩ := by
        rw [hl1]; rfl
      wp_apply wp_updateNode cfg c sl' [N] (DFrac.own 1) (sl'.len - W64 1) N true ((false, go!"") : Role)
        (by word) hN0 (by intro r hr; simp at hr; subst hr; exact ha)
        $$ [Hreplicas Hsl Hconn HroleA Htok] as %errN ⟨Hreplicas, Hsl, %bN, Hconn, HNpost⟩
      · iframe Hreplicas Hconn
        isplitl [Hsl]
        · iExactEq Hsl; rfl
        isplitr
        · iapply BigSepL.bigSepL_singleton.2; iexact HnfN
        unfold sendPre
        simp only [↓reduceIte]
        iframe HroleA
        rw [hm0]
        unfold updDep
        simp only [↓reduceIte, _root_.and_self]
        iexists []
        iframe Htok
        unfold srcOk
        simp only [↓reduceIte]
        ipureintro
        intro k; rfl
      unfold sendPost
      icases HNpost with (⟨%Hok, HNpost⟩ | ⟨%HbN, #HerrN⟩)
      · obtain ⟨rfl, -, rfl⟩ := Hok
        unfold updPost
        icases HNpost with ⟨HNr, -⟩
        rw [hm0]
        wp_auto
        wp_apply wp_updateAll cfg c sl' [N] (sl'.len - W64 1) ⟨by word, by rw [hl1]; rfl⟩ (by simp)
          (by intro r hr; simp at hr; subst hr; exact ha) $$ [Hreplicas Hsl] as ⟨Hreplicas, Hsl, -⟩
        · iframe
          isplitr
          · iapply BigSepL.bigSepL_singleton.2; iexact HnfN
          iapply BigSepL.bigSepL_singleton.2
          unfold inF; rw [if_pos (show 0 + 1 = [N].length from rfl)]; itrivial
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
          Hconn HNr Hjoin]
        · inext
          iapply coordLock_pack cfg c sl' [N] ver np np
            ⟨by simp, by intro r hr; simp at hr; subst hr; exact ha⟩
          iframe Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
          isplitr
          · imodintro; iapply BigSepL.bigSepL_singleton.2; iexact HnfN
          isplitl [Hconn HNr]
          · iapply BigSepL.bigSepL_singleton.2
            iapply (connRole_last cfg [N] 0 N rfl).2
            iframe Hconn
            simp only [N, ↓reduceIte]
            iexact HNr
          isplitl [Hjoin]
          · iapply Hjoin
            ipureintro
            intro b hb; simp at hb; left; exact hb
          rw [if_neg (by simp)]; itrivial
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists ⟨_, _, _, _, _⟩
        unfold metaPtr
        iassumption
      · subst HbN
        ihave %Hne := models_lab.errAny_ne_nil $$ HerrN
        obtain ⟨ie, rfl⟩ : ∃ ie, errN = GoInterface.ok ie := by
          cases errN with
          | nil => exact absurd rfl Hne
          | ok i => exact ⟨i, rfl⟩
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
          [interface.mkOk go.string #a, GoInterface.ok ie]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %args_sl ⟨Hargs, -⟩
        wp_apply wp_Printf_args _ _ [interface.mkOk go.string #a, GoInterface.ok ie] _ $$ [Hargs]
        · iframe Hargs
          iapply BigSepL.bigSepL_cons.2
          isplitr
          · iapply logArg_str
          iapply BigSepL.bigSepL_cons.2
          isplitr
          · iapply logArg_err $$ HerrN
          iapply BigSepL.bigSepL_nil.2; iempintro
        iintro -
        wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
          Hconn Hjoin]
        · inext
          iapply coordLock_pack cfg c sl' [⟨np, a, false⟩] ver np np
            ⟨by simp, by intro r hr; simp at hr; subst hr; exact ha⟩
          iframe Hreplicas Hcap Hversion Hnext Hhead Htail
          isplitl [Hsl]
          · iExactEq Hsl; rfl
          isplitr
          · imodintro; iapply BigSepL.bigSepL_singleton.2; iexact HnfN
          isplitl [Hconn]
          · iapply BigSepL.bigSepL_singleton.2
            iapply connRole_disc cfg _ _ ⟨np, a, false⟩ rfl $$ Hconn
          isplitl [Hjoin]
          · iapply Hjoin
            ipureintro
            intro b hb; simp at hb; left; exact hb
          rw [if_neg (by simp)]; itrivial
        iapply HΦ
        iright; iexact HerrN
    · -- a new tail after `rL`
      rw [List.concat_eq_append] at *
      ihave %Hlen := ownSlice_len $$ Hsl
      simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_map,
        List.length_singleton] at Hlen
      have hl0 : sint.Z (W64 0) < sint.Z sl.len := by word
      rw [decide_eq_true hl0]
      wp_auto
      have hlast : sint.nat (sl.len - W64 1) = pre.length := by word
      have hrL : (pre ++ [rL])[pre.length]? = some rL := by simp
      wp_join iprop(∃ p : GoString,
          structFieldRef coordinator.Coordinator go!"replicas" c ↦ sl ∗
          sl ↦* (pre ++ [rL]).map Rep.loc ∗ cdr_ptr ↦ c ∗ last_ptr ↦ (sl.len - W64 1) ∗
          meta_ptr ↦ transport.NodeMeta.mk (decide (sl.len - W64 1 = W64 0)) false p a a ∗
          ⌜p = if 0 < pre.length then addrAt (pre ++ [rL]) (pre.length - 1) else go!""⌝)
        with [Hreplicas Hsl cdr last «meta»] as ⟨%p, Hreplicas, Hsl, cdr, last, «meta», %Hp⟩
      · list_elem (pre ++ [rL]) (pre.length - 1) as rp
        ihave #Hnfp := nodeFacts_at cfg _ _ rp Hrp_lookup $$ Hnfs
        have hb : 0 ≤ sint.Z (sl.len - W64 1 - W64 1) ∧ sint.Z (sl.len - W64 1 - W64 1) < sint.Z sl.len := by
          constructor <;> word
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1 - W64 1)) _ (DFrac.own 1) rp.loc hb.1
          $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro
          rw [show (sint.Z (sl.len - W64 1 - W64 1)).toNat = pre.length - 1 by word]
          exact locs_at _ _ rp Hrp_lookup
        wp_apply wp_node_Address' cfg rp.loc rp.addr $$ Hnfp
        wp_join_done
        iexists _
        iframe
        ipureintro
        rw [if_pos (by word), addrAt_of_getElem Hrp_lookup]
      · iexists _
        iframe
        ipureintro
        rw [if_neg (by word)]
        rfl
      -- the fence: `rL` stops acting as the tail, its successor the new node
      ihave ⟨Hpre, HL⟩ := BigSepL.bigSepL_snoc.1 $$ Hreps
      ihave ⟨HLc, HLr⟩ := (connRole_last cfg (pre ++ [rL]) pre.length rL (by simp)).1 $$ HL
      ihave #HnfL := nodeFacts_at cfg _ _ rL hrL $$ Hnfs
      have hb : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := ⟨by word, by word⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) _ (DFrac.own 1) rL.loc hb.1 $$ [Hsl] as Hsl
      · iframe Hsl; ipureintro
        rw [show (sint.Z (sl.len - W64 1)).toNat = pre.length by word]
        exact locs_at _ _ rL hrL
      have hrLa : rL.addr ∈ cfg.chain := Hwf.2 rL (by simp)
      have hpch : p ∈ go!"" :: cfg.chain := by
        rw [Hp]; split
        · exact addrAt_mem _ _ cfg.chain Hwf.2
        · simp
      ihave Hm : metaPtr meta_ptr (DFrac.own 1) ⟨decide (sl.len - W64 1 = W64 0), false, p, a, a⟩ $$ [«meta»]
      · unfold metaPtr; iexact «meta»
      wp_apply wp_sendMeta cfg c rL.loc meta_ptr rL.addr rL.conn (DFrac.own 1)
        ⟨decide (sl.len - W64 1 = W64 0), false, p, a, a⟩ ((true, go!"") : Role) $$ [HnfL HLc Hm HLr]
        as %errL ⟨%bL, HLc, HLpost⟩
      · iframe HnfL HLc Hm
        isplitr
        · ipureintro; exact ⟨hpch, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ ha⟩
        unfold sendPre
        cases rL.conn
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · simp only [↓reduceIte]; iframe HLr; unfold updDep
          simp only [Bool.false_eq_true, false_and, ↓reduceIte]; itrivial
      unfold sendPost
      icases HLpost with (⟨%Hok, HLpost⟩ | ⟨%HbL, #HerrL⟩)
      · -- fenced: the token and `rL`'s cover
        obtain ⟨rfl, hLc, rfl⟩ := Hok
        unfold updPost
        simp only [true_and, ↓reduceIte]
        icases HLpost with ⟨HLr, %L, Htok', #Hcov⟩
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.PointerType coordinator.node.ty)))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := Loc) (t := go.PointerType coordinator.node.ty) [np]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        wp_apply wp_slice_append sl _ _ [np] (DFrac.own 1) $$ [Hsl Hcap Hnsl] as %sl' ⟨Hsl, Hcap, -⟩
        · iframe
        ihave %Hlen' := ownSlice_len $$ Hsl
        simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_map,
          List.length_singleton] at Hlen'
        have hl1 : ¬ sl'.len = W64 1 := by intro h; rw [h] at Hlen'; have := Hlen'.1; word
        rw [decide_eq_false hl1]
        wp_auto
        have hb2 : 0 ≤ sint.Z (sl'.len - W64 2) ∧ sint.Z (sl'.len - W64 2) < sint.Z sl'.len := ⟨by word, by word⟩
        simp only [hb2, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sl' (sint.Z (sl'.len - W64 2)) _ (DFrac.own 1) rL.loc hb2.1
          $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro
          rw [show (sint.Z (sl'.len - W64 2)).toNat = pre.length by word]
          simp
        wp_apply wp_node_Address' cfg rL.loc rL.addr $$ HnfL
        -- the new node is activated from `rL`
        let N : Rep := ⟨np, a, true⟩
        have hN : (pre ++ [rL] ++ [N])[sint.nat (sl'.len - W64 1)]? = some N := by
          rw [show sint.nat (sl'.len - W64 1) = pre.length + 1 by word]; simp
        have hmN : metaOf (pre ++ [rL] ++ [N]) (sint.nat (sl'.len - W64 1)) =
            ⟨false, true, rL.addr, go!"", a⟩ := by
          rw [show sint.nat (sl'.len - W64 1) = pre.length + 1 by word]
          simp [metaOf, addrAt, N]
        have hch1 : ∀ r ∈ pre ++ [rL] ++ [N], r.addr ∈ cfg.chain := by
          intro r hr
          rcases List.mem_append.mp hr with h | h
          · exact Hwf.2 r h
          · simp at h; subst h; exact ha
        have hLne : rL.addr ≠ go!"" := by intro h; apply Hctxp.2.2.2; rw [← h]; exact hrLa
        ihave #HnfsN : [∗list] r ∈ pre ++ [rL] ++ [N], nodeFacts cfg r.loc r.addr $$ []
        · iapply BigSepL.bigSepL_snoc.2; iframe Hnfs; iexact HnfN
        wp_apply wp_updateNode cfg c sl' (pre ++ [rL] ++ [N]) (DFrac.own 1) (sl'.len - W64 1) N true
          ((false, go!"") : Role) (by word) hN hch1
          $$ [Hreplicas Hsl Hconn HroleA Htok'] as %errN ⟨Hreplicas, Hsl, %bN, Hconn, HNpost⟩
        · iframe Hreplicas Hconn
          isplitl [Hsl]
          · iExactEq Hsl; simp [N]
          isplitr
          · iexact HnfsN
          unfold sendPre
          simp only [↓reduceIte]
          iframe HroleA
          rw [hmN]
          unfold updDep
          simp only [↓reduceIte, _root_.and_self]
          iexists L
          iframe Htok'
          unfold srcOk
          rw [if_neg hLne]
          iexact Hcov
        rw [hmN]
        have hwfF : ∀ pre' : List Rep, pre'.map Rep.addr = (pre ++ [rL]).map Rep.addr →
            repsWf cfg (pre' ++ [N]) := by
          intro pre' hpa
          refine ⟨?_, ?_⟩
          · rw [List.map_append, hpa, List.nodup_append]
            refine ⟨Hwf.1, by simp, ?_⟩
            intro x hx y hy; simp at hy; subst hy; intro h; subst h; exact Hnotin hx
          · intro r hr
            rcases List.mem_append.mp hr with h | h
            · have : r.addr ∈ pre'.map Rep.addr := List.mem_map_of_mem h
              rw [hpa] at this
              obtain ⟨r0, hr0, he⟩ := List.mem_map.mp this
              rw [← he]; exact Hwf.2 r0 hr0
            · simp at h; subst h; exact ha
        unfold sendPost
        icases HNpost with (⟨%Hok, HNpost⟩ | ⟨%HbN, #HerrN⟩)
        · obtain ⟨rfl, -, rfl⟩ := Hok
          unfold updPost
          icases HNpost with ⟨HNr, -⟩
          wp_auto
          ihave Hin := reps_inF cfg (pre ++ [rL]) N $$ [Hpre HLc HLr]
          · iapply BigSepL.bigSepL_snoc.2
            isplitl [Hpre]
            · iapply BigSepL.bigSepL_mono _ $$ Hpre
              intro j r hj
              have hl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
              exact connRole_updIn cfg (pre ++ [rL]) j r (by simp; omega)
            · unfold updIn
              rw [hLc]
              iframe HLc
              simp only [↓reduceIte]
              iexists a; iexact HLr
          have hlenle := reps_length_le cfg _ (hwfF (pre ++ [rL]) rfl)
          wp_apply wp_updateAll cfg c sl' (pre ++ [rL] ++ [N]) (sl'.len - W64 1)
            ⟨by word, by rw [show sint.nat (sl'.len - W64 1) = pre.length + 1 by word]; simp⟩
            (by simp at hlenle ⊢; omega) hch1 $$ [Hreplicas Hsl Hin] as ⟨Hreplicas, Hsl, Hout⟩
          · iframe; iexact HnfsN
          ihave ⟨%pre', %Hm, Hreps⟩ := reps_final cfg (pre ++ [rL]) N $$ [Hout Hconn HNr]
          · iframe Hout Hconn
            simp only [N, ↓reduceIte]
            iexact HNr
          ihave #HnfsF := nodeFacts_of_map cfg (pre ++ [rL] ++ [N]) (pre' ++ [N])
            (by simp [Hm.1]) (by simp [Hm.2]) $$ HnfsN
          ihave Hjoin := Hjoin $$ %(pre' ++ [N]) %(fun b hb => by
            rw [List.map_append, Hm.2] at hb
            rcases List.mem_append.mp hb with h | h
            · exact Or.inr h
            · simp at h; exact Or.inl h)
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
            Hreps Hjoin]
          · inext
            iapply coordLock_pack cfg c sl' (pre' ++ [N]) ver hd np (hwfF pre' Hm.2)
            iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
            isplitl [Hsl]
            · iExactEq Hsl; simp [Hm.1]
            isplitr
            · iexact HnfsF
            rw [if_neg (by simp)]; itrivial
          iapply HΦ
          ileft
          isplitr
          · ipureintro; rfl
          iexists ⟨_, _, _, _, _⟩
          unfold metaPtr
          iassumption
        · -- the new node's activation failed: it is disconnected
          subst HbN
          ihave %Hne := models_lab.errAny_ne_nil $$ HerrN
          obtain ⟨ie, rfl⟩ : ∃ ie, errN = GoInterface.ok ie := by
            cases errN with
            | nil => exact absurd rfl Hne
            | ok i => exact ⟨i, rfl⟩
          wp_auto
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
            [interface.mkOk go.string #a, GoInterface.ok ie]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %args_sl ⟨Hargs, -⟩
          wp_apply wp_Printf_args _ _ [interface.mkOk go.string #a, GoInterface.ok ie] _ $$ [Hargs]
          · iframe Hargs
            iapply BigSepL.bigSepL_cons.2
            isplitr
            · iapply logArg_str
            iapply BigSepL.bigSepL_cons.2
            isplitr
            · iapply logArg_err $$ HerrN
            iapply BigSepL.bigSepL_nil.2; iempintro
          iintro -
          wp_auto
          let N' : Rep := ⟨np, a, false⟩
          ihave Hreps : [∗list] j ↦ x ∈ pre ++ [rL] ++ [N'], connRole cfg (pre ++ [rL] ++ [N']) j x
            $$ [Hpre HLc HLr Hconn]
          · iapply BigSepL.bigSepL_snoc.2
            isplitl [Hpre HLc HLr]
            · iapply BigSepL.bigSepL_snoc.2
              isplitl [Hpre]
              · iapply BigSepL.bigSepL_mono _ $$ Hpre
                intro j r hj
                have hl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
                apply connRole_mono2 cfg r
                · simp; omega
                · intro r' hr' hc
                  refine ⟨r', ?_, hc, rfl⟩
                  rw [List.getElem?_append_left (by simp; omega)] at hr'
                  exact hr'
              · unfold connRole roleRes
                rw [hLc]
                iframe HLc
                simp only [↓reduceIte]
                iexists a
                have hd : decide (pre.length + 1 = (pre ++ [rL] ++ [N']).length) = false := by simp
                rw [hd]
                iframe HLr
                ipureintro
                refine ⟨fun h => by simp at h, fun r' hr' _ => ?_⟩
                have : (pre ++ [rL] ++ [N'])[pre.length + 1]? = some N' := by simp
                rw [this] at hr'; cases hr'; rfl
            · iapply connRole_disc cfg _ _ N' rfl $$ Hconn
          ihave #HnfsE := nodeFacts_of_map cfg (pre ++ [rL] ++ [N]) (pre ++ [rL] ++ [N'])
            (by simp [N, N']) (by simp [N, N']) $$ HnfsN
          ihave Hjoin := Hjoin $$ %(pre ++ [rL] ++ [N']) %(fun b hb => by
            rw [List.map_append] at hb
            rcases List.mem_append.mp hb with h | h
            · exact Or.inr h
            · simp [N'] at h; exact Or.inl h)
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
            Hreps Hjoin]
          · inext
            iapply coordLock_pack cfg c sl' (pre ++ [rL] ++ [N']) ver hd np
              (hwfF (pre ++ [rL]) rfl |>.casesOn fun h1 h2 => ⟨by simpa [N, N'] using h1,
                fun r hr => by
                  rcases List.mem_append.mp hr with h | h
                  · exact Hwf.2 r h
                  · simp [N'] at h; subst h; exact ha⟩)
            iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
            isplitl [Hsl]
            · iExactEq Hsl; simp [N, N']
            isplitr
            · iexact HnfsE
            rw [if_neg (by simp)]; itrivial
          iapply HΦ
          iright; iexact HerrN
      · -- the fence failed: `rL` is disconnected
        subst HbL
        ihave %Hne := models_lab.errAny_ne_nil $$ HerrL
        obtain ⟨ie, rfl⟩ : ∃ ie, errL = GoInterface.ok ie := by
          cases errL with
          | nil => exact absurd rfl Hne
          | ok i => exact ⟨i, rfl⟩
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
          [interface.mkOk go.string #a, GoInterface.ok ie]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %args_sl ⟨Hargs, -⟩
        wp_apply wp_Printf_args _ _ [interface.mkOk go.string #a, GoInterface.ok ie] _ $$ [Hargs]
        · iframe Hargs
          iapply BigSepL.bigSepL_cons.2
          isplitr
          · iapply logArg_str
          iapply BigSepL.bigSepL_cons.2
          isplitr
          · iapply logArg_err $$ HerrL
          iapply BigSepL.bigSepL_nil.2; iempintro
        iintro -
        wp_auto
        have hT' : rL.addr = rL.addr ∧ (false = true → rL.conn = true) := ⟨rfl, by simp⟩
        ihave Hreps := reps_put cfg (pre ++ [rL]) pre.length rL hrL { rL with conn := false } hT'
          $$ [Hpre HLc]
        · rw [List.take_left' rfl]
          iframe Hpre
          isplitr
          · rw [List.drop_of_length_le (by simp)]; iapply BigSepL.bigSepL_nil.2; iempintro
          iapply connRole_disc cfg _ _ { rL with conn := false } rfl $$ HLc
        have hml := map_set_eq Rep.loc (r' := { rL with conn := false }) hrL rfl
        have hma := map_set_eq Rep.addr (r' := { rL with conn := false }) hrL rfl
        ihave #Hnfs1 := nodeFacts_of_map cfg _ _ hml hma $$ Hnfs
        ihave Hjoin := Hjoin $$ %(pre ++ [rL]) %(fun b hb => Or.inr hb)
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
          Hreps Hjoin]
        · inext
          iapply coordLock_new cfg c sl (pre ++ [rL]) _ ver hd tl Hwf (by rw [hma]; exact List.Sublist.refl _)
            (by intro h; rw [List.set_eq_nil_iff] at h; simp at h)
          iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
          isplitl [Hsl]
          · rw [hml]; iexact Hsl
          iexact Hnfs1
        iapply HΦ
        iright; iexact HerrL
  · ihave %Hne := models_lab.errAny_ne_nil $$ HerrC
    obtain ⟨ie, rfl⟩ : ∃ ie, errC = GoInterface.ok ie := by
      cases errC with
      | nil => exact absurd rfl Hne
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [interface.mkOk go.string #a]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %args_sl ⟨Hargs, -⟩
    wp_apply log.Printf.wp_proof _ _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hargs]
    · iframe
    iintro -
    wp_auto
    iapply HΦ
    iright; iexact HerrC

end proof

end github_com.despreston.go_craq

end Perennial
