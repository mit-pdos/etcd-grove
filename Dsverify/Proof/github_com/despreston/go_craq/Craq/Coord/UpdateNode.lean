/-
`cdr.updateNode(i)` (lock held): replica `i`'s metadata (`metaOf`), sent by `sendMeta`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.SendMeta

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The address of replica `j` (none out of range). -/
def addrAt (rs : List Rep) (j : Nat) : GoString := (rs[j]?.map Rep.addr).getD go!""

/-- Replica `i`'s metadata, as `updateNode(i)` sends it. -/
def metaOf (rs : List Rep) (i : Nat) : MetaV where
  isHead := decide (i = 0)
  isTail := decide (rs.length = i + 1)
  prev := if 1 < rs.length ∧ 0 < i then addrAt rs (i - 1) else go!""
  next := if 1 < rs.length ∧ i + 1 ≠ rs.length then addrAt rs (i + 1) else go!""
  tail := addrAt rs (rs.length - 1)

theorem addrAt_mem (rs : List Rep) (j : Nat) (chain : List GoString)
    (hch : ∀ r ∈ rs, r.addr ∈ chain) : addrAt rs j ∈ go!"" :: chain := by
  unfold addrAt
  cases h : rs[j]? with
  | none => simp
  | some r => simp only [Option.map_some, Option.getD_some]; exact List.mem_cons_of_mem _ (hch r (List.mem_of_getElem? h))

theorem metaOf_addrsOk (rs : List Rep) (i : Nat) (chain : List GoString)
    (hch : ∀ r ∈ rs, r.addr ∈ chain) : metaAddrsOk chain (metaOf rs i) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [metaOf]
  · split
    · exact addrAt_mem rs _ chain hch
    · simp
  · split
    · exact addrAt_mem rs _ chain hch
    · simp
  · exact addrAt_mem rs _ chain hch

section proof0
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogSpecs GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem nodeFacts_at (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) (h : rs[j]? = some r) :
    ([∗list] r ∈ rs, nodeFacts cfg r.loc r.addr) ⊢ nodeFacts cfg r.loc r.addr :=
  BigSepL.bigSepL_lookup (Φ := fun _ r => nodeFacts cfg r.loc r.addr) h

theorem locs_at (rs : List Rep) (j : Nat) (r : Rep) (h : rs[j]? = some r) :
    (rs.map Rep.loc)[j]? = some r.loc := by
  simp [h]

theorem wp_node_Address' (cfg : Cfg GF) (n : Loc) (a : GoString) :
    {{ nodeFacts cfg n a }}
      (App (Val (n @!! go.GoType.PointerType coordinator.node.ty @!! go!"Address")) (Val #()))
    {{ RET #a; True }} := by
  wp_start as #Hn
  unfold nodeFacts
  icases Hn with ⟨#Ha, -⟩
  wp_auto
  iapply HΦ; itrivial

end proof0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogSpecs GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem wp_updateNode (cfg : Cfg GF) (c : Loc) (sl : GoSlice) (rs : List Rep) (dq : DFrac)
    (i : w64) (ri : Rep) (b : Bool) (r : Role)
    (hi : 0 ≤ sint.Z i) (hri : rs[sint.nat i]? = some ri) (hch : ∀ r ∈ rs, r.addr ∈ cfg.chain) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        structFieldRef coordinator.Coordinator go!"replicas" c ↦{dq} sl ∗
        sl ↦*{dq} rs.map Rep.loc ∗ ([∗list] r ∈ rs, nodeFacts cfg r.loc r.addr) ∗
        structFieldRef coordinator.node go!"connected" ri.loc ↦ b ∗
        sendPre cfg ri.addr b r (metaOf rs (sint.nat i)) }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"updateNode"))
        (Val #i))
    {{ (err : GoInterface), RET #err;
        structFieldRef coordinator.Coordinator go!"replicas" c ↦{dq} sl ∗
        sl ↦*{dq} rs.map Rep.loc ∗
        ∃ b' : Bool, structFieldRef coordinator.node go!"connected" ri.loc ↦ b' ∗
          sendPost cfg ri.addr b r (metaOf rs (sint.nat i)) b' err }} := by
  wp_start as ⟨Hrep, Hsl, #Hnfs, Hconn, Hpre⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  simp only [List.length_map] at Hlen
  have hlt : sint.nat i < rs.length := by
    rcases (List.getElem?_eq_some_iff.mp hri) with ⟨h, -⟩; exact h
  ihave #Hnf := nodeFacts_at cfg rs _ ri hri $$ Hnfs
  wp_auto
  simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, by word⟩, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z i) (rs.map Rep.loc) dq ri.loc hi $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; exact locs_at rs _ ri hri
  wp_apply wp_node_Address' cfg ri.loc ri.addr $$ Hnf
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [interface.mkOk go.string #ri.addr]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args_sl ⟨Hargs, -⟩
  wp_apply log.Printf.wp_proof _ _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hargs]
  · iframe
  iintro -
  wp_auto
  have hpos : 0 < rs.length := by omega
  list_elem rs (rs.length - 1) as rl
  ihave #Hnfl := nodeFacts_at cfg rs _ rl Hrl_lookup $$ Hnfs
  have hl1 : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := by
    constructor <;> word
  simp only [hl1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) (rs.map Rep.loc) dq rl.loc hl1.1 $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro
    rw [show (sint.Z (sl.len - W64 1)).toNat = rs.length - 1 by word]
    exact locs_at rs _ rl Hrl_lookup
  wp_apply wp_node_Address' cfg rl.loc rl.addr $$ Hnfl
  dsimp only
  wp_join iprop(∃ p nx : GoString,
      structFieldRef coordinator.Coordinator go!"replicas" c ↦{dq} sl ∗
      sl ↦*{dq} rs.map Rep.loc ∗ cdr_ptr ↦ c ∗ i_ptr ↦ i ∗
      args_ptr ↦ transport.NodeMeta.mk (decide (i = W64 0)) (decide (sl.len = i + W64 1)) p nx rl.addr ∗
      ⌜p = (metaOf rs (sint.nat i)).prev ∧ nx = (metaOf rs (sint.nat i)).next⌝)
    with [Hrep Hsl cdr i args] as ⟨%p, %nx, Hrep, Hsl, cdr, i, args, %Hpn⟩
  · -- `len > 1`
    wp_join iprop(∃ p : GoString,
        structFieldRef coordinator.Coordinator go!"replicas" c ↦{dq} sl ∗
        sl ↦*{dq} rs.map Rep.loc ∗ cdr_ptr ↦ c ∗ i_ptr ↦ i ∗
        args_ptr ↦ transport.NodeMeta.mk (decide (i = W64 0)) (decide (sl.len = i + W64 1)) p
          (zero_val transport.NodeMeta).Next' rl.addr ∗
        ⌜p = (metaOf rs (sint.nat i)).prev⌝)
      with [Hrep Hsl cdr i args] as ⟨%p, Hrep, Hsl, cdr, i, args, %Hp⟩
    · -- `i > 0`
      list_elem rs (sint.nat i - 1) as rp
      ihave #Hnfp := nodeFacts_at cfg rs _ rp Hrp_lookup $$ Hnfs
      have hb : 0 ≤ sint.Z (i - W64 1) ∧ sint.Z (i - W64 1) < sint.Z sl.len := by
        constructor <;> word
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z (i - W64 1)) (rs.map Rep.loc) dq rp.loc hb.1 $$ [Hsl] as Hsl
      · iframe Hsl; ipureintro
        rw [show (sint.Z (i - W64 1)).toNat = sint.nat i - 1 by word]
        exact locs_at rs _ rp Hrp_lookup
      wp_apply wp_node_Address' cfg rp.loc rp.addr $$ Hnfp
      wp_join_done
      iexists _
      iframe
      ipureintro
      simp only [metaOf]
      rw [if_pos ⟨by word, by word⟩]
      simp [addrAt, Hrp_lookup]
    · iexists _
      iframe
      ipureintro
      simp only [metaOf]
      rw [if_neg (by intro h; word)]
      rfl
    · by_cases hn : i + W64 1 = sl.len
      · rw [decide_eq_true hn]
        simp only [Bool.not_true]
        wp_auto
        wp_join_done
        iexists _, _
        iframe
        ipureintro
        refine ⟨Hp, ?_⟩
        simp only [metaOf]
        rw [if_neg (by intro h; apply h.2; word)]
        rfl
      · rw [decide_eq_false hn]
        simp only [Bool.not_false]
        wp_auto
        have hnl : sint.nat i + 1 < rs.length := by
          have : sint.nat i + 1 ≠ rs.length := by intro h; apply hn; word
          omega
        list_elem rs (sint.nat i + 1) as rn
        ihave #Hnfn := nodeFacts_at cfg rs _ rn Hrn_lookup $$ Hnfs
        have hb : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) < sint.Z sl.len := by
          constructor <;> word
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sl (sint.Z (i + W64 1)) (rs.map Rep.loc) dq rn.loc hb.1 $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro
          rw [show (sint.Z (i + W64 1)).toNat = sint.nat i + 1 by word]
          exact locs_at rs _ rn Hrn_lookup
        wp_apply wp_node_Address' cfg rn.loc rn.addr $$ Hnfn
        wp_join_done
        iexists _, _
        iframe
        ipureintro
        refine ⟨Hp, ?_⟩
        simp only [metaOf]
        rw [if_pos ⟨by word, by intro h; apply hn; word⟩]
        simp [addrAt, Hrn_lookup]
  · iexists _, _
    iframe
    ipureintro
    simp only [metaOf]
    rw [if_neg (by intro h; word), if_neg (by intro h; word)]
    exact ⟨rfl, rfl⟩
  have hm : transport.NodeMeta.mk (decide (i = W64 0)) (decide (sl.len = i + W64 1)) p nx rl.addr =
      transport.NodeMeta.mk (metaOf rs (sint.nat i)).isHead (metaOf rs (sint.nat i)).isTail
        (metaOf rs (sint.nat i)).prev (metaOf rs (sint.nat i)).next (metaOf rs (sint.nat i)).tail := by
    rw [Hpn.1, Hpn.2]
    have h1 : decide (i = W64 0) = decide (sint.nat i = 0) := by
      apply decide_eq_decide.mpr; constructor <;> intro h <;> word
    have h2 : decide (sl.len = i + W64 1) = decide (rs.length = sint.nat i + 1) := by
      apply decide_eq_decide.mpr; constructor <;> intro h <;> word
    have h3 : rl.addr = addrAt rs (rs.length - 1) := by simp [addrAt, Hrl_lookup]
    simp only [metaOf, h1, h2, h3]
  ihave Hm : metaPtr args_ptr (DFrac.own 1) (metaOf rs (sint.nat i)) $$ [args]
  · unfold metaPtr; rw [← hm]; iexact args
  wp_apply wp_sendMeta cfg c ri.loc args_ptr ri.addr b (DFrac.own 1) (metaOf rs (sint.nat i)) r
    $$ [Hnf Hconn Hm Hpre] as %err ⟨%b', Hconn, Hpost⟩
  · iframe Hnf; iframe; ipureintro; exact metaOf_addrsOk rs _ cfg.chain hch
  iapply HΦ
  iframe

end proof

end github_com.despreston.go_craq

end Perennial
