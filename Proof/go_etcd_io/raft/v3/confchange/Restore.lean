/-
Proof of `Spec/confchange_Restore.lean`.

Until 2026-10-08 this file was `axiom confchange.Restore.wp_proof` (the Rocq
`proof_confchange_Restore.v`'s `Axiom`): the package was not translated. It is now
proved from its callees (`toConfChangeSingle`, the `chg.Simple(cc)` closures, `chain`),
in the voters-only case the spec states. The statement is unchanged.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.confchange.toConfChangeSingle
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.chain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The invariant `chain` threads through `Restore`'s ops: before op `j`, the pair is
either the empty configuration `Restore` started from (`j = 0`), or a fresh voters-only
config holding the first `j` voters, with a progress for each (`0 < j`).
`MakeProgressTracker`'s own voter map `v0` is only read and comes back. -/
def restoreInv (chg : confchange.Changer) (v0 : Loc) (voters : List w64)
    (j : Nat) (cfg : tracker.Config) (prs : Loc) : IProp GF :=
  iprop(v0 ↦$ (∅ : GMap w64 Unit) ∗
    (⌜j = 0 ∧ cfg = chg.Tracker'.Config' ∧ prs = chg.Tracker'.Progress'⌝ ∨
     (∃ (v : Loc) (vm : GMap w64 Unit) (prs' : GMap w64 Loc),
       ⌜0 < j⌝ ∗ ⌜ConfigSimple cfg v⌝ ∗ v ↦$ vm ∗ prs ↦$ prs' ∗
       ⌜domSet prs' = domSet vm ∧ domSet vm = GMap.listToSet (voters.take j) ∧
         GMap.size vm ≤ j⌝ ∗
       ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp))))

theorem confchange.Restore.wp_proof
    (wp_confchange_toConfChangeSingle : confchange.toConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_confchange_chain : confchange.chain.spec (GF := GF) (hG := hG)) :
    confchange.Restore.spec (GF := GF) (hG := hG) := by
  intro chg cs voters dq v0 Hvne Hv0n Hcvo Hcl Hcln Hmi Harr Hl Hln
  wp_start as ⟨Hvs, Hv0, #Hpm⟩
  wp_auto
  wp_apply wp_confchange_toConfChangeSingle _ voters _ Hcvo Hcl Hcln $$ [$Hvs]
    as %ins ⟨Hvs, Hins, Hinscap⟩
  ihave %Hvlen := ownSlice_len $$ Hvs
  ihave %Hinslen := ownSlice_len $$ Hins
  ihave Hnil : (slice.nil ↦* ([] : List GoFunc)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  -- `for _, cc := range incoming { cc := cc; ops = append(ops, func(chg) {chg.Simple(cc)}) }`:
  -- after `n` iterations, `ops` holds `n` closures, the `j`th taking the pair from
  -- `restoreInv j` to `restoreInv (j + 1)` (op `j` adds voter `j`)
  ihave IH : iprop(∃ (n : w64) (ops' : GoSlice) (fs : List GoFunc) (x : raftpb.ConfChangeSingle),
      "i" ∷ i_ptr ↦ n ∗
      "ops" ∷ ops_ptr ↦ ops' ∗
      "Hcc" ∷ cc_ptr ↦ x ∗
      "Hops" ∷ ops' ↦* fs ∗
      "Hopscap" ∷ ownSliceCap GoFunc ops' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (voters.length : Int) ∧ fs.length = sint.nat n⌝ ∗
      "#Hfs" ∷ □ (∀ (j : Nat) (f : GoFunc), ⌜fs[j]? = some f⌝ -∗
        opSpec f chg (restoreInv chg v0 voters j) (restoreInv chg v0 voters (j + 1))))
    $$ [i ops cc Hnil Hcap]
  · iexists W64 0, slice.nil, [], zero_val raftpb.ConfChangeSingle
    simp only [named]
    iframe i ops cc Hnil Hcap
    isplitr
    · ipureintro; exact ⟨by decide, by word, rfl⟩
    imodintro
    iintro %j %f %Hjf
    simp at Hjf
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < voters.length := by
      have := Hinslen.1; rw [List.length_map] at this; word
    obtain ⟨idn, Hidn⟩ : ∃ x, voters[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ins.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index ins (sint.Z n) _ _ (addNodeCC idn) Hn.1 $$ [Hins] with Hins
    · iframe Hins; ipureintro; rw [List.getElem?_map, Hidn]; rfl
    -- the closure captures its loop-local copy `cc`, read-only from here on
    ipersist cc
    -- `ops = append(ops, func(chg Changer) {...})`
    wp_func_lits
    wp_apply wp_slice_literal (V := GoFunc) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hops $Hopscap $Hsl] as %ops2 ⟨Hops, Hopscap, -⟩
    wp_for_post
    iframe HΦ Hv0 chg Hvs Hins Hinscap
    iexists n + W64 1, ops2, _, addNodeCC idn
    simp only [named]
    iframe i ops Hcc Hops Hopscap
    have Hidn0 : idn ≠ W64 0 := fun h => Hv0n (h ▸ List.mem_of_getElem? Hidn)
    have Hfslen : fs.length = sint.nat n := Hn.2.2
    isplitr
    · ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [List.length_append, List.length_singleton, Hfslen]; word
    -- the closures' triples: the old ones, and the new one, op `fs.length = n`
    imodintro
    iintro %j %f %Hjf
    rcases Nat.lt_or_ge j fs.length with Hj | Hj
    · rw [List.getElem?_append_left Hj] at Hjf
      iapply Hfs $$ %j %f %Hjf
    have Hj' : j = fs.length := by
      have := (List.getElem?_eq_some_iff.1 Hjf).1
      rw [List.length_append, List.length_singleton] at this
      omega
    subst Hj'
    rw [List.getElem?_concat_length] at Hjf
    cases Hjf
    -- `func(chg Changer) { return chg.Simple(cc) }`: `Simple([AddNode idn])` on the
    -- pair in `chg`'s tracker, from `restoreInv fs.length` to `restoreInv (fs.length + 1)`
    unfold opSpec
    iintro %cfg %prs
    wp_start_folded as HI
    wp_auto
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [addNodeCC idn]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    have Htake : voters.take (fs.length + 1) = voters.take fs.length ++ [idn] := by
      rw [List.take_add_one, Hfslen, Hidn]; rfl
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, %Hcfg, %Hprs⟩ | ⟨%v, %vm, %prs', %Hpos, %Hcs, Hv, Hprs, %Hd, Hprogs⟩)⟩
    · -- op 0: from the empty configuration `Restore` started from
      subst Hcfg Hprs
      have Hcv : ConfigVotersOnly chg.Tracker'.Config' v0 := ⟨Harr, Hl, Hln⟩
      wp_apply wp_Changer_Simple _ _ _ idn v0 ∅ ∅ _ _ _ _ Hidn0
        (by rw [GMap.map_size_empty]; decide) Hcv rfl Hmi $$ [$chg $Hsl2 $Hv0 $Hpm]
        as %cfg' %trk %v' %prs'' ⟨chg, Hsl2, Hv0, -, %Hcs', Hv', Htrk, %Hd', Hprogs'⟩
      · iapply BigSepM.bigSepM_empty.2; iempintro
      iapply HΦ
      iframe Hv0
      iright
      iexists v', <[idn := ()]> ∅, prs''
      iframe Hv' Htrk Hprogs'
      ipureintro
      refine ⟨by omega, Hcs', Hd', ?_, ?_⟩
      · have Hv0' : voters[0]? = some idn := (Hfslen.symm.trans Hj0) ▸ Hidn
        rw [Hj0]
        show (<[idn := ()]> ∅).domSet = listToSet (List.take (0 + 1) voters)
        simp only [List.take_add_one, List.take_zero, Hv0', Option.toList_some, List.nil_append,
          GMap.listToSet_cons, GMap.listToSet_nil, GMap.dom_insert, GMap.dom_empty]
      · rw [GMap.map_size_insert_None _ _ _ (by rfl), GMap.map_size_empty]; omega
    · -- op `fs.length > 0`: from the configuration the previous op built
      have Hsz : GMap.size vm < 2 ^ 63 := by
        have := Hd.2.2
        have h2 := Hvlen.1
        word
      wp_apply wp_Changer_Simple _
        ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer)
        _ idn v vm prs' _ _ _ _ Hidn0 Hsz Hcs.1 Hd.1 Hmi
        $$ [$chg $Hsl2 $Hv $Hprs $Hprogs]
        as %cfg' %trk %v' %prs'' ⟨chg, Hsl2, -, -, %Hcs', Hv', Htrk, %Hd', Hprogs'⟩
      iapply HΦ
      iframe Hv0
      iright
      iexists v', <[idn := ()]> vm, prs''
      iframe Hv' Htrk Hprogs'
      ipureintro
      refine ⟨by omega, Hcs', Hd', ?_, ?_⟩
      · rw [Htake, GMap.listToSet_app, GMap.listToSet_cons, GMap.listToSet_nil, ← Hd.2.1,
          GMap.dom_insert]
        apply GMap.set_eq; intro k
        simp only [GMap.elem_of_union, GMap.elem_of_singleton, GMap.elem_of_empty, or_false]
        exact Or.comm
      · rcases h : vm !! idn with _ | ⟨⟩
        · rw [GMap.map_size_insert_None _ _ _ h]; omega
        · rw [GMap.insert_id _ _ _ h]; omega
  · -- the loop is over: `chain(chg, ops...)`
    have Hn' : sint.nat n = voters.length := by
      have := Hinslen.1; rw [List.length_map] at this; word
    ihave HI0 : restoreInv chg v0 voters 0 chg.Tracker'.Config' chg.Tracker'.Progress' $$ [Hv0]
    · unfold restoreInv
      iframe Hv0
      ileft
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    wp_apply wp_confchange_chain chg ops' fs _ (restoreInv chg v0 voters) $$ [$Hops $HI0 $Hfs]
      as %cfg %prs ⟨Hops, HI⟩
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, -, -⟩ | ⟨%v, %vm, %prs', %Hpos, %Hcs, Hv, Hprs, %Hd, Hprogs⟩)⟩
    · exfalso
      rw [Hn.2.2, Hn'] at Hj0
      exact Hvne (List.eq_nil_of_length_eq_zero Hj0)
    iapply HΦ
    iframe Hvs Hv0 Hpm Hv Hprs Hprogs
    ipureintro
    rw [Hn.2.2, Hn', List.take_length] at Hd
    exact ⟨⟨Hcs.1.1, Hcs.1.2.1, Hcs.1.2.2, Hcs.2⟩, Hd.2.1, Hd.1.trans Hd.2.1⟩

end proof

end EtcdGrove
end Perennial
