/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__randomChange.lean`.
Lean-first (no Rocq counterpart).

A random replica's conf state (`conf`, read-only) for `randomID`. The empty `ConfChangeV2`, one
time in eight; else `count` (one to three) single changes appended into a fresh slice (the loop
invariant: the slice holds `i` read-only changes, `ccsRO`, their cells frozen: `t.Enum()` and
`new(id)`), and a transition picked from the three defined ones; then a `ConfChange` of the first
change (its cells shared), or the `ConfChangeV2` of the changes. Every transition is defined
(`enterJointOf` answers for `0`, `1`, `2`), and a `ConfChange`'s is the automatic one
(`ccTransOk_v1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__randomChange
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__randomID
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__conf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeTransition__Enum

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- A `ConfChangeV2` of a defined transition is shaped, whatever its changes. -/
theorem ccTransOk_v2 (t : w32) (chs : List ConfChangeSingleM) (ctx : List w8)
    (ht : t = W32 0 ∨ t = W32 1 ∨ t = W32 2) : ccTransOk (.v2 ⟨t, chs, ctx⟩) := by
  simp only [ccTransOk, ccToV2, enterJointOf]
  rcases ht with h | h | h <;> subst h <;> by_cases hn : 1 < chs.length <;> simp [hn]

/-- The loop's counter, one step on. -/
private theorem loop_step (i cnt : w64) (n : Nat) (h1 : n = sint.nat i) (h2 : 0 ≤ sint.Z i)
    (h3 : sint.Z i < sint.Z cnt) (hc : sint.Z cnt ≤ 3) :
    n + 1 = sint.nat (i + W64 1) ∧ 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z cnt := by
  subst h1
  refine ⟨?_, ?_, ?_⟩ <;> word

/-- The loop's exit at one change. -/
private theorem len_one (i : w64) (n : Nat) (h1 : n = sint.nat i) (h2 : sint.Z i ≤ sint.Z (W64 1))
    (h3 : ¬ sint.Z i < sint.Z (W64 1)) : n = 1 := by
  subst h1; word

/-- `(*ConfChangeType).Enum` (`t.Enum()` on the local variable): the value method on `*l`. -/
private theorem ConfChangeType.wp_ptr_Enum_of
    (wp_Enum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG)) (l : Loc)
    (x : raftpb.ConfChangeType) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ (l ↦ x : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType raftpb.ConfChangeType.ty @!! go!"Enum")) (Val #()))
    {{ (p : Loc), RET #p; l ↦ x ∗ p ↦ x }} := by
  wp_start as Hl
  wp_auto
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_Enum x
  iintro %p Hp
  iapply HΦ
  iframe

/-- `(*ConfChangeTransition).Enum` (`transition.Enum()` on the local variable). -/
private theorem ConfChangeTransition.wp_ptr_Enum_of
    (wp_Enum : raftpb.ConfChangeTransition.Enum.spec (GF := GF) (hG := hG)) (l : Loc)
    (x : raftpb.ConfChangeTransition) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ (l ↦ x : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType raftpb.ConfChangeTransition.ty @!! go!"Enum"))
        (Val #()))
    {{ (p : Loc), RET #p; l ↦ x ∗ p ↦ x }} := by
  wp_start as Hl
  wp_auto
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_Enum x
  iintro %p Hp
  iapply HΦ
  iframe

set_option linter.unreachableTactic false in
theorem Cluster.randomChange.wp_proof (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_randomID : Cluster.randomID.spec (GF := GF) (hG := hG))
    (wp_conf : Replica.conf.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_TypeEnum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (wp_TransEnum : raftpb.ConfChangeTransition.Enum.spec (GF := GF) (hG := hG)) :
    Cluster.randomChange.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  intro γr vs c
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_random γr vs c $$ [$Hc] as %r0 ⟨%id0, #Hr0⟩
  wp_apply wp_conf γr vs id0 r0 $$ [$Hr0] as %csp %idx ⟨%cs, #Hcs⟩
  try wp_auto
  wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b8 -
  cases b8 <;> try wp_auto
  rotate_left
  · -- the empty `ConfChangeV2`
    wp_alloc_auto
    rename_i l
    irename : (l ↦ zero_val raftpb.ConfChangeV2 : IProp GF) => Hl
    ihave #cnull := cellRO_null (GF := GF) (V := w32)
    ihave #Hnilb : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hnilc : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownConfChangeV2_of_struct l (zero_val raftpb.ConfChangeV2) ConfChangeV2M.empty [] ⊤ rfl
      $$ [Hl Hnilc] with Hv2
    · iframe Hl
      rw [show (zero_val raftpb.ConfChangeV2).Transition' = null from rfl,
        show (zero_val raftpb.ConfChangeV2).Changes' = slice.nil from rfl,
        show (zero_val raftpb.ConfChangeV2).Context' = slice.nil from rfl,
        show ConfChangeV2M.empty.transition = zero_val w32 from rfl,
        show ConfChangeV2M.empty.changes = [] from rfl,
        show ConfChangeV2M.empty.context = [] from rfl]
      iframe cnull Hnilc Hnilb
      iapply BigSepL2.bigSepL2_nil.2; itrivial
    try wp_auto
    ispecialize HΦ $$ %(interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #l)
      %(ConfChangeIM.v2 ConfChangeV2M.empty)
    iapply HΦ
    isplitl
    · simp only [ownConfChangeI]
      iexists l
      iframe Hv2
      ipureintro; rfl
    ipureintro
    simp [ccTransOk, ccToV2, ConfChangeV2M.empty, enterJointOf]
  -- the number of changes
  wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b2 -
  cases b2 <;> try wp_auto
  ihave Hcnt : iprop(∃ cnt : w64, count_ptr ↦ cnt ∗ ⌜1 ≤ sint.Z cnt ∧ sint.Z cnt ≤ 3⌝) $$ [count]
  · iexists W64 1; iframe count; ipureintro; decide
  rotate_left
  wp_apply wp_below (W64 3) as %k %Hk
  try wp_auto
  ihave Hcnt : iprop(∃ cnt : w64, count_ptr ↦ cnt ∗ ⌜1 ≤ sint.Z cnt ∧ sint.Z cnt ≤ 3⌝) $$ [count]
  · iexists _; iframe count; ipureintro
    have := Hk.2 (by decide)
    constructor <;> word
  clear Hk
  -- the changes
  all_goals
    icases Hcnt with ⟨%cnt, Hcount, %Hc⟩
    rw [show zero_val GoSlice = slice.nil from rfl]
    ihave IH : iprop(∃ (i : w64) (chs : GoSlice) (ls : List Loc) (ms : List ConfChangeSingleM),
        "i" ∷ i_ptr ↦ i ∗ "changes" ∷ changes_ptr ↦ chs ∗ "Hch" ∷ chs ↦* ls ∗
        "Hchc" ∷ ownSliceCap Loc chs (DFrac.own 1) ∗
        "#Hccs" ∷ ([∗list] q;m ∈ ls;ms, ccsRO q m) ∗
        "%Hi" ∷ ⌜ls.length = sint.nat i ∧ 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z cnt⌝) $$ [i changes]
    · iexists W64 0, slice.nil, [], []
      iframe i changes
      simp only [named]
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro; refine ⟨rfl, by decide, by word⟩
    wp_for IH
    wp_if_destruct
    · -- one more change: its type (`wp_if_destruct` leaves the loop's condition unsimplified in
      -- one of the two copies)
      have Hlt : sint.Z i < sint.Z cnt := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj (V := Bool) Hif)
      have Hi1 : ls.length + 1 = sint.nat (i + W64 1) ∧ 0 ≤ sint.Z (i + W64 1) ∧
          sint.Z (i + W64 1) ≤ sint.Z cnt := by
        exact loop_step i cnt _ Hi.1 Hi.2.1 Hlt Hc.2
      wp_apply wp_below (W64 16) as %sw -
      simp only [show raftpb.ConfChangeAddNode = #(W32 0) from rfl,
        show raftpb.ConfChangeRemoveNode = #(W32 1) from rfl,
        show raftpb.ConfChangeUpdateNode = #(W32 2) from rfl,
        show raftpb.ConfChangeAddLearnerNode = #(W32 3) from rfl]
      try wp_auto
      wp_bind (If _ _ _)
      iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ tv : w32, t_ptr ↦ tv)))
      isplitl [t]
      · iterate 16 (all_goals (try wp_if_destruct); all_goals (try wp_auto))
        all_goals
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _; iexact t
      iintro %v ⟨%Hv, %tv, Ht⟩
      subst Hv
      try wp_auto
      -- its id, and the fresh change
      wp_apply wp_randomID γr vs c csp cs _ $$ [$Hc $Hcs] as %nid -
      try wp_auto
      wp_apply ConfChangeType.wp_ptr_Enum_of wp_TypeEnum t_ptr tv $$ [$Hpb $Ht] as %pty ⟨Ht, Hpty⟩
      try wp_auto
      imod cellRO_alloc _ _ $$ Hpty with #cty
      imod cellRO_alloc _ _ $$ «$v1» with #cnd
      imod ccsRO_of_struct «$sl0_ptr»
        { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
          sizeCache' := 0 }
        (ConfChangeSingleM.mk tv nid) ⊤ rfl $$ [«$sl0»] with #Hq
      · dsimp only
        iframe
        iframe cty cnd
      wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hch $Hchc $Hsl1] as %chs' ⟨Hch, Hchc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, chs', ls ++ [«$sl0_ptr»], ms ++ [ConfChangeSingleM.mk tv nid]
      iframe
      isplitr
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe Hccs Hq
      ipureintro
      simp only [List.length_append, List.length_singleton]
      exact Hi1
    · -- the transition
      have Hge : ¬ sint.Z i < sint.Z cnt := by
        first | exact Hif | (intro h; apply Hif; simp [h])
      try rw [ite_eq_left (by simp [Hge])]
      simp only [show raftpb.ConfChangeTransitionAuto = #(W32 0) from rfl,
        show raftpb.ConfChangeTransitionJointImplicit = #(W32 1) from rfl,
        show raftpb.ConfChangeTransitionJointExplicit = #(W32 2) from rfl]
      try wp_auto
      wp_apply wp_slice_literal (V := w32) [W32 0, W32 1, W32 2]
      isplitr
      · ipureintro; rfl
      iintro %trs ⟨Htrs, -⟩
      rw [show go.arrayLiteralSize _ = 3 from rfl]
      generalize Htrsd : slice.mk trs (W64 3) (W64 3) = trsl
      wp_apply wp_below (W64 3) as %k3 %Hk3
      try wp_auto
      ihave %Htlen := ownSlice_len _ _ _ $$ Htrs
      have Hk3' : uint.Z k3 < 3 := Hk3.2 (by decide)
      have Hbnd : 0 ≤ sint.Z k3 ∧ sint.Z k3 < sint.Z trsl.len := by
        subst Htrsd
        constructor <;> word
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      have Hkn : sint.nat k3 < 3 := by word
      obtain ⟨tr, Htr⟩ : ∃ tr, [W32 0, W32 1, W32 2][sint.nat k3]? = some tr :=
        ⟨_, List.getElem?_eq_getElem (by simpa using Hkn)⟩
      have Htr3 : tr = W32 0 ∨ tr = W32 1 ∨ tr = W32 2 := by
        have := List.mem_of_getElem? Htr; simpa using this
      wp_apply wp_load_slice_index _ (sint.Z k3) _ _ tr Hbnd.1 $$ [Htrs] as Htrs
      · iframe Htrs; ipureintro; exact Htr
      try wp_auto
      ihave %Hlens := BigSepL2.bigSepL2_length $$ Hccs
      ihave %Hchlen := ownSlice_len _ _ _ $$ Hch
      wp_if_destruct
      try wp_auto
      wp_if_destruct
      wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b -
      cases b <;> try wp_auto
      rotate_left
      · -- a `ConfChange` of the one change (its cells shared)
        have Hl1 : ls.length = 1 := len_one i _ Hi.1 Hi.2.2 Hge
        obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp Hl1
        obtain ⟨m0, rfl⟩ := List.length_eq_one_iff.mp (Hlens.symm.trans Hl1)
        ihave Hq := BigSepL2.bigSepL2_singleton.1 $$ Hccs
        iunfold ccsRO at Hq
        iunfold ccsPts at Hq
        icases Hq with ⟨%pt, %pn, %uf, %Hnn, #HT, #cT1, #HN, #cN1, #Hpbq⟩
        have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z chs.len := by
          obtain ⟨h1, h2⟩ := Hchlen
          simp only [List.length_singleton] at h1
          constructor <;> word
        simp only [Hb0, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index chs (sint.Z (W64 0)) [q] (DFrac.own 1) q Hb0.1 $$ [Hch] as Hch
        · iframe Hch; ipureintro; rfl
        try wp_auto
        simp only [Hb0, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index chs (sint.Z (W64 0)) [q] (DFrac.own 1) q Hb0.1 $$ [Hch] as Hch
        · iframe Hch; ipureintro; rfl
        try wp_auto
        wp_alloc_auto
        rename_i l
        irename : (l ↦ (_ : raftpb.ConfChange) : IProp GF) => Hl
        ihave #cnull := cellRO_null (GF := GF) (V := w64)
        ihave #Hnilb : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
        · iapply ownSlice_nil
        imod ownConfChange_of_struct l
          { state' := zeroValDef, Type' := pt, NodeId' := pn, Context' := slice.nil, Id' := null,
            unknownFields' := slice.nil, sizeCache' := 0 }
          { type := m0.Type', nodeId := m0.NodeId', context := [], id := zero_val w64 } ⊤ rfl
          $$ [Hl] with Hv1
        · dsimp only
          iframe Hl
          iframe cT1 cN1 cnull Hnilb
        try wp_auto
        ispecialize HΦ $$ %(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #l)
          %(ConfChangeIM.v1 { type := m0.Type', nodeId := m0.NodeId', context := [], id := zero_val w64 })
        iapply HΦ
        isplitl
        · simp only [ownConfChangeI]
          iexists l
          iframe Hv1
          ipureintro; rfl
        ipureintro
        exact ccTransOk_v1 _
      -- the `ConfChangeV2` of the changes
      all_goals
        wp_apply ConfChangeTransition.wp_ptr_Enum_of wp_TransEnum transition_ptr _ $$ [$Hpb $transition]
          as %ptr ⟨-, Hptr⟩
        try wp_auto
        wp_alloc_auto
        rename_i l
        irename : (l ↦ (_ : raftpb.ConfChangeV2) : IProp GF) => Hl
        imod cellRO_alloc _ _ $$ Hptr with #cT
        ihave #Hnilb : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
        · iapply ownSlice_nil
        imod ownConfChangeV2_of_struct l
          { state' := zeroValDef, Transition' := ptr, Changes' := chs, Context' := slice.nil,
            unknownFields' := slice.nil, sizeCache' := 0 }
          ⟨_, ms, []⟩ ls ⊤ rfl $$ [Hl Hch] with Hv2
        · dsimp only
          iframe Hl Hch
          iframe cT Hccs Hnilb
        try wp_auto
        ispecialize HΦ $$ %(interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #l)
          %(ConfChangeIM.v2 ⟨_, ms, []⟩)
        iapply HΦ
        isplitl
        · simp only [ownConfChangeI]
          iexists l
          iframe Hv2
          ipureintro; rfl
        ipureintro
        exact ccTransOk_v2 _ ms [] Htr3

end proof

end kvreconf
end EtcdGrove
end Perennial
