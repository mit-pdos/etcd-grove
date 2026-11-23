/-
Proof of `Spec/go_etcd_io/raft/v3/DescribeConfChange.lean` (#25, 2026-11-23; a trust-boundary axiom
from stage R4, 2026-10-16, until then): `DescribeConfChange` (`util.go`, raft v3.7) over the specs of
its callees, Perennial's `strings.Builder` (`9da0efb89`) and `fmt.Fprintf` (`7b2259a12`, with the
`[]byte` argument of `%q`):

```go
func DescribeConfChange(cc pb.ConfChangeI) string {
	cv2 := cc.AsV2()
	var b strings.Builder
	fmt.Fprintf(&b, "transition:%v", cv2.GetTransition())
	for _, c := range cv2.GetChanges() {
		fmt.Fprintf(&b, " changes:{type:%v node_id:%d}", c.GetType(), c.GetNodeId())
	}
	if len(cv2.Context) > 0 {
		fmt.Fprintf(&b, " context:%q", cv2.Context)
	}
	return b.String()
}
```

`%v` of the transition and of each change's type calls their `String()` (trusted models since
2026-11-23, `TrustedCode/go_etcd_io/raft/v3/raftpb.lean`); `%d` of the node id, and `%q` of the
context's bytes (lent read-only), call nothing. The builder is the writer of every `Fprintf`.
-/
module

public import Spec.go_etcd_io.raft.v3.DescribeConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetTransition
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetChanges
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetNodeId
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__String
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeTransition__String
public import Proof.go_etcd_io.raft.v3.raftpb.MsgTypeName
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.fmt.BytesResults
public import Perennial.Proof.strings.Link
public import Perennial.Proof.strings.BuilderBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! The range loop over the changes is proved by `wp_slice_for_range_ro`, at the `slice.forRange`
it is about, not unfolded by `wp_auto`. -/
attribute [-instance] pure_wp_slice_for_range

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (`for i, x := range s { body }`): `P i` holds
before the `i`-th iteration, and the body ends normally. (A copy of
`Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range`, which this package does not import.) -/
private theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end loop

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `*strings.Builder` at `b`, as an `io.Writer`: `Write` appends what it is given. -/
private theorem builder_writeSpec (b : Loc) (s : GoString) :
    ⊢ _root_.Perennial.fmt.writeSpec (GF := GF) ⟨go.GoType.PointerType strings.Builder.ty, #b⟩
      (strings.ownBuilder b s) (fun bs _ _ => strings.ownBuilder b (s ++ bs)) := by
  unfold _root_.Perennial.fmt.writeSpec
  iintro %sl %bs %Φ Hb Hsl HΦ
  wp_apply strings.Builder.wp_Write b s sl bs (DFrac.own 1) $$ [$Hb $Hsl] as ⟨Hb, Hsl⟩
  iapply HΦ $$ Hsl Hb

omit package_sem in
/-- `%v` of a value of an `int32`-based enum of raftpb with an exact `String()` spec. -/
private theorem enum_argOk (ty : go.GoType) (f : w32 → GoString)
    (h : ∀ x : w32, {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
      (App (Val (x @!! ty @!! go!"String")) (Val #())) {{ RET #(f x); True }})
    (hF : methodSet ty !! go!"Format" = none) (hE : methodSet ty !! go!"Error" = none)
    (hS : methodSet ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig)
    (hC : methodSet ty !! go!"CanInterface" = none) (x : w32) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ⊢
      _root_.Perennial.fmt.argOk (interface.mkOk ty #x) := by
  iintro #Hpkg
  unfold _root_.Perennial.fmt.argOk
  iright; iright
  isplitl
  · iapply fmt.stringMethodSpec_of_wp ty go!"String" _ f h x $$ Hpkg
  · ipureintro; exact ⟨hF, hE, hS, hC⟩

omit [GooseSemantics] in
/-- The method-set facts `fmt`'s `%v` asks of `ConfChangeTransition` (no `Format`, no `Error`, a
`String() string`, no `CanInterface`). -/
private theorem transition_methods :
    methodSet raftpb.ConfChangeTransition.ty !! go!"Format" = none ∧
    methodSet raftpb.ConfChangeTransition.ty !! go!"Error" = none ∧
    methodSet raftpb.ConfChangeTransition.ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig ∧
    methodSet raftpb.ConfChangeTransition.ty !! go!"CanInterface" = none := by
  have h1 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeTransition.ty) go!"Format")
  have h2 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeTransition.ty) go!"Error")
  have h3 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeTransition.ty) go!"String")
  have h4 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeTransition.ty) go!"CanInterface")
  simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3 h4
  exact ⟨by simpa using h1, by simpa using h2,
    by simpa [_root_.Perennial.fmt.noArgStringSig] using h3, by simpa using h4⟩

omit [GooseSemantics] in
/-- The same of `ConfChangeType`. -/
private theorem type_methods :
    methodSet raftpb.ConfChangeType.ty !! go!"Format" = none ∧
    methodSet raftpb.ConfChangeType.ty !! go!"Error" = none ∧
    methodSet raftpb.ConfChangeType.ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig ∧
    methodSet raftpb.ConfChangeType.ty !! go!"CanInterface" = none := by
  have h1 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeType.ty) go!"Format")
  have h2 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeType.ty) go!"Error")
  have h3 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeType.ty) go!"String")
  have h4 := (go.MethodSetIs.method_set_is (t := raftpb.ConfChangeType.ty) go!"CanInterface")
  simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3 h4
  exact ⟨by simpa using h1, by simpa using h2,
    by simpa [_root_.Perennial.fmt.noArgStringSig] using h3, by simpa using h4⟩

/-- The arguments of `"transition:%v"`. -/
private theorem transition_argsOk (hTrS : raftpb.ConfChangeTransition.String.spec (GF := GF) (hG := hG))
    (t : w32) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ⊢
      _root_.Perennial.fmt.argsOk _root_.Perennial.fmt.methodVerbs go!"transition:%v"
        [interface.mkOk raftpb.ConfChangeTransition.ty #t] := by
  iintro #Hpkg
  iapply _root_.Perennial.fmt.argsOk_intro (ds := [⟨W8 118, false⟩]) (by rfl)
  unfold _root_.Perennial.fmt.argsOkAt
  isplitl
  · unfold _root_.Perennial.fmt.argOkAt
    iright; iright; ileft
    isplitr
    · ipureintro; exact ⟨by decide, rfl, fun h => absurd h (by decide)⟩
    obtain ⟨hF, hE, hS, hC⟩ := transition_methods (GF := GF)
    iapply enum_argOk _ _ hTrS hF hE hS hC t $$ Hpkg
  · unfold _root_.Perennial.fmt.argsOkAt; itrivial

/-- The arguments of `" changes:{type:%v node_id:%d}"`. -/
private theorem changes_argsOk (hTyS : raftpb.ConfChangeType.String.spec (GF := GF) (hG := hG))
    (t : w32) (n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ⊢
      _root_.Perennial.fmt.argsOk _root_.Perennial.fmt.methodVerbs go!" changes:{type:%v node_id:%d}"
        [interface.mkOk raftpb.ConfChangeType.ty #t, interface.mkOk go.uint64 #n] := by
  iintro #Hpkg
  iapply _root_.Perennial.fmt.argsOk_intro (ds := [⟨W8 118, false⟩, ⟨W8 100, false⟩]) (by rfl)
  unfold _root_.Perennial.fmt.argsOkAt
  isplitl
  · unfold _root_.Perennial.fmt.argOkAt
    iright; iright; ileft
    isplitr
    · ipureintro; exact ⟨by decide, rfl, fun h => absurd h (by decide)⟩
    obtain ⟨hF, hE, hS, hC⟩ := type_methods (GF := GF)
    iapply enum_argOk _ _ hTyS hF hE hS hC t $$ Hpkg
  unfold _root_.Perennial.fmt.argsOkAt
  isplitl
  · unfold _root_.Perennial.fmt.argOkAt
    ileft; ipureintro
    exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 n) _root_.Perennial.fmt.ArgsWf.nil _
      (List.mem_singleton_self _)
  · unfold _root_.Perennial.fmt.argsOkAt; itrivial

omit package_sem in
/-- `%q` of the context's bytes, lent read-only. -/
private theorem context_args (cs : GoSlice) (bs : List w8) :
    cs ↦*□ bs ⊢
      _root_.Perennial.fmt.bytesOwn (GF := GF) DFrac.discard (fun _ => some bs)
        [interface.mkOk (go.GoType.SliceType go.byte) #cs] ∗
      _root_.Perennial.fmt.argsOkB (GF := GF) (fun _ => some bs) _root_.Perennial.fmt.methodVerbs
        go!" context:%q" [interface.mkOk (go.GoType.SliceType go.byte) #cs] := by
  iintro #Hcs
  isplitl
  · unfold _root_.Perennial.fmt.bytesOwn _root_.Perennial.fmt.bytesArgOwn
    isplitl
    · iexists ⟨go.GoType.SliceType go.byte, #cs⟩, cs
      iframe #
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    · iapply BigSepL.bigSepL_nil.2; itrivial
  · unfold _root_.Perennial.fmt.argsOkB
    iright
    iexists [⟨W8 113, false⟩]
    isplitr
    · ipureintro; rfl
    unfold _root_.Perennial.fmt.argsOkAtB _root_.Perennial.fmt.argOkAtB
    isplitl
    · iright; ipureintro; rfl
    · unfold _root_.Perennial.fmt.argsOkAtB; itrivial

omit package_sem in
/-- The `Context` field of a `*ConfChangeV2`, lent. -/
private theorem ownConfChangeV2_context (v : Loc) (dq : DFrac) (m : ConfChangeV2M) :
    ownConfChangeV2 (GF := GF) v dq m ⊢ ∃ cs : GoSlice,
      v.[raftpb.ConfChangeV2, go!"Context"] ↦{dq} cs ∗ cs ↦*□ m.context ∗
      (v.[raftpb.ConfChangeV2, go!"Context"] ↦{dq} cs -∗ ownConfChangeV2 v dq m) := by
  iintro Hv
  iNamed Hv
  iexists cs
  isplitl [HC]
  · iexact HC
  isplitr
  · iexact Hcs
  iintro HC
  iunfold ownConfChangeV2
  iexists pt, chs, ls, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  try iframe #

set_option hygiene false in
/-- `DescribeConfChange` after `cc.AsV2()`, from `Hv`, the `*ConfChangeV2` it returned, to the
return: the one proof of both cases. -/
local macro "describe_tail" v:term:max dq:term:max mm:term:max : tactic => `(tactic| (
  try wp_auto
  wp_apply hTr.1 $v $dq $mm $$ [Hv] as Hv
  · iframe
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  ihave Hb := strings.ownBuilder_zero b_ptr $$ b
  wp_apply fmt.wp_Fprintf (interface.mkOk (go.GoType.PointerType strings.Builder.ty) #b_ptr)
    _ _ _ (DFrac.own 1) (strings.ownBuilder b_ptr [])
    (fun bs _ _ => strings.ownBuilder b_ptr ([] ++ bs)) $$ [Hsl Hb] as %n1 %e1 ⟨Hsl, %s1, -, Hb⟩
  · iframe
    isplitl
    · iapply transition_argsOk hTrS $$ Hpb
    iexists _
    isplitr
    · ipureintro; rfl
    iapply builder_writeSpec
  try wp_auto
  wp_apply hCh.1 $v $dq $mm $$ [Hv] as %chs %ls ⟨Hchs, #Hccs, Hback⟩
  · iframe
  try wp_auto
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hccs
  wp_apply (wp_slice_for_range_ro (V := Loc) _ chs ls $dq _
    (fun _ => iprop(∃ s, strings.ownBuilder b_ptr s ∗ ∃ c : Loc, c_ptr ↦ c))) $$ Hchs [Hb c]
  · iframe
  · imodintro
    iintro %i %x %hx ⟨%s, Hb, %c0, c⟩ Hchs
    have hi : i < ls.length := (List.getElem?_eq_some_iff.1 hx).1
    ihave #Hx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => ccsRO (GF := GF) a b) hx
      (List.getElem?_eq_getElem (lt_of_lt_of_eq hi Hll)) $$ Hccs
    try wp_auto
    wp_apply hTy.1 x DFrac.discard _ $$ [] as -
    · iframe #
    try wp_auto
    wp_apply hNid.1 x DFrac.discard _ $$ [] as -
    · iframe #
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero]
    try wp_auto
    wp_apply fmt.wp_Fprintf (interface.mkOk (go.GoType.PointerType strings.Builder.ty) #b_ptr)
      _ _ _ (DFrac.own 1) (strings.ownBuilder b_ptr s)
      (fun bs _ _ => strings.ownBuilder b_ptr (s ++ bs)) $$ [Hsl2 Hb] as %n2 %e2 ⟨-, %s2, -, Hb⟩
    · iframe
      isplitl
      · iapply changes_argsOk hTyS $$ Hpb
      iexists _
      isplitr
      · ipureintro; rfl
      iapply builder_writeSpec
    try wp_auto
    isplitr
    · ipureintro; rfl
    isplitl [Hb c]
    · iexists _; iframe
    · iframe
  iintro ⟨%s, Hb, %c1, c⟩ Hchs
  ihave Hv := Hback $$ Hchs
  ihave ⟨%cs, HC, #Hcs, Hv⟩ := ownConfChangeV2_context _ _ _ $$ Hv
  try wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %sl3 ⟨Hsl3, -⟩
    try wp_auto
    ihave ⟨Hown, #Hok⟩ := context_args (GF := GF) cs _ $$ Hcs
    wp_apply fmt.wp_Fprintf_bytes _ DFrac.discard
      (interface.mkOk (go.GoType.PointerType strings.Builder.ty) #b_ptr)
      _ _ _ (DFrac.own 1) (strings.ownBuilder b_ptr s)
      (fun bs _ _ => strings.ownBuilder b_ptr (s ++ bs)) $$ [Hsl3 Hb Hown] as %n3 %e3 ⟨-, -, %s3, -, Hb⟩
    · iframe
      iframe #
      iexists _
      isplitr
      · ipureintro; rfl
      iapply builder_writeSpec
    try wp_auto
    wp_apply strings.Builder.wp_String b_ptr _ $$ Hb as Hb
    try wp_auto
    ihave Hv := Hv $$ HC
    iapply HΦ; iframe
  · try wp_auto
    wp_apply strings.Builder.wp_String b_ptr _ $$ Hb as Hb
    try wp_auto
    ihave Hv := Hv $$ HC
    iapply HΦ; iframe))

theorem DescribeConfChange.wp_proof
    (hAsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (hAsV2' : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (hTr : raftpb.ConfChangeV2.GetTransition.spec (GF := GF) (hG := hG))
    (hCh : raftpb.ConfChangeV2.GetChanges.spec (GF := GF) (hG := hG))
    (hTy : raftpb.ConfChangeSingle.GetType.spec (GF := GF) (hG := hG))
    (hNid : raftpb.ConfChangeSingle.GetNodeId.spec (GF := GF) (hG := hG))
    (hTyS : raftpb.ConfChangeType.String.spec (GF := GF) (hG := hG))
    (hTrS : raftpb.ConfChangeTransition.String.spec (GF := GF) (hG := hG)) :
    DescribeConfChange.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq m
    wp_start as Hcc
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    wp_auto
    wp_apply hAsV2 p dq m $$ [Hcc] as %v ⟨Hcc, Hv⟩
    · iframe
    describe_tail v (DFrac.own 1) m.asV2
  · intro p dq m
    wp_start as Hv
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    wp_auto
    wp_apply hAsV2' p $$ []
    describe_tail p dq m

end proof

end EtcdGrove
end Perennial
