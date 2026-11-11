/-
Lean-first (no Rocq counterpart).

# The driver's model: its Go values (stage 6a)

As linkvtxn's `Defs.lean`:

- `storeOwn s g`, `histOwn h hs`, `cfgOwn c g`: the Go store `s`'s items hold `g`'s, the history
  `h`'s nodes hold the stores `hs` (oldest first: `hs[R-1]` at revision `R`, the node of `R`
  recording its length `R`), the configuration `c`'s store, history and pending inputs hold `g`'s,
  all read-only, the history's nodes' lengths not wrapping (configurations share slices and histories: `step` returns `c.st` in a new
  configuration, `advance` a history extending `c.hist`; stage 7e, Q7e-3b-1: the state owns the
  history chain read-only);
- `boxIn x`, `boxOut y`, `boxSt sl`: a Go `Input`, `Output`, `state` boxed (`any(x)`); `decOp`, the
  model's decoder of porcupine's operations (a boxed `Input` and `Output` is the input and
  `ansOf` the output, `decOp_box`; any other pair is no operation);
- `stRepB h0 n v S`: a Go state value (a boxed `state`, its slice and configurations read-only) whose
  configurations `gs` represent `S` (`GOk`), each `Bounded n`;
- `k8setcd3S h0`, the model's `ModelSpec` from the seeded store and its history `h0`:
  `pM (kSpec h0) decOp`, `rep k` = `stRepB h0 (k + h0.st.items.length + h0.hist.length + 1)` (a
  value made by `k` steps), and `ioOk i o` (a boxed `Input` and a boxed `Output`: what `Step`'s
  type assertions need).

`Input_intoVal_inj`/`Output_intoVal_inj`: a struct's `intoVal` is injective, from the
translation's field projections (`proj_eq`, as linkvtxn's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg hnode item Input Output state)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A Go store holds `g` (see the file header). -/
def storeOwn (s : mstore) (g : GSt) : IProp GF :=
  iprop(s.items' ↦*□ g.items ∗ ⌜s.rv' = g.rv⌝)

instance storeOwn_persistent (s : mstore) (g : GSt) : Persistent (storeOwn (GF := GF) s g) := by
  unfold storeOwn; infer_instance

/-- A Go history holds the stores `hs`, newest first (see the file header). -/
def histOwnR : Loc → List GSt → IProp GF
  | h, [] => iprop(⌜h = null⌝)
  | h, s :: rest => iprop(∃ hn : hnode, h ↦□ hn ∗ storeOwn hn.st' s ∗
      ⌜hn.n' = W64 ((rest.length + 1 : Nat) : Int)⌝ ∗ histOwnR hn.prev' rest)

instance histOwnR_persistent (h : Loc) (hs : List GSt) : Persistent (histOwnR (GF := GF) h hs) := by
  induction hs generalizing h with
  | nil => unfold histOwnR; infer_instance
  | cons s rest ih => unfold histOwnR; infer_instance

/-- A Go history holds the stores `hs`, oldest first (see the file header). -/
def histOwn (h : Loc) (hs : List GSt) : IProp GF := histOwnR h hs.reverse

instance histOwn_persistent (h : Loc) (hs : List GSt) : Persistent (histOwn (GF := GF) h hs) := by
  unfold histOwn; infer_instance

theorem histOwn_nil (h : Loc) : histOwn (GF := GF) h [] ⊣⊢ iprop(⌜h = null⌝) := by
  unfold histOwn; simp only [List.reverse_nil, histOwnR]; exact .rfl

theorem histOwn_snoc (h : Loc) (hs : List GSt) (s : GSt) :
    histOwn (GF := GF) h (hs ++ [s]) ⊣⊢ iprop(∃ hn : hnode, h ↦□ hn ∗ storeOwn hn.st' s ∗
      ⌜hn.n' = W64 ((hs.length + 1 : Nat) : Int)⌝ ∗ histOwn hn.prev' hs) := by
  unfold histOwn; simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, histOwnR, List.length_reverse]; exact .rfl

/-- Two stores of the same Go store are equal. -/
theorem storeOwn_agree (st : mstore) (a b : GSt) :
    storeOwn (GF := GF) st a ⊢ storeOwn st b -∗ ⌜a = b⌝ := by
  unfold storeOwn
  iintro ⟨Ha, %Hra⟩ ⟨Hb, %Hrb⟩
  icases ownSlice_agree _ _ _ _ _ $$ Ha Hb with %He
  ipureintro
  cases a; cases b; simp_all

/-- Two histories of the same Go history, of the same length, are equal. -/
theorem histOwnR_agree (h : Loc) (a b : List GSt) :
    histOwnR (GF := GF) h a ⊢ histOwnR h b -∗ ⌜a.length = b.length → a = b⌝ := by
  induction a generalizing h b with
  | nil =>
    iintro - -; ipureintro; intro hl; cases b <;> simp_all
  | cons s rest ih =>
    cases b with
    | nil => iintro - -; ipureintro; intro hl; simp at hl
    | cons t rest' =>
      simp only [histOwnR]
      iintro ⟨%hn, #Hh, #Hs, %Hn, #Hr⟩ ⟨%hn', #Hh', #Hs', %Hn', #Hr'⟩
      icases typedPointsto_agree_wand _ _ _ _ _ $$ Hh Hh' with %He
      subst He
      icases storeOwn_agree _ _ _ $$ Hs Hs' with %Hst
      icases ih _ _ $$ Hr Hr' with %Hrest
      ipureintro
      intro hl
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [Hst, Hrest hl]

theorem histOwn_agree (h : Loc) (a b : List GSt) :
    histOwn (GF := GF) h a ⊢ histOwn h b -∗ ⌜a.length = b.length → a = b⌝ := by
  unfold histOwn
  iintro Ha Hb
  icases histOwnR_agree _ _ _ $$ Ha Hb with %H
  ipureintro
  intro hl
  have := H (by simpa using hl)
  exact List.reverse_inj.1 this

/-- A Go configuration holds `g` (see the file header). -/
def cfgOwn (c : mcfg) (g : GCfg) : IProp GF :=
  iprop(storeOwn c.st' g.st.st ∗ histOwn c.hist' g.st.hist ∗ c.pend' ↦*□ g.pend ∗
    ⌜g.st.hist.length < 2 ^ 64⌝)

instance cfgOwn_persistent (c : mcfg) (g : GCfg) : Persistent (cfgOwn (GF := GF) c g) := by
  unfold cfgOwn; infer_instance

/-- The input `x`, boxed (`any(x)`). -/
abbrev boxIn (x : Input) : GoInterface := interface.mkOk Input.ty #x

/-- The output `y`, boxed (`any(y)`). -/
abbrev boxOut (y : Output) : GoInterface := interface.mkOk Output.ty #y

/-- The state slice `sl`, boxed (`any(state(sl))`). -/
abbrev boxSt (sl : GoSlice) : GoInterface := interface.mkOk state.ty #sl

open Classical in
/-- The model's decoder of porcupine's operations (see the file header). -/
def decOp (io : github_com.anishathalye.porcupine.OpV) : Option (Input × linkv.Ans Output) :=
  if h : ∃ p : Input × Output, io = (boxIn p.1, boxOut p.2) then
    some (h.choose.1, ansOf h.choose.2)
  else none

/-- Two values with a field's deterministic projection have equal projections. -/
theorem proj_eq {t : Tag} {f : GoInstruction} {a b : val} {ea eb : Expr}
    (ha : go.IsGoStepPureDetTagged t f a ea) (hb : go.IsGoStepPureDetTagged t f b eb)
    (h : a = b) : ea = eb := by
  have h1 := ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := hb.isGoStep_det_internal.isGoStep_pure_det
  subst h
  rw [h2] at h1
  exact cast (congrFun h1 eb) rfl

include sem package_sem in
theorem Obj_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Namespace x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Namespace y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Name x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Name y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_UID x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_UID y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Value x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Value y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Node x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Node y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_App x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_App y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_ResourceVersion x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_ResourceVersion y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Annotated x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get_Annotated y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Input_intoVal_inj : Function.Injective (intoVal (V := Input)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Kind x) (Input.TypeAssumptions.get_Kind y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Key x) (Input.TypeAssumptions.get_Key y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Val x) (Input.TypeAssumptions.get_Val y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Node x) (Input.TypeAssumptions.get_Node y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_App x) (Input.TypeAssumptions.get_App y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_HasReject x) (Input.TypeAssumptions.get_HasReject y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Reject x) (Input.TypeAssumptions.get_Reject y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_NoOp x) (Input.TypeAssumptions.get_NoOp y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_IgnoreNotFound x) (Input.TypeAssumptions.get_IgnoreNotFound y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_UID x) (Input.TypeAssumptions.get_UID y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_HasPreUID x) (Input.TypeAssumptions.get_HasPreUID y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_PreUID x) (Input.TypeAssumptions.get_PreUID y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_HasPreRV x) (Input.TypeAssumptions.get_HasPreRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_PreRV x) (Input.TypeAssumptions.get_PreRV y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_UseCached x) (Input.TypeAssumptions.get_UseCached y) h))
  have := Obj_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Cached x) (Input.TypeAssumptions.get_Cached y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_MinRV x) (Input.TypeAssumptions.get_MinRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_ListKey x) (Input.TypeAssumptions.get_ListKey y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Recursive x) (Input.TypeAssumptions.get_Recursive y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Match x) (Input.TypeAssumptions.get_Match y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Field x) (Input.TypeAssumptions.get_Field y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_SelNS x) (Input.TypeAssumptions.get_SelNS y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_SelName x) (Input.TypeAssumptions.get_SelName y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_SelNode x) (Input.TypeAssumptions.get_SelNode y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_SelApp x) (Input.TypeAssumptions.get_SelApp y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Limit x) (Input.TypeAssumptions.get_Limit y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Client x) (Input.TypeAssumptions.get_Client y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_WKey x) (Input.TypeAssumptions.get_WKey y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_SendInit x) (Input.TypeAssumptions.get_SendInit y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Bookmarks x) (Input.TypeAssumptions.get_Bookmarks y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Behavior x) (Input.TypeAssumptions.get_Behavior y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Skip x) (Input.TypeAssumptions.get_Skip y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Output_intoVal_inj : Function.Injective (intoVal (V := Output)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Err x) (Output.TypeAssumptions.get_Err y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_ErrKey x) (Output.TypeAssumptions.get_ErrKey y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_ErrRV x) (Output.TypeAssumptions.get_ErrRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Namespace x) (Output.TypeAssumptions.get_Namespace y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Name x) (Output.TypeAssumptions.get_Name y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_UID x) (Output.TypeAssumptions.get_UID y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Value x) (Output.TypeAssumptions.get_Value y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Node x) (Output.TypeAssumptions.get_Node y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_App x) (Output.TypeAssumptions.get_App y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_RV x) (Output.TypeAssumptions.get_RV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Items x) (Output.TypeAssumptions.get_Items y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_ListRV x) (Output.TypeAssumptions.get_ListRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Continue x) (Output.TypeAssumptions.get_Continue y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_HasRemaining x) (Output.TypeAssumptions.get_HasRemaining y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Remaining x) (Output.TypeAssumptions.get_Remaining y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_WEvents x) (Output.TypeAssumptions.get_WEvents y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_WFailed x) (Output.TypeAssumptions.get_WFailed y) h))
  cases x; cases y; simp_all

include sem package_sem in
/-- The decoder of a boxed input and output. -/
theorem decOp_box (x : Input) (y : Output) : decOp (boxIn x, boxOut y) = some (x, ansOf y) := by
  have h : ∃ p : Input × Output, (boxIn x, boxOut y) = (boxIn p.1, boxOut p.2) := ⟨(x, y), rfl⟩
  unfold decOp
  rw [dif_pos h]
  have hs : (boxIn x, boxOut y) = (boxIn h.choose.1, boxOut h.choose.2) := h.choose_spec
  have h1 := (GoInterfaceOk.mk.inj (GoInterface.ok.inj (congrArg Prod.fst hs))).2
  have h2 := (GoInterfaceOk.mk.inj (GoInterface.ok.inj (congrArg Prod.snd hs))).2
  have e : h.choose = (x, y) :=
    Prod.ext (Input_intoVal_inj (sem := sem) (package_sem := package_sem) h1).symm
      (Output_intoVal_inj (sem := sem) (package_sem := package_sem) h2).symm
  rw [e]

/-- A Go state value represents `S`, its configurations `Bounded n` (see the file header). -/
def stRepB (g0 : HSt) (n : Nat) (v : GoInterface) (S : linkv.PSet HSt Input) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List mcfg) (gs : List GCfg),
    ⌜v = boxSt sl ∧ GOk g0 gs S ∧ ∀ g ∈ gs, Bounded n g⌝ ∗ sl ↦*□ cs ∗
      [∗list] c;g ∈ cs;gs, cfgOwn c g)

instance stRepB_persistent (g0 : HSt) (n : Nat) (v : GoInterface) (S : linkv.PSet HSt Input) :
    Persistent (stRepB (GF := GF) g0 n v S) := by
  unfold stRepB; infer_instance

/-- **The model's specification** (see the file header). -/
def k8setcd3S (g0 : HSt) : github_com.anishathalye.porcupine.ModelSpec GF (linkv.PSet HSt Input) where
  M := linkv.pM (kSpec g0) decOp
  rep k := stRepB g0 (k + g0.st.items.length + g0.hist.length + 1)
  ioOk i o := iprop(⌜∃ x y, i = boxIn x ∧ o = boxOut y⌝)
  ioOk_pers _ _ := by infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
