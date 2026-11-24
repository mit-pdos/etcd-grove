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
  `ansOf` the output's plain value, `plainOut`, which zeroes the `Raw` the model ignores, `decOp_box`; any other pair is no operation);
- `stRepB h0 n v S`: a Go state value (a boxed `state`, its slice and configurations read-only) whose
  configurations `gs` represent `S` (`GOk`), each `Bounded n`;
- `k8setcd3S h0`, the model's `ModelSpec` from the seeded store and its history `h0`:
  `pM (kSpec h0) decOp`, `rep k` = `stRepB h0 (k + h0.st.items.length + h0.hist.length + 1)` (a
  value made by `k` steps), and `ioOk i o` (a boxed `Input` and a boxed `Output`: what `Step`'s
  type assertions need; a watch's output not an error and its resource version, parsed, below
  `2^63`, stage E of 7f-6; a unary output's `Raw` what its plain fields encode, `rawOk`, unless it
  is `EOther`'s, k8s 7g step 5; the input's resource version floored at the seeded revision, and a
  watch's received events, `wrawOk`, k8s 7g step 5).

`Input_intoVal_inj`/`Output_intoVal_inj`: a struct's `intoVal` is injective, from the
translation's field projections (`proj_eq`, as linkvtxn's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RawOk

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
    some (h.choose.1, ansOf (plainOut h.choose.2))
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
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Namespace x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Namespace y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Name x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Name y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'UID x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'UID y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Value x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Value y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Node x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Node y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'App x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'App y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'ResourceVersion x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'ResourceVersion y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Annotated x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.TypeAssumptions.get'Annotated y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Input_intoVal_inj : Function.Injective (intoVal (V := Input)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Kind x) (Input.TypeAssumptions.get'Kind y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Key x) (Input.TypeAssumptions.get'Key y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Val x) (Input.TypeAssumptions.get'Val y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Node x) (Input.TypeAssumptions.get'Node y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'App x) (Input.TypeAssumptions.get'App y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'HasReject x) (Input.TypeAssumptions.get'HasReject y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Reject x) (Input.TypeAssumptions.get'Reject y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'NoOp x) (Input.TypeAssumptions.get'NoOp y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'IgnoreNotFound x) (Input.TypeAssumptions.get'IgnoreNotFound y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'UID x) (Input.TypeAssumptions.get'UID y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'HasPreUID x) (Input.TypeAssumptions.get'HasPreUID y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'PreUID x) (Input.TypeAssumptions.get'PreUID y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'HasPreRV x) (Input.TypeAssumptions.get'HasPreRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'PreRV x) (Input.TypeAssumptions.get'PreRV y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'UseCached x) (Input.TypeAssumptions.get'UseCached y) h))
  have := Obj_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Cached x) (Input.TypeAssumptions.get'Cached y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'MinRV x) (Input.TypeAssumptions.get'MinRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'ListKey x) (Input.TypeAssumptions.get'ListKey y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Recursive x) (Input.TypeAssumptions.get'Recursive y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Match x) (Input.TypeAssumptions.get'Match y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Field x) (Input.TypeAssumptions.get'Field y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'SelNS x) (Input.TypeAssumptions.get'SelNS y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'SelName x) (Input.TypeAssumptions.get'SelName y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'SelNode x) (Input.TypeAssumptions.get'SelNode y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'SelApp x) (Input.TypeAssumptions.get'SelApp y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Limit x) (Input.TypeAssumptions.get'Limit y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Client x) (Input.TypeAssumptions.get'Client y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'WKey x) (Input.TypeAssumptions.get'WKey y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'SendInit x) (Input.TypeAssumptions.get'SendInit y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Bookmarks x) (Input.TypeAssumptions.get'Bookmarks y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Behavior x) (Input.TypeAssumptions.get'Behavior y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get'Skip x) (Input.TypeAssumptions.get'Skip y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Raw_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw.TypeAssumptions.get'Object x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw.TypeAssumptions.get'Object y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw.TypeAssumptions.get'Err x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw.TypeAssumptions.get'Err y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw.TypeAssumptions.get'Events x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw.TypeAssumptions.get'Events y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Output_intoVal_inj : Function.Injective (intoVal (V := Output)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := Raw_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Raw x) (Output.TypeAssumptions.get'Raw y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Err x) (Output.TypeAssumptions.get'Err y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'ErrKey x) (Output.TypeAssumptions.get'ErrKey y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'ErrRV x) (Output.TypeAssumptions.get'ErrRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'ErrMsg x) (Output.TypeAssumptions.get'ErrMsg y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Namespace x) (Output.TypeAssumptions.get'Namespace y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Name x) (Output.TypeAssumptions.get'Name y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'UID x) (Output.TypeAssumptions.get'UID y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Value x) (Output.TypeAssumptions.get'Value y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Node x) (Output.TypeAssumptions.get'Node y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'App x) (Output.TypeAssumptions.get'App y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'RV x) (Output.TypeAssumptions.get'RV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Items x) (Output.TypeAssumptions.get'Items y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'ListRV x) (Output.TypeAssumptions.get'ListRV y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Continue x) (Output.TypeAssumptions.get'Continue y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'HasRemaining x) (Output.TypeAssumptions.get'HasRemaining y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'Remaining x) (Output.TypeAssumptions.get'Remaining y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'WEvents x) (Output.TypeAssumptions.get'WEvents y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get'WFailed x) (Output.TypeAssumptions.get'WFailed y) h))
  cases x; cases y; simp_all

include sem package_sem in
/-- The decoder of a boxed input and output. -/
theorem decOp_box (x : Input) (y : Output) : decOp (boxIn x, boxOut y) = some (x, ansOf (plainOut y)) := by
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

end defs

/-! ## The inputs `Gen` may return (moved from `Inv`/`Calls`: the model's `ioOk` names them) -/

section genIn
variable [GooseExts]

/-- The workload's keys (`workloadKeys`, 7e-0's: two levels, prefix boundaries). -/
abbrev wkKeysL : List GoString :=
  [go!"ns-1/pod-1", go!"ns-1/pod-11", go!"ns-2/pod-2", go!"ns-11/pod-1"]

/-- **An input `Gen` may return**, as far as the model needs: its key one of the workload's, its
UID, node and app fit an object's, its minimum resource version parses (stage 7b), below `2^63`;
a list's match one of the three, its key under the resource prefix, its limit not negative (stage
7e-4: `refine_list`'s and `GetList`'s premises), a key `PrepareKey` takes, short (a request's key). -/
def InOk (x : Input) : Prop :=
  x.Key' ∈ wkKeysL ∧ x.UID'.length < 256 ∧ x.Node'.length < 256 ∧ x.App'.length < 256 ∧
    (∃ n, parseRVD x.MinRV' = some n ∧ uint.Z n < 2 ^ 63) ∧
    (x.Kind' = W64 4 → (x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2) ∧
      go!"/objs/" <+: x.ListKey' ∧ 0 ≤ sint.Z x.Limit' ∧
      (k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive').isSome ∧ x.ListKey'.length ≤ 2 ^ 20)

/-- **The cached object's scope premise** (D1 of stage 7b, `notes/k8s-etcd3-plan.md`;
`issues/k8s-etcd3-cached-noop-skips-preconditions.md`): an update with a cached object carries no
resource version precondition. -/
def CachedNoRV (x : Input) : Prop :=
  x.UseCached' = true → x.Kind' = W64 2 → x.HasPreRV' = false

/-- **A list's options as `genList` draws them** (k8s 7g, gap 2: what `listOptions` needs not to
fail, `listConsL`): a match option only with a minimum resource version, and `Exact` only with a
non-zero one. -/
def ListOptOk (x : Input) : Prop :=
  x.Kind' = W64 4 → (x.MinRV' = [] → x.Match' = W64 0) ∧ (x.Match' = W64 2 → parseRVD x.MinRV' ≠ some 0)

/-- **An input `Gen` may return**, as far as `Apply` needs: its name one of the workload's keys
(`workloadKeys`), its kind one of the four, its value at most `2 ^ 20` bytes (an object it creates
or updates fits a request; 2026-10-31, `notes/invoke-size.md`, pass 4), its UID shorter than 256
bytes (`uidOf`'s two), its minimum resource version one `parseRV` takes (`minRV`'s), and no
resource version precondition on an update with a cached object (`CachedNoRV`), and a list's
options `listOptions` takes (`ListOptOk`). -/
def GenIn (x : Input) : Prop :=
  InOk x ∧ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 ∨ x.Kind' = W64 3 ∨ x.Kind' = W64 4) ∧
    x.Val'.length ≤ 2 ^ 20 ∧ CachedNoRV x ∧ ListOptOk x

/-- **A watch `Gen` may return** (stage E of 7f-6: a watcher's `genWatchFrom`, or a skipped watch):
kind 5, no cached object; unless skipped, its key under the driver's resource prefix and one
`PrepareKey` takes, short, its resource version parsed below `2^62 + 201` (G1: a cached object at
`2^62` or above counts as none), its match and initial-events options as the watch check reads
them (`WatchInOk`), a watch-list asking for bookmarks, and any other watch from revision 0 asking
for initial events (`kModeOk_of`'s premises), and no limit (`checkWatch`'s, k8s 7g); a skipped watch has no
resource version. -/
def GenInW (x : Input) : Prop :=
  x.Kind' = W64 5 ∧ x.UseCached' = false ∧ (x.Skip' = true → x.MinRV' = []) ∧
  (x.Skip' = false →
    go!"/objs/" <+: x.WKey' ∧ (k8s.prepareKeyM go!"/objs" x.WKey' x.Recursive').isSome ∧
    x.WKey'.length ≤ 2 ^ 20 ∧
    ∃ n, parseRVD x.MinRV' = some n ∧ uint.nat n < 2 ^ 62 + 201 ∧ WatchInOk x (uint.nat n) ∧
      (x.SendInit' = W64 2 → x.Bookmarks' = true) ∧
      (x.SendInit' ≠ W64 2 → x.SendInit' = W64 1 ∨ 0 < uint.nat n) ∧ x.Limit' = W64 0)

/-- **An input `Gen` may return** (stage E of 7f-6): a unary client's (`GenIn`) or a watcher's
(`GenInW`). -/
def GenInA (x : Input) : Prop := GenIn x ∨ GenInW x

end genIn

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **The model's specification** (see the file header). -/
def k8setcd3S (g0 : HSt) : github_com.anishathalye.porcupine.ModelSpec GF (linkv.PSet HSt Input) where
  M := linkv.pM (kSpec g0) decOp
  rep k := stRepB g0 (k + g0.st.items.length + g0.hist.length + 1)
  ioOk i o := iprop(∃ x y, ⌜i = boxIn x ∧ o = boxOut y ∧
    (x.Kind' = W64 5 → y.Err' ≠ W64 4 ∧ ∀ n, parseRVD x.MinRV' = some n → uint.Z n < 2 ^ 63) ∧
    GenInA x ∧ FloorOk g0.st.rv x⌝ ∗
    (⌜x.Kind' = W64 5 ∨ plainOut y = otherL⌝ ∨ k8s_correctness.rawOk x y) ∗
    (⌜x.Kind' ≠ W64 5⌝ ∨ k8s_correctness.wrawOk g0.st.rv x y))
  ioOk_pers _ _ := by infer_instance

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
