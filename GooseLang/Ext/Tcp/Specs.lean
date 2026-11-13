/-
The WP specs of the TCP extension's operations (`Impl.lean`), over its ghost state (`Ghost.lean`).

The specs of the operations on a connection end are logically atomic: the end's resources
(`tcpEnd`, `tcpOut`) are taken by an atomic update, so that a program may keep them in an
invariant shared by the threads that use the end (a reader and a writer, as grpc's and net/http's
connections have). So are `Dial`'s and `Accept`'s, over the address's pending set (`tcpPend`), which
a program keeps in an invariant with its per-address protocol. An operation that may wait
(`Read`, `Accept`) uses its update only when it returns. Each takes `tcpConnAt c a` (persistent,
from `Dial` or `Accept`): the connection exists, and its ends' ids are in range.

The outcomes are those of `Impl.lean`, as the user sees them:
* `Read`: a failure (`readRes [] 2`, the end broken unless a deadline was set); nothing from an
  empty buffer; the next bytes `bs` (the other end has written at least `sent`, whose bytes past
  those already read are `bs`: `tcpOutLb`); EOF (the other end sent its FIN after exactly the bytes
  read: `tcpFin`).
* `Write`: `k` bytes appended to the end's out-pipe (`WriteRes`).
* `Close`, `CloseWrite`: the end's FIN (`tcpOut … true` and `tcpFin`) unless it is broken.
-/
module

public import GooseLang.Ext.Tcp.Ghost
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The record algebra -/

section algebra

@[simp] theorem endSt_setEnd (cn : TcpConn) (s t : Bool) (st : TcpEnd) :
    (cn.setEnd s st).endSt t = if s = t then st else cn.endSt t := by
  cases s <;> cases t <;> rfl

@[simp] theorem out_setEnd (cn : TcpConn) (s t : Bool) (st : TcpEnd) :
    (cn.setEnd s st).out t = cn.out t := by
  cases s <;> cases t <;> rfl

@[simp] theorem endSt_setOut (cn : TcpConn) (s t : Bool) (p : TcpPipe) :
    (cn.setOut s p).endSt t = cn.endSt t := by
  cases s <;> cases t <;> rfl

@[simp] theorem out_setOut (cn : TcpConn) (s t : Bool) (p : TcpPipe) :
    (cn.setOut s p).out t = if s = t then p else cn.out t := by
  cases s <;> cases t <;> rfl

@[simp] theorem addr_setEnd (cn : TcpConn) (s : Bool) (st : TcpEnd) :
    (cn.setEnd s st).addr = cn.addr := by cases s <;> rfl
@[simp] theorem addr_setOut (cn : TcpConn) (s : Bool) (p : TcpPipe) :
    (cn.setOut s p).addr = cn.addr := by cases s <;> rfl
@[simp] theorem accepted_setEnd (cn : TcpConn) (s : Bool) (st : TcpEnd) :
    (cn.setEnd s st).accepted = cn.accepted := by cases s <;> rfl
@[simp] theorem accepted_setOut (cn : TcpConn) (s : Bool) (p : TcpPipe) :
    (cn.setOut s p).accepted = cn.accepted := by cases s <;> rfl

@[simp] theorem setConn_plan (g : TcpGlobal) (c : Nat) (cn : TcpConn) :
    (g.setConn c cn).plan = g.plan := rfl

@[simp] theorem setConn_conns (g : TcpGlobal) (c : Nat) (cn : TcpConn) :
    (g.setConn c cn).conns = g.conns.insert c cn := rfl

theorem setConn_self {g : TcpGlobal} {c : Nat} {cn : TcpConn} (h : g.conns !! c = some cn) :
    g.setConn c cn = g := by
  cases g with
  | mk plan conns =>
    simp only [TcpGlobal.setConn, TcpGlobal.mk.injEq, true_and]
    apply GMap.ext; intro k; simp only [GMap.lookup_insert_eq_iff]
    split <;> simp_all

theorem endId_inj {c c' : Nat} {s s' : Bool} (h : 2 * c + 1 < 2 ^ 64) (h' : 2 * c' + 1 < 2 ^ 64)
    (he : endId c s = endId c' s') : c = c' ∧ s = s' := by
  simp only [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at h h'
  unfold endId at he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by cases s <;> simp <;> omega),
    Nat.mod_eq_of_lt (by cases s' <;> simp <;> omega)] at this
  cases s <;> cases s' <;> simp at this ⊢ <;> omega

/-- A connection replaced by one with its address and acceptance keeps `PendOk`. -/
theorem pendOk_setConn {g : TcpGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {cn cn' : TcpConn}
    (hp : PendOk g pm) (hc : g.conns !! c = some cn) (ha : cn'.addr = cn.addr)
    (hacc : cn'.accepted = cn.accepted) : PendOk (g.setConn c cn') pm := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1, fun a S k hS => ?_, fun k cn₀ hk => ?_⟩
  · rw [h2 a S k hS]
    simp only [setConn_conns, GMap.lookup_insert_eq_iff]
    by_cases hk : c = k
    · subst hk; simp [hc, ha, hacc]
    · simp [hk]
  · simp only [setConn_conns, setConn_plan, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hck : c = k
    · subst hck; simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      rw [ha]; exact h3 c cn hc
    · simp only [hck, ↓reduceIte] at hk; exact h3 k cn₀ hk

@[simp] theorem onFail_closed (st : TcpEnd) : st.onFail.closed = st.closed := by
  unfold TcpEnd.onFail; split <;> rfl
@[simp] theorem onFail_wshut (st : TcpEnd) : st.onFail.wshut = st.wshut := by
  unfold TcpEnd.onFail; split <;> rfl
@[simp] theorem onFail_dl (st : TcpEnd) : st.onFail.dl = st.dl := by
  unfold TcpEnd.onFail; split <;> rfl

@[simp] theorem finIf_sent (st : TcpEnd) (p : TcpPipe) : (p.finIf st).sent = p.sent := by
  unfold TcpPipe.finIf; split <;> rfl
@[simp] theorem finIf_rcvd (st : TcpEnd) (p : TcpPipe) : (p.finIf st).rcvd = p.rcvd := by
  unfold TcpPipe.finIf; split <;> rfl
theorem finIf_fin (st : TcpEnd) (p : TcpPipe) : (p.finIf st).fin = (p.fin || !st.broken) := by
  unfold TcpPipe.finIf; split <;> simp_all

/-- A dial keeps `PendOk`, the new connection pending at its address. -/
theorem pendOk_dial {g : TcpGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {a h : GoString}
    {S : GSet Nat} (hp : PendOk g pm) (hc : g.conns !! c = none) (hb : 2 * c + 1 < 2 ^ 64)
    (ha : g.plan !! a = some h) (hS : pm !! a = some S) :
    PendOk (g.setConn c (TcpConn.fresh a)) (pm.insert a (S ∪ {[c]})) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun a' => ?_, fun a' S' k hS' => ?_, fun k cn hk => ?_⟩
  · simp only [GMap.lookup_insert_eq_iff, setConn_plan]
    by_cases haa : a = a'
    · subst haa; simp [ha]
    · simp [haa, h1 a']
  · simp only [GMap.lookup_insert_eq_iff] at hS'
    simp only [setConn_conns, GMap.lookup_insert_eq_iff]
    by_cases haa : a = a'
    · subst haa
      simp only [↓reduceIte, Option.some.injEq] at hS'
      subst hS'
      rw [GMap.elem_of_union, GMap.elem_of_singleton, h2 a S k hS]
      by_cases hkc : c = k
      · subst hkc; simp [hc, TcpConn.fresh]
      · simp [hkc, Ne.symm hkc]
    · simp only [haa, ↓reduceIte] at hS'
      rw [h2 a' S' k hS']
      by_cases hkc : c = k
      · subst hkc; simp [hc, TcpConn.fresh, haa]
      · simp [hkc]
  · simp only [setConn_conns, setConn_plan, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hkc : c = k
    · subst hkc
      simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      exact ⟨by simp [TcpConn.fresh, ha], hb⟩
    · simp only [hkc, ↓reduceIte] at hk; exact h3 k cn hk

/-- An accept keeps `PendOk`, the connection no longer pending. -/
theorem pendOk_accept {g : TcpGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {cn : TcpConn}
    {S : GSet Nat} (hp : PendOk g pm) (hcn : g.conns !! c = some cn)
    (hS : pm !! cn.addr = some S) :
    PendOk (g.setConn c { cn with accepted := true }) (pm.insert cn.addr (S \ {[c]})) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun a' => ?_, fun a' S' k hS' => ?_, fun k cn' hk => ?_⟩
  · simp only [GMap.lookup_insert_eq_iff, setConn_plan]
    by_cases haa : cn.addr = a'
    · subst haa; rw [← h1]; simp [hS]
    · simp [haa, h1 a']
  · simp only [GMap.lookup_insert_eq_iff] at hS'
    simp only [setConn_conns, GMap.lookup_insert_eq_iff]
    by_cases haa : cn.addr = a'
    · subst haa
      simp only [↓reduceIte, Option.some.injEq] at hS'
      subst hS'
      rw [GMap.elem_of_difference, GMap.elem_of_singleton, h2 _ S k hS]
      by_cases hkc : c = k
      · subst hkc; simp
      · simp [hkc, Ne.symm hkc]
    · simp only [haa, ↓reduceIte] at hS'
      rw [h2 a' S' k hS']
      by_cases hkc : c = k
      · subst hkc; simp [hcn, haa]
      · simp [hkc]
  · simp only [setConn_conns, setConn_plan, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hkc : c = k
    · subst hkc
      simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      exact h3 c cn hcn
    · simp only [hkc, ↓reduceIte] at hk; exact h3 k cn' hk

end algebra

/-! ## The ends' parts of the context after a change -/

section endCtx
variable {GF : BundledGFunctors} [AllG GF]

theorem finCtx_rcvd (γ : GName) (p : TcpPipe) (k : Nat) :
    finCtx (GF := GF) γ { p with rcvd := k } = finCtx γ p := rfl

theorem finCtx_rcvd_entails (γ : GName) (p : TcpPipe) (k : Nat) :
    finCtx (GF := GF) γ p ⊢ finCtx γ { p with rcvd := k } := .rfl

theorem finCtx_fin (γ : GName) (p : TcpPipe) (h : p.fin = true) :
    finCtx (GF := GF) γ p ⊣⊢ dghostVar γ .discard (some p.sent) := by
  unfold finCtx; rw [if_pos h]; exact .rfl

theorem finCtx_nofin (γ : GName) (p : TcpPipe) (h : p.fin = false) :
    finCtx (GF := GF) γ p ⊣⊢ dghostVar γ (.own (1 : Qp).half) (none : Option GoString) := by
  unfold finCtx; rw [if_neg (by simp [h])]; exact .rfl

/-- The other end's part is unchanged by a change of the end `s`'s state. -/
theorem endCtx_setEnd_other (γ : ConnNames) (s : Bool) (cn : TcpConn) (st : TcpEnd) :
    endCtx (GF := GF) γ (!s) (cn.setEnd s st) = endCtx γ (!s) cn := by
  cases s <;> rfl

/-- The end `s`'s part, after a change of its state. -/
theorem endCtx_setEnd_self (γ : ConnNames) (s : Bool) (cn : TcpConn) (st : TcpEnd) :
    endCtx (GF := GF) γ s (cn.setEnd s st) =
      iprop(ghostVar (γ.v s) (1 : Qp).half (st, (cn.out (!s)).rcvd) ∗
        monoListAuthOwn (γ.out s) (1 : Qp).half (cn.out s).sent ∗
        finCtx (γ.fin s) (cn.out s) ∗
        ⌜(cn.out s).rcvd ≤ (cn.out s).sent.length ∧
          ((cn.out s).fin = true → st.closed = true ∨ st.wshut = true)⌝) := by
  cases s <;> rfl

/-- The end `s`'s part, after the end reads (its in-pipe, the other end's out-pipe, changes). -/
theorem endCtx_setIn_self (γ : ConnNames) (s : Bool) (cn : TcpConn) (p : TcpPipe) :
    endCtx (GF := GF) γ s (cn.setOut (!s) p) =
      iprop(ghostVar (γ.v s) (1 : Qp).half (cn.endSt s, p.rcvd) ∗
        monoListAuthOwn (γ.out s) (1 : Qp).half (cn.out s).sent ∗
        finCtx (γ.fin s) (cn.out s) ∗
        ⌜(cn.out s).rcvd ≤ (cn.out s).sent.length ∧
          ((cn.out s).fin = true → (cn.endSt s).closed = true ∨ (cn.endSt s).wshut = true)⌝) := by
  cases s <;> rfl

/-- The other end's part, after the end `s` reads: its out-pipe with a new read count. -/
theorem endCtx_setIn_other (γ : ConnNames) (s : Bool) (cn : TcpConn) (p : TcpPipe) :
    endCtx (GF := GF) γ (!s) (cn.setOut (!s) p) =
      iprop(ghostVar (γ.v (!s)) (1 : Qp).half (cn.endSt (!s), (cn.out s).rcvd) ∗
        monoListAuthOwn (γ.out (!s)) (1 : Qp).half p.sent ∗
        finCtx (γ.fin (!s)) p ∗
        ⌜p.rcvd ≤ p.sent.length ∧
          (p.fin = true → (cn.endSt (!s)).closed = true ∨ (cn.endSt (!s)).wshut = true)⌝) := by
  cases s <;> rfl

/-- The end `s`'s part, after a change of its out-pipe and its state. -/
theorem endCtx_setOutEnd_self (γ : ConnNames) (s : Bool) (cn : TcpConn) (p : TcpPipe)
    (st : TcpEnd) :
    endCtx (GF := GF) γ s ((cn.setOut s p).setEnd s st) =
      iprop(ghostVar (γ.v s) (1 : Qp).half (st, (cn.out (!s)).rcvd) ∗
        monoListAuthOwn (γ.out s) (1 : Qp).half p.sent ∗
        finCtx (γ.fin s) p ∗
        ⌜p.rcvd ≤ p.sent.length ∧ (p.fin = true → st.closed = true ∨ st.wshut = true)⌝) := by
  cases s <;> rfl

/-- The other end's part, after a change of the end `s`'s out-pipe and state. -/
theorem endCtx_setOutEnd_other (γ : ConnNames) (s : Bool) (cn : TcpConn) (p : TcpPipe)
    (st : TcpEnd) :
    endCtx (GF := GF) γ (!s) ((cn.setOut s p).setEnd s st) =
      iprop(ghostVar (γ.v (!s)) (1 : Qp).half (cn.endSt (!s), p.rcvd) ∗
        monoListAuthOwn (γ.out (!s)) (1 : Qp).half (cn.out (!s)).sent ∗
        finCtx (γ.fin (!s)) (cn.out (!s)) ∗
        ⌜(cn.out (!s)).rcvd ≤ (cn.out (!s)).sent.length ∧
          ((cn.out (!s)).fin = true → (cn.endSt (!s)).closed = true ∨
            (cn.endSt (!s)).wshut = true)⌝) := by
  cases s <;> rfl

/-- The end `s`'s part, unfolded. -/
theorem endCtx_eq (γ : ConnNames) (s : Bool) (cn : TcpConn) :
    endCtx (GF := GF) γ s cn =
      iprop(ghostVar (γ.v s) (1 : Qp).half (cn.endSt s, (cn.out (!s)).rcvd) ∗
        monoListAuthOwn (γ.out s) (1 : Qp).half (cn.out s).sent ∗
        finCtx (γ.fin s) (cn.out s) ∗
        ⌜(cn.out s).rcvd ≤ (cn.out s).sent.length ∧
          ((cn.out s).fin = true → (cn.endSt s).closed = true ∨ (cn.endSt s).wshut = true)⌝) :=
  rfl

theorem mono_half_split {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ 1 l ⊣⊢
      iprop(monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l) := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (monoListAuthOwn_fractional γ l).fractional _ _

/-- The two halves of a monotone list agree, and append together. -/
theorem mono_halves_app {A : Type} [Pos.Countable A] (γ : GName) (l l' x : List A) :
    monoListAuthOwn (GF := GF) γ (1 : Qp).half l -∗ monoListAuthOwn γ (1 : Qp).half l' ==∗
      ⌜l = l'⌝ ∗ monoListAuthOwn γ (1 : Qp).half (l ++ x) ∗
        monoListAuthOwn γ (1 : Qp).half (l ++ x) := by
  iintro H1 H2
  icases monoListAuthOwn_agree γ _ _ l l' $$ H1 H2 with %Hag
  obtain ⟨-, rfl⟩ := Hag
  ihave H := (mono_half_split γ l).mpr $$ [H1 H2]
  · iframe H1 H2
  imod monoListAuthOwn_update_app x $$ H with ⟨H, -⟩
  icases (mono_half_split γ (l ++ x)).mp $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2
  ipureintro; rfl

/-- The writer's FIN flag is the network's. -/
theorem fin_agree (γ : GName) (bs : GoString) (f : Bool) (p : TcpPipe) :
    (if f then dghostVar (GF := GF) γ .discard (some bs)
      else dghostVar γ (.own (1 : Qp).half) (none : Option GoString)) -∗ finCtx γ p -∗
      ⌜f = p.fin ∧ (f = true → bs = p.sent)⌝ := by
  unfold finCtx
  iintro H1 H2
  cases f <;> cases hp : p.fin <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · ipureintro; simp
  · icases dghostVar_agree $$ H1 H2 with %Hag; cases Hag
  · icases dghostVar_agree $$ H1 H2 with %Hag; cases Hag
  · icases dghostVar_agree $$ H1 H2 with %Hag
    ipureintro; simpa using Hag

/-- A close (or a shutdown of the write side) by an end in state `st`: the FIN of its out-pipe
`p`, unless the end is broken. -/
theorem fin_close (γ : GName) (p : TcpPipe) (st : TcpEnd) :
    (if p.fin then dghostVar (GF := GF) γ .discard (some p.sent)
      else dghostVar γ (.own (1 : Qp).half) (none : Option GoString)) -∗ finCtx γ p ==∗
    (if (p.fin || !st.broken) then dghostVar (GF := GF) γ .discard (some p.sent)
      else dghostVar γ (.own (1 : Qp).half) (none : Option GoString)) ∗ finCtx γ (p.finIf st) := by
  unfold finCtx TcpPipe.finIf
  iintro H1 H2
  cases hf : p.fin <;> cases hb : st.broken <;>
    simp only [hf, hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      Bool.or_true, Bool.or_false]
  · imod dghostVar_update_halves (some p.sent) $$ H1 H2 with ⟨H1, H2⟩
    imod dghostVar_persist $$ H1 with H1
    imod dghostVar_persist $$ H2 with H2
    imodintro
    iframe H1 H2
  all_goals (imodintro; iframe H1 H2)

theorem ghostVar_alloc_halves {A : Type} [Pos.Countable A] (a : A) :
    ⊢ |==> ∃ γ, ghostVar (GF := GF) γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  imod ghostVar_alloc (GF := GF) a with ⟨%γ, H⟩
  icases (ghostVar_split_half γ 1 a).mp $$ H with ⟨H1, H2⟩
  imodintro
  iexists γ
  iframe H1 H2

theorem mono_alloc_halves {A : Type} [Pos.Countable A] (l : List A) :
    ⊢ |==> ∃ γ, monoListAuthOwn (GF := GF) γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  imod mono_list_own_alloc (GF := GF) l with ⟨%γ, H, -⟩
  icases (mono_half_split γ l).mp $$ H with ⟨H1, H2⟩
  imodintro
  iexists γ
  iframe H1 H2

theorem dghostVar_alloc_halves {A : Type} [Pos.Countable A] (a : A) :
    ⊢ |==> ∃ γ, dghostVar (GF := GF) γ (.own (1 : Qp).half) a ∗
      dghostVar γ (.own (1 : Qp).half) a := by
  have Ha := dghostVar_alloc (GF := GF) a
  rw [show (DFrac.own (1 : Qp) : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half by
    rw [DFrac.op_own, Qp.half_add_half]] at Ha
  imod Ha with ⟨%γ, H⟩
  icases dghostVar_split γ a _ _ $$ H with ⟨H1, H2⟩
  imodintro
  iexists γ
  iframe H1 H2

/-- The end `s`'s part of a new connection. -/
theorem endCtx_fresh (γ : ConnNames) (s : Bool) (a : GoString) :
    endCtx (GF := GF) γ s (TcpConn.fresh a) =
      iprop(ghostVar (γ.v s) (1 : Qp).half (TcpEnd.fresh, 0) ∗
        monoListAuthOwn (γ.out s) (1 : Qp).half ([] : GoString) ∗
        dghostVar (γ.fin s) (.own (1 : Qp).half) (none : Option GoString) ∗
        ⌜0 ≤ ([] : GoString).length ∧ (false = true → false = true ∨ false = true)⌝) := by
  cases s <;> rfl

end endCtx

/-! ## Opening the network -/

section acc
variable {GF : BundledGFunctors}

/-- The connection `c` with names `γ`: its record, its part of the context, and the context back
for any record of the same address and acceptance. -/
theorem tcpCtx_acc (hG : TcpGS GF) (g : TcpGlobal) (c : Nat) (γ : ConnNames) :
    tcpCtx hG g -∗ tcpNames hG c γ -∗
      ∃ cn, ⌜g.conns !! c = some cn⌝ ∗ @connCtx GF hG.allG γ cn ∗
        ∀ cn', ⌜cn'.addr = cn.addr ∧ cn'.accepted = cn.accepted⌝ -∗
          @connCtx GF hG.allG γ cn' -∗ tcpCtx hG (g.setConn c cn') := by
  letI := hG.allG
  unfold tcpCtx tcpNames
  iintro ⟨%nm, %pm, Hn, Hp, Hl, %Hpure, Hconns⟩ #Hγ
  obtain ⟨Hdom, Hpend⟩ := Hpure
  icases ghost_map_lookup $$ Hn Hγ with %Hnγ
  have hsome : (g.conns !! c).isSome := by rw [← Hdom c]; simp [Hnγ]
  obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hsome
  icases BigSepM.bigSepM_insert_acc hcn $$ Hconns with ⟨⟨%γ', %Hγ', #Hn', Hcc⟩, Hclose⟩
  have : γ' = γ := by
    rw [Hnγ] at Hγ'; exact (Option.some.inj Hγ').symm
  subst this
  iexists cn
  isplitr
  · ipureintro; exact hcn
  iframe Hcc
  iintro %cn' %Hah Hcc'
  obtain ⟨ha, hacc⟩ := Hah
  iexists nm, pm
  rw [setConn_plan]
  iframe Hn Hp Hl
  isplitr
  · ipureintro
    refine ⟨fun k => ?_, pendOk_setConn Hpend hcn ha hacc⟩
    rw [Hdom k]; simp only [setConn_conns, GMap.lookup_insert_eq_iff]
    by_cases hk : c = k
    · subst hk; simp [hcn]
    · simp [hk]
  · rw [setConn_conns]
    iapply Hclose
    iexists γ'
    iframe Hcc' Hn'
    ipureintro; exact Hγ'

theorem tcpCtx_of_eq (hG : TcpGS GF) {g g' : TcpGlobal} (h : g' = g) :
    tcpCtx hG g' ⊢ tcpCtx hG g := by subst h; exact .rfl

/-- `connCtx` by the end `s` and the other one. -/
theorem connCtx_ends [AllG GF] (γ : ConnNames) (cn : TcpConn) (s : Bool) :
    connCtx (GF := GF) γ cn ⊣⊢ iprop(⌜γ.addr = cn.addr⌝ ∗ endCtx γ s cn ∗ endCtx γ (!s) cn) := by
  unfold connCtx
  cases s
  · exact .rfl
  · simp only [Bool.not_true]
    constructor
    · iintro ⟨$, H0, H1⟩; iframe
    · iintro ⟨$, H1, H0⟩; iframe

theorem tcpNames_agree (hG : TcpGS GF) (c : Nat) (γ γ' : ConnNames) :
    tcpNames hG c γ -∗ tcpNames hG c γ' -∗ ⌜γ = γ'⌝ := by
  letI := hG.allG
  unfold tcpNames
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- The connection `c` is in the network (the context is kept). -/
theorem tcpCtx_lookup (hG : TcpGS GF) (g : TcpGlobal) (c : Nat) (γ : ConnNames) :
    tcpCtx hG g -∗ tcpNames hG c γ -∗ ⌜∃ cn, g.conns !! c = some cn⌝ ∗ tcpCtx hG g := by
  letI := hG.allG
  unfold tcpCtx tcpNames
  iintro ⟨%nm, %pm, Hn, Hp, Hl, %Hpure, Hconns⟩ #Hγ
  obtain ⟨Hdom, Hpend⟩ := Hpure
  icases ghost_map_lookup $$ Hn Hγ with %Hnγ
  have hsome : (g.conns !! c).isSome := by rw [← Hdom c]; simp [Hnγ]
  isplitr
  · ipureintro; exact Option.isSome_iff_exists.mp hsome
  iexists nm, pm
  iframe Hn Hp Hl Hconns
  ipureintro; exact ⟨Hdom, Hpend⟩

end acc

/-! ## The resources' laws -/

section laws
variable {GF : BundledGFunctors}

/-- Two lower bounds of one end's bytes: one is a prefix of the other. -/
theorem tcpOutLb_valid (hG : TcpGS GF) (c : Nat) (s : Bool) (l1 l2 : GoString) :
    tcpOutLb hG c s l1 -∗ tcpOutLb hG c s l2 -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  letI := hG.allG
  unfold tcpOutLb
  iintro ⟨%γ1, #H1, #L1⟩ ⟨%γ2, #H2, #L2⟩
  icases tcpNames_agree hG c γ1 γ2 $$ H1 H2 with %e
  subst e
  iapply mono_list_lb_valid $$ L1 L2

/-- A lower bound of an end's bytes is a prefix of them. -/
theorem tcpOut_lb_prefix (hG : TcpGS GF) (c : Nat) (s : Bool) (bs : GoString) (f : Bool)
    (l : GoString) :
    tcpOut hG c s bs f -∗ tcpOutLb hG c s l -∗ ⌜l <+: bs⌝ := by
  letI := hG.allG
  unfold tcpOut tcpOutLb
  iintro ⟨%γ1, #H1, M, -, -⟩ ⟨%γ2, #H2, #L⟩
  icases tcpNames_agree hG c γ1 γ2 $$ H1 H2 with %e
  subst e
  icases mono_list_auth_lb_valid $$ M L with %h
  ipureintro; exact h.2

/-- An end's bytes are a lower bound of them. -/
theorem tcpOut_lb (hG : TcpGS GF) (c : Nat) (s : Bool) (bs : GoString) (f : Bool) :
    tcpOut hG c s bs f -∗ tcpOutLb hG c s bs := by
  letI := hG.allG
  unfold tcpOut tcpOutLb
  iintro ⟨%γ, #H, M, -, -⟩
  iexists γ
  iframe H
  iapply monoListLbOwn_get $$ M

/-- Nothing is a lower bound of any end's bytes. -/
theorem tcpOutLb_nil (hG : TcpGS GF) (c : Nat) (s : Bool) (a : GoString) :
    tcpConnAt hG c a ==∗ tcpOutLb hG c s [] := by
  letI := hG.allG
  unfold tcpConnAt tcpOutLb
  iintro ⟨%γ, #H, -⟩
  imod monoListLbOwn_nil (γ.out s) with L
  imodintro
  iexists γ
  iframe H L

/-- A FIN of an end agrees with the end's bytes and FIN flag: it was sent, after them. -/
theorem tcpOut_fin (hG : TcpGS GF) (c : Nat) (s : Bool) (bs : GoString) (f : Bool)
    (bs' : GoString) :
    tcpOut hG c s bs f -∗ tcpFin hG c s bs' -∗ ⌜f = true ∧ bs' = bs⌝ := by
  letI := hG.allG
  unfold tcpOut tcpFin
  iintro ⟨%γ1, #H1, -, Hf, -⟩ ⟨%γ2, #H2, #F⟩
  icases tcpNames_agree hG c γ1 γ2 $$ H1 H2 with %e
  subst e
  cases f
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases dghostVar_agree $$ Hf F with %h; cases h
  · simp only [↓reduceIte]
    icases dghostVar_agree $$ Hf F with %h
    ipureintro; exact ⟨trivial, (Option.some.inj h).symm⟩

/-- An end's written bytes are owned once. -/
theorem tcpOut_excl (hG : TcpGS GF) (c : Nat) (s : Bool) (bs bs' : GoString) (f f' : Bool) :
    tcpOut hG c s bs f -∗ tcpOut hG c s bs' f' -∗ False := by
  letI := hG.allG
  unfold tcpOut
  iintro ⟨%γ1, #H1, -, -, T1⟩ ⟨%γ2, #H2, -, -, T2⟩
  icases tcpNames_agree hG c γ1 γ2 $$ H1 H2 with %e
  subst e
  iapply token_exclusive $$ T1 T2

/-- An end that has sent its FIN: the FIN, after its bytes. -/
theorem tcpOut_fin_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (bs : GoString) :
    tcpOut hG c s bs true -∗ tcpFin hG c s bs := by
  letI := hG.allG
  unfold tcpOut tcpFin
  simp only [↓reduceIte]
  iintro ⟨%γ, #H, -, #F, -⟩
  iexists γ
  iframe H F

end laws

/-! ## The specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {sk : Stuckness} {E : CoPset}

/-- The network's ghost state. -/
abbrev tcpG : TcpGS GF := extGlobalGS tcpExt

/-- This node's ghost state. -/
abbrev tcpL : TcpLocalGS GF := extLocalGS tcpExt (L := L)

theorem tcp_local_ctx_eq (σ : TcpLocal) :
    ExtInterp.localCtx (E := tcpExt) (extLocalGS tcpExt (L := L) (GF := GF)) σ ⊣⊢
      tcpLocalCtx (tcpL (L := L)) σ := .rfl

theorem tcp_global_ctx_eq (g : TcpGlobal) :
    ExtInterp.globalCtx (E := tcpExt) (extGlobalGS tcpExt (G := G)) g ⊣⊢ tcpCtx (tcpG (G := G)) g :=
  .rfl

/-- What a read of `n` bytes by the end `s` of `c`, whose state was `st` with `r` bytes read,
gives with its result `res`: a failure; nothing from an empty buffer; the bytes `bs`, which follow
the `r` already read in what the other end has written (`sent`, a prefix of its bytes); or EOF, the
other end's FIN after exactly the `r` bytes read. -/
def ReadPost (hG : TcpGS GF) (c : Nat) (s : Bool) (n : w64) (st : TcpEnd) (r : Nat)
    (res : val) : IProp GF :=
  iprop(
    (⌜res = readRes [] 2⌝ ∗ tcpEnd hG c s st.onFail r) ∨
    (⌜st.closed = false ∧ n = 0 ∧ res = readRes [] 0⌝ ∗ tcpEnd hG c s st r) ∨
    (∃ (bs sent : GoString), ⌜st.closed = false ∧ 1 ≤ bs.length ∧ bs.length ≤ n.toNat ∧
        sent.length = r + bs.length ∧ sent.drop r = bs ∧ res = readRes bs 0⌝ ∗
      tcpOutLb hG c (!s) sent ∗ tcpEnd hG c s st (r + bs.length)) ∨
    (∃ sent : GoString, ⌜st.closed = false ∧ sent.length = r ∧ res = readRes [] 1⌝ ∗
      tcpFin hG c (!s) sent ∗ tcpEnd hG c s st r))

theorem pair_w64_inj {e e' n n' : w64} (h : PairV (#e) (#n) = PairV (#e') (#n')) :
    e = e' ∧ n = n' := by
  obtain ⟨h1, h2⟩ := val.PairV.inj h
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

/-- The end's resource agrees with the network: its names are the connection's, and its state and
read count are the network's. -/
theorem tcpEnd_agree (hG : TcpGS GF) (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat) (γ : ConnNames)
    (cn : TcpConn) :
    tcpNames hG c γ -∗ tcpEnd hG c s st r -∗
      @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half (cn.endSt s, (cn.out (!s)).rcvd) -∗
      ⌜st = cn.endSt s ∧ r = (cn.out (!s)).rcvd⌝ ∗
        @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half (st, r) ∗
        @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half (cn.endSt s, (cn.out (!s)).rcvd) := by
  letI := hG.allG
  unfold tcpEnd
  iintro #Hγ ⟨%γ', #Hγ', Hv⟩ Hc
  icases tcpNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  icases ghostVar_agree $$ Hv Hc with %Hag
  obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
  isplitr
  · ipureintro; exact ⟨h1, h2⟩
  iframe Hv Hc

theorem tcpEnd_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat)
    (γ : ConnNames) :
    tcpNames hG c γ -∗ @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half (st, r) -∗
      tcpEnd hG c s st r := by
  letI := hG.allG
  unfold tcpEnd
  iintro #Hγ Hv
  iexists γ
  iframe Hγ Hv

/-- `Read` of `n` bytes by the end `s` of `c` (`ReadPost`). The update is used only when the read
returns. -/
theorem wp_tcp_Read (c : Nat) (s : Bool) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st r, tcpEnd tcpG c s st r ∗
      ∀ res, ReadPost tcpG c s n st r res ={∅,E}=∗ Φ res) -∗
    WP (ExternalOp tcpExt.name "Read" (Val (PairV (#(endId c s)) (#n)))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat
  unfold tcpConnAt
  icases Hat with ⟨%γ, #Hγ, %Hγa⟩
  iloeb as IH
  iintro HAU
  iapply wp_extStep "Read" (PairV (#(endId c s)) (#n)) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  icases tcpCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hex, Hg⟩
  obtain ⟨cn, hcn⟩ := Hex
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ, g, rfl, endId c s, n, c, s, rfl, ⟨Hγa.2, rfl⟩,
      ⟨cn, hcn, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, e0, n0, c0, s0, Hv, ⟨Hb0, He0⟩, Hrs, rfl⟩ := Hst
  obtain ⟨He, rfl⟩ := pair_w64_inj Hv
  obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2 Hb0 (He.trans He0)
  imod Hclose
  obtain ⟨cn', hcn', Hcase⟩ := Hrs
  rw [hcn] at hcn'
  cases hcn'
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨Hopen, Hcase⟩
  · -- it waits
    imodintro
    iframe Hheap Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply IH
    iexact HAU
  · -- a failure
    imod HAU with ⟨%st, %r, Hend, Hk⟩
    icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn2, %hcn2, Hcc, Hgclose⟩
    rw [hcn] at hcn2; cases hcn2
    icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
    rw [endCtx_eq γ s cn]
    icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
    icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
    obtain ⟨rfl, rfl⟩ := Hagr
    imod ghostVar_update_halves ((cn.endSt s).onFail, (cn.out (!s)).rcvd) $$ Hv Hgv
      with ⟨Hv, Hgv⟩
    imod Hk $$ %(readRes [] 2) [Hv] with HΦ
    · unfold ReadPost
      ileft
      isplitr
      · ipureintro; rfl
      iapply tcpEnd_intro $$ Hγ Hv
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · iapply (tcp_global_ctx_eq _).mpr
      iapply Hgclose $$ %(cn.setEnd s (cn.endSt s).onFail) %(And.intro (by simp) (by simp))
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_setEnd_other, endCtx_setEnd_self]
      iframe Heo Hgv Hmono Hfin
      ipureintro
      refine ⟨by simpa using Haddr, Hpure.1, fun hf => by simpa using Hpure.2 hf⟩
    iapply wp_value'
    iexact HΦ
  · obtain ⟨Hz, rfl, Hgg⟩ | ⟨k, hk1, hkn, hkr, rfl, rfl⟩ | ⟨Hr, Hf, rfl, Hgg⟩ := Hcase
    · -- an empty buffer
      imod HAU with ⟨%st, %r, Hend, Hk⟩
      icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn2, %hcn2, Hcc, Hgclose⟩
      rw [hcn] at hcn2; cases hcn2
      icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
      rw [endCtx_eq γ s cn]
      icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
      icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
      obtain ⟨rfl, rfl⟩ := Hagr
      imod Hk $$ %(readRes [] 0) [Hv] with HΦ
      · unfold ReadPost
        iright; ileft
        isplitr
        · ipureintro; exact ⟨Hopen, Hz, rfl⟩
        iapply tcpEnd_intro $$ Hγ Hv
      imodintro
      iframe Hheap Hl
      isplitr [HΦ]
      · rw [Hgg]
        iapply (tcp_global_ctx_eq _).mpr
        iapply tcpCtx_of_eq _ (setConn_self hcn)
        iapply Hgclose $$ %cn %(And.intro rfl rfl)
        iapply (connCtx_ends γ _ s).mpr
        rw [endCtx_eq γ s cn]
        iframe Heo Hgv Hmono Hfin
        ipureintro; exact ⟨Haddr, Hpure⟩
      iapply wp_value'
      iexact HΦ
    · -- the next `k` bytes
      imod HAU with ⟨%st, %r, Hend, Hk⟩
      icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn2, %hcn2, Hcc, Hgclose⟩
      rw [hcn] at hcn2; cases hcn2
      icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
      rw [endCtx_eq γ s cn, endCtx_eq γ (!s) cn]
      icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
      icases Heo with ⟨Hgvo, Hmonoo, Hfino, %Hpureo⟩
      icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
      obtain ⟨rfl, rfl⟩ := Hagr
      simp only [Bool.not_not] at Hpureo ⊢
      imod ghostVar_update_halves (cn.endSt s, (cn.out (!s)).rcvd + k) $$ Hv Hgv
        with ⟨Hv, Hgv⟩
      ihave #Hlb := monoListLbOwn_get _ _ _ $$ Hmonoo
      ihave #Hlb' := monoListLbOwn_le ((cn.out (!s)).sent.take ((cn.out (!s)).rcvd + k))
        (List.take_prefix _ _) $$ Hlb
      have hlen : (((cn.out (!s)).sent.drop (cn.out (!s)).rcvd).take k).length = k := by
        simp only [List.length_take, List.length_drop]; omega
      imod Hk $$ %(readRes (((cn.out (!s)).sent.drop (cn.out (!s)).rcvd).take k) 0) [Hv] with HΦ
      · unfold ReadPost
        iright; iright; ileft
        iexists ((cn.out (!s)).sent.drop (cn.out (!s)).rcvd).take k,
          (cn.out (!s)).sent.take ((cn.out (!s)).rcvd + k)
        isplitr
        · ipureintro
          refine ⟨Hopen, by rw [hlen]; omega, by rw [hlen]; omega, ?_, ?_, rfl⟩
          · rw [hlen]; simp only [List.length_take]; omega
          · rw [List.drop_take]; congr 1; omega
        isplitr
        · unfold tcpOutLb; iexists γ; iframe Hγ Hlb'
        rw [hlen]
        iapply tcpEnd_intro $$ Hγ Hv
      imodintro
      iframe Hheap Hl
      isplitr [HΦ]
      · iapply (tcp_global_ctx_eq _).mpr
        iapply Hgclose $$ %(cn.setOut (!s) { cn.out (!s) with rcvd := (cn.out (!s)).rcvd + k })
          %(And.intro (by simp) (by simp))
        iapply (connCtx_ends γ _ s).mpr
        rw [endCtx_setIn_other, endCtx_setIn_self]
        ihave Hfino := finCtx_rcvd_entails _ (cn.out (!s)) ((cn.out (!s)).rcvd + k) $$ Hfino
        dsimp only
        iframe Hgv Hmono Hfin Hgvo Hmonoo Hfino
        ipureintro
        refine ⟨by simpa using Haddr, Hpure, by simpa using hkr, Hpureo.2⟩
      iapply wp_value'
      iexact HΦ
    · -- EOF
      imod HAU with ⟨%st, %r, Hend, Hk⟩
      icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn2, %hcn2, Hcc, Hgclose⟩
      rw [hcn] at hcn2; cases hcn2
      icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
      rw [endCtx_eq γ s cn, endCtx_eq γ (!s) cn]
      icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
      icases Heo with ⟨Hgvo, Hmonoo, Hfino, %Hpureo⟩
      icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
      obtain ⟨rfl, rfl⟩ := Hagr
      simp only [Bool.not_not] at Hpureo ⊢
      icases (finCtx_fin _ _ Hf).mp $$ Hfino with #Hfino
      imod Hk $$ %(readRes [] 1) [Hv] with HΦ
      · unfold ReadPost
        iright; iright; iright
        iexists (cn.out (!s)).sent
        isplitr
        · ipureintro; exact ⟨Hopen, Hr.symm, rfl⟩
        isplitr
        · unfold tcpFin; iexists γ; iframe Hγ Hfino
        iapply tcpEnd_intro $$ Hγ Hv
      imodintro
      iframe Hheap Hl
      isplitr [HΦ]
      · rw [Hgg]
        iapply (tcp_global_ctx_eq _).mpr
        iapply tcpCtx_of_eq _ (setConn_self hcn)
        iapply Hgclose $$ %cn %(And.intro rfl rfl)
        iapply (connCtx_ends γ _ s).mpr
        rw [endCtx_eq γ s cn, endCtx_eq γ (!s) cn]
        simp only [Bool.not_not]
        ihave Hfino' := (finCtx_fin _ _ Hf).mpr $$ Hfino
        iframe Hgv Hmono Hfin Hgvo Hmonoo Hfino'
        ipureintro; exact ⟨Haddr, Hpure, by simpa using Hpureo⟩
      iapply wp_value'
      iexact HΦ

/-- The outcomes of a write of `bs` by an end in state `st`: `k` bytes written, `ok` its result,
`st'` the end's state after it. Nothing, and a failure, once the end is closed, shut for writing
or broken; otherwise all of `bs`, or a shorter prefix and a failure (the end broken unless a
deadline was set). -/
def WriteRes (st : TcpEnd) (bs : GoString) (k : Nat) (ok : Bool) (st' : TcpEnd) : Prop :=
  (st.blocked = true ∧ k = 0 ∧ ok = false ∧ st' = st) ∨
  (st.blocked = false ∧
    ((k = bs.length ∧ ok = true ∧ st' = st) ∨ (k < bs.length ∧ ok = false ∧ st' = st.onFail)))

theorem tcpOut_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (bs : GoString) (f : Bool)
    (γ : ConnNames) :
    tcpNames hG c γ -∗ @monoListAuthOwn GF hG.allG _ _ (γ.out s) (1 : Qp).half bs -∗
      (if f then @dghostVar GF hG.allG _ _ (γ.fin s) .discard (some bs)
        else @dghostVar GF hG.allG _ _ (γ.fin s) (.own (1 : Qp).half) (none : Option GoString)) -∗
      @token GF hG.allG (γ.tk s) -∗
      tcpOut hG c s bs f := by
  letI := hG.allG
  unfold tcpOut
  iintro #Hγ Hm Hf Htk
  iexists γ
  iframe Hγ Hm Hf Htk

theorem tcpOut_elim (hG : TcpGS GF) (c : Nat) (s : Bool) (bs : GoString) (f : Bool) :
    tcpOut hG c s bs f ⊢ ∃ γ, tcpNames hG c γ ∗
      @monoListAuthOwn GF hG.allG _ _ (γ.out s) (1 : Qp).half bs ∗
      (if f then @dghostVar GF hG.allG _ _ (γ.fin s) .discard (some bs)
        else @dghostVar GF hG.allG _ _ (γ.fin s) (.own (1 : Qp).half) (none : Option GoString)) ∗
      @token GF hG.allG (γ.tk s) :=
  .rfl

theorem setEnd_endSt_setOut (cn : TcpConn) (s : Bool) (p : TcpPipe) :
    (cn.setOut s p).setEnd s (cn.endSt s) = cn.setOut s p := by
  cases s <;> rfl

theorem W64_zero : (W64 0 : w64) = BitVec.ofNat 64 0 := rfl

theorem ite_false_ent {P Q R : IProp GF} {f : Bool} (h : f = false) :
    (if f then P else Q) ⊢ (if f then R else Q) := by subst h; exact .rfl

/-- `Write` of `bs` by the end `s` of `c`: `k` bytes appended (`WriteRes`). -/
theorem wp_tcp_Write (c : Nat) (s : Bool) (a : GoString) (bs : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st r out f, tcpEnd tcpG c s st r ∗ tcpOut tcpG c s out f ∗
      ∀ k ok st', ⌜WriteRes st bs k ok st'⌝ -∗ tcpEnd tcpG c s st' r -∗
        tcpOut tcpG c s (out ++ bs.take k) f ={∅,E}=∗ Φ (PairV (#(BitVec.ofNat 64 k)) (#ok))) -∗
    WP (ExternalOp tcpExt.name "Write" (Val (PairV (#(endId c s)) (#bs)))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat HAU
  unfold tcpConnAt
  icases Hat with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_extStep "Write" (PairV (#(endId c s)) (#bs)) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  imod HAU with ⟨%st, %r, %out, %f, Hend, Hout, Hk⟩
  icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn, %hcn, Hcc, Hgclose⟩
  icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
  rw [endCtx_eq γ s cn]
  icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
  icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
  obtain ⟨rfl, rfl⟩ := Hagr
  icases tcpOut_elim _ c s out f $$ Hout with ⟨%γ', #Hγ', Hm, Hf, Htk⟩
  icases tcpNames_agree _ c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  icases monoListAuthOwn_agree _ _ _ out _ $$ Hm Hmono with %Hmag
  obtain ⟨-, rfl⟩ := Hmag
  icases fin_agree _ _ f _ $$ Hf Hfin with %Hfag
  obtain ⟨rfl, -⟩ := Hfag
  imodintro
  isplitr
  · ipureintro
    by_cases hb : (cn.endSt s).blocked = true
    · refine ⟨Val (PairV (#(W64 0)) (#false)), h, σ, g, rfl, endId c s, bs, c, s, rfl,
        ⟨Hγa.2, rfl⟩, ⟨cn, hcn, ?_⟩, rfl⟩
      simp [hb]
    · refine ⟨Val (PairV (#(BitVec.ofNat 64 bs.length)) (#true)), h, σ,
        g.setConn c (cn.setOut s { cn.out s with sent := (cn.out s).sent ++ bs }), rfl,
        endId c s, bs, c, s, rfl, ⟨Hγa.2, rfl⟩, ⟨cn, hcn, ?_⟩, rfl⟩
      simp [hb]
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, e0, bs0, c0, s0, Hv0, ⟨Hb0, He0⟩, Hrs, rfl⟩ := Hst
  obtain ⟨He1, He2⟩ := val.PairV.inj Hv0
  obtain rfl := go.intoVal_inj (V := w64) He1
  obtain rfl := go.intoVal_inj (V := GoString) He2
  obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2 Hb0 He0
  obtain ⟨cn', hcn', Hcase⟩ := Hrs
  rw [hcn] at hcn'
  cases hcn'
  by_cases hb : (cn.endSt s).blocked = true
  · -- blocked: nothing written
    simp only [hb, ↓reduceIte] at Hcase
    obtain ⟨rfl, Hgg⟩ := Hcase
    imod Hk $$ %0 %false %(cn.endSt s) %(.inl ⟨hb, rfl, rfl, rfl⟩) [Hv] [Hm Hf Htk] with HΦ
    · iapply tcpEnd_intro $$ Hγ Hv
    · rw [List.take_zero, List.append_nil]
      iapply tcpOut_intro $$ Hγ Hm Hf Htk
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · rw [Hgg]
      iapply (tcp_global_ctx_eq _).mpr
      iapply tcpCtx_of_eq _ (setConn_self hcn)
      iapply Hgclose $$ %cn %(And.intro rfl rfl)
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_eq γ s cn]
      iframe Heo Hgv Hmono Hfin
      ipureintro; exact ⟨Haddr, Hpure⟩
    iapply wp_value'
    rw [W64_zero]
    iexact HΦ
  · -- not blocked: the end has sent no FIN
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at Hcase
    have hnf : (cn.out s).fin = false := by
      cases hf : (cn.out s).fin
      · rfl
      · rcases Hpure.2 hf with h1 | h1 <;> simp [TcpEnd.blocked, h1] at hb
    have hb' : (cn.endSt s).blocked = false := by simpa using hb
    obtain ⟨k, ok, st', hwr, rfl, rfl⟩ : ∃ k ok st', WriteRes (cn.endSt s) bs k ok st' ∧
        e' = Val (PairV (#(BitVec.ofNat 64 k)) (#ok)) ∧
        g' = g.setConn c
          ((cn.setOut s { cn.out s with sent := (cn.out s).sent ++ bs.take k }).setEnd s st') := by
      rcases Hcase with ⟨rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩
      · refine ⟨bs.length, true, cn.endSt s, .inr ⟨hb', .inl ⟨rfl, rfl, rfl⟩⟩, rfl, ?_⟩
        rw [List.take_length, setEnd_endSt_setOut]
      · exact ⟨k, false, (cn.endSt s).onFail, .inr ⟨hb', .inr ⟨hk, rfl, rfl⟩⟩, rfl, rfl⟩
    imod mono_halves_app _ _ _ (bs.take k) $$ Hm Hmono with ⟨-, Hm, Hmono⟩
    imod ghostVar_update_halves (st', (cn.out (!s)).rcvd) $$ Hv Hgv with ⟨Hv, Hgv⟩
    ihave Hf := ite_false_ent (R := dghostVar (γ.fin s) .discard
      (some ((cn.out s).sent ++ bs.take k))) hnf $$ Hf
    imod Hk $$ %k %ok %st' %hwr [Hv] [Hm Hf Htk] with HΦ
    · iapply tcpEnd_intro $$ Hγ Hv
    · iapply tcpOut_intro $$ Hγ Hm Hf Htk
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · iapply (tcp_global_ctx_eq _).mpr
      iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_setOutEnd_other, endCtx_setOutEnd_self]
      ihave Hfin := (finCtx_nofin _ _ hnf).mp $$ Hfin
      ihave Hfin := (finCtx_nofin _ { cn.out s with sent := (cn.out s).sent ++ bs.take k }
        hnf).mpr $$ Hfin
      rw [endCtx_eq γ (!s) cn]
      icases Heo with ⟨Hgvo, Hmonoo, Hfino, %Hpureo⟩
      dsimp only
      simp only [Bool.not_not] at Hpureo ⊢
      iframe Hgv Hmono Hfin Hgvo Hmonoo Hfino
      ipureintro
      refine ⟨by simpa using Haddr, ⟨?_, fun h => by simp [hnf] at h⟩, Hpureo⟩
      simp only [List.length_append]; omega
    iapply wp_value'
    iexact HΦ

/-- The outcomes of a close (`upd` sets the end's flag, `closed` or `wshut`) by an end in state
`st` with FIN flag `f`: a failure that changes nothing (`canFail`: for a shutdown, always
possible; for a close, only of a closed end), or the flag set, and the FIN sent unless the end is
broken. -/
def CloseRes (canFail : Bool) (upd : TcpEnd → TcpEnd) (st : TcpEnd) (f : Bool) (ok : Bool)
    (st' : TcpEnd) (f' : Bool) : Prop :=
  ((canFail = true ∨ st.closed = true) ∧ ok = false ∧ st' = st ∧ f' = f) ∨
  (st.closed = false ∧ st' = upd st ∧ f' = (f || !st.broken))

/-- The close-like steps' common part: the end's flag set (`upd`) and its FIN sent unless broken,
with the result `ok`, or nothing changed and the result `false`. -/
theorem wp_tcp_closeLike (o : String) (canFail : Bool) (upd : TcpEnd → TcpEnd)
    (hupd : ∀ st : TcpEnd, (upd st).closed = true ∨ (upd st).wshut = true)
    (hupdb : ∀ st : TcpEnd, (upd st).broken = st.broken)
    (Hstep : ∀ (v : val) (h : GMap Loc (NonAtomic val)) (σ : TcpLocal) (g : TcpGlobal) (e' : Expr)
        (h' : GMap Loc (NonAtomic val)) (σ' : TcpLocal) (g' : TcpGlobal) (c : Nat) (s : Bool)
        (cn : TcpConn), v = #(endId c s) → 2 * c + 1 < 2 ^ 64 → g.conns !! c = some cn →
      ExtSemantics.step (E := tcpExt) o v h σ g e' h' σ' g' →
        h' = h ∧ σ' = σ ∧
        (((canFail = true ∨ (cn.endSt s).closed = true) ∧ e' = Val (#false) ∧ g' = g) ∨
         ((cn.endSt s).closed = false ∧ ∃ ok : Bool, e' = Val (#ok) ∧
          g' = g.setConn c ((cn.setOut s ((cn.out s).finIf (cn.endSt s))).setEnd s
            (upd (cn.endSt s))))))
    (Hex : ∀ (v : val) (h : GMap Loc (NonAtomic val)) (σ : TcpLocal) (g : TcpGlobal) (c : Nat)
        (s : Bool) (cn : TcpConn), v = #(endId c s) → 2 * c + 1 < 2 ^ 64 →
        g.conns !! c = some cn →
      ∃ e' g', ExtSemantics.step (E := tcpExt) o v h σ g e' h σ g')
    (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st r out f, tcpEnd tcpG c s st r ∗ tcpOut tcpG c s out f ∗
      ∀ ok st' f', ⌜CloseRes canFail upd st f ok st' f'⌝ -∗ tcpEnd tcpG c s st' r -∗
        tcpOut tcpG c s out f' ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name o (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat HAU
  unfold tcpConnAt
  icases Hat with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_extStep o (#(endId c s)) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  imod HAU with ⟨%st, %r, %out, %f, Hend, Hout, Hk⟩
  icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn, %hcn, Hcc, Hgclose⟩
  icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
  rw [endCtx_eq γ s cn]
  icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
  icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
  obtain ⟨rfl, rfl⟩ := Hagr
  icases tcpOut_elim _ c s out f $$ Hout with ⟨%γ', #Hγ', Hm, Hf, Htk⟩
  icases tcpNames_agree _ c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  icases monoListAuthOwn_agree _ _ _ out _ $$ Hm Hmono with %Hmag
  obtain ⟨-, rfl⟩ := Hmag
  icases fin_agree _ _ f _ $$ Hf Hfin with %Hfag
  obtain ⟨rfl, -⟩ := Hfag
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', g', hst⟩ := Hex _ h σ g c s cn rfl Hγa.2 hcn
    exact ⟨e', h, σ, g', hst⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, rfl, Hcase⟩ := Hstep _ h σ g e' h' σ' g' c s cn rfl Hγa.2 hcn Hst
  rcases Hcase with ⟨hcf, rfl, Hgg⟩ | ⟨hc, ok, rfl, rfl⟩
  · -- nothing changed
    imod Hk $$ %false %(cn.endSt s) %((cn.out s).fin) %(.inl ⟨hcf, rfl, rfl, rfl⟩) [Hv] [Hm Hf Htk]
      with HΦ
    · iapply tcpEnd_intro $$ Hγ Hv
    · iapply tcpOut_intro $$ Hγ Hm Hf Htk
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · rw [Hgg]
      iapply (tcp_global_ctx_eq _).mpr
      iapply tcpCtx_of_eq _ (setConn_self hcn)
      iapply Hgclose $$ %cn %(And.intro rfl rfl)
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_eq γ s cn]
      iframe Heo Hgv Hmono Hfin
      ipureintro; exact ⟨Haddr, Hpure⟩
    iapply wp_value'
    iexact HΦ
  · -- the flag set, and the FIN
    imod ghostVar_update_halves (upd (cn.endSt s), (cn.out (!s)).rcvd) $$ Hv Hgv with ⟨Hv, Hgv⟩
    imod fin_close _ (cn.out s) (cn.endSt s) $$ Hf Hfin with ⟨Hf, Hfin⟩
    imod Hk $$ %ok %(upd (cn.endSt s)) %((cn.out s).fin || !(cn.endSt s).broken)
      %(.inr ⟨hc, rfl, rfl⟩) [Hv] [Hm Hf Htk] with HΦ
    · iapply tcpEnd_intro $$ Hγ Hv
    · iapply tcpOut_intro $$ Hγ Hm Hf Htk
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · iapply (tcp_global_ctx_eq _).mpr
      iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_setOutEnd_other, endCtx_setOutEnd_self]
      rw [endCtx_eq γ (!s) cn]
      icases Heo with ⟨Hgvo, Hmonoo, Hfino, %Hpureo⟩
      simp only [finIf_sent, finIf_rcvd, Bool.not_not] at Hpureo ⊢
      iframe Hgv Hmono Hfin Hgvo Hmonoo Hfino
      ipureintro
      exact ⟨by simpa using Haddr, ⟨Hpure.1, fun _ => hupd _⟩, Hpureo⟩
    iapply wp_value'
    iexact HΦ

/-- `Close` of the end `s` of `c`: a failure of a closed end; otherwise the end closed, and its
FIN sent unless it is broken (`CloseRes`; the result may be a failure all the same). -/
theorem wp_tcp_Close (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st r out f, tcpEnd tcpG c s st r ∗ tcpOut tcpG c s out f ∗
      ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
        tcpEnd tcpG c s st' r -∗ tcpOut tcpG c s out f' ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name "Close" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  refine wp_tcp_closeLike "Close" false (fun st => { st with closed := true }) (fun _ => .inl rfl)
    (fun _ => rfl) ?_ ?_ c s a Φ
  · intro v h σ g e' h' σ' g' c s cn hv hb hcn hst
    subst hv
    obtain ⟨rfl, e0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn0, hcn0, hstep⟩, rfl⟩ := hst
    obtain rfl := go.intoVal_inj (V := w64) hv
    obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 he0
    rw [hcn] at hcn0; cases hcn0
    refine ⟨rfl, rfl, ?_⟩
    by_cases hc : (cn.endSt s).closed = true
    · simp only [hc, ↓reduceIte] at hstep
      exact .inl ⟨.inr hc, hstep⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hstep
      exact .inr ⟨by simpa using hc, hstep⟩
  · intro v h σ g c s cn hv hb hcn
    subst hv
    by_cases hc : (cn.endSt s).closed = true
    · refine ⟨Val (#false), g, rfl, endId c s, c, s, rfl, ⟨hb, rfl⟩, ⟨cn, hcn, ?_⟩, rfl⟩
      simp [hc]
    · refine ⟨Val (#true), g.setConn c ((cn.setOut s ((cn.out s).finIf (cn.endSt s))).setEnd s
        { cn.endSt s with closed := true }), rfl, endId c s, c, s, rfl, ⟨hb, rfl⟩,
        ⟨cn, hcn, ?_⟩, rfl⟩
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨true, rfl, trivial⟩

/-- `CloseWrite` of the end `s` of `c`: a failure that changes nothing; or, unless the end is
closed, its write side shut and its FIN sent unless it is broken (`CloseRes`). -/
theorem wp_tcp_CloseWrite (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st r out f, tcpEnd tcpG c s st r ∗ tcpOut tcpG c s out f ∗
      ∀ ok st' f', ⌜CloseRes true (fun st => { st with wshut := true }) st f ok st' f'⌝ -∗
        tcpEnd tcpG c s st' r -∗ tcpOut tcpG c s out f' ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name "CloseWrite" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  refine wp_tcp_closeLike "CloseWrite" true (fun st => { st with wshut := true })
    (fun _ => .inr rfl) (fun _ => rfl) ?_ ?_ c s a Φ
  · intro v h σ g e' h' σ' g' c s cn hv hb hcn hst
    subst hv
    obtain ⟨rfl, e0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn0, hcn0, hstep⟩, rfl⟩ := hst
    obtain rfl := go.intoVal_inj (V := w64) hv
    obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 he0
    rw [hcn] at hcn0; cases hcn0
    refine ⟨rfl, rfl, ?_⟩
    rcases hstep with ⟨he, hg⟩ | ⟨hc, he, hg⟩
    · exact .inl ⟨.inl rfl, he, hg⟩
    · exact .inr ⟨hc, true, he, hg⟩
  · intro v h σ g c s cn hv hb hcn
    subst hv
    exact ⟨Val (#false), g, rfl, endId c s, c, s, rfl, ⟨hb, rfl⟩, ⟨cn, hcn, .inl ⟨rfl, rfl⟩⟩, rfl⟩

/-- `SetDeadline` of the end `s` of `c`: a failure of a closed end; otherwise a deadline recorded. -/
theorem wp_tcp_SetDeadline (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st r, tcpEnd tcpG c s st r ∗
      ∀ ok st', ⌜(st.closed = true ∧ ok = false ∧ st' = st) ∨
          (st.closed = false ∧ ok = true ∧ st' = { st with dl := true })⌝ -∗
        tcpEnd tcpG c s st' r ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name "SetDeadline" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat HAU
  unfold tcpConnAt
  icases Hat with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_extStep "SetDeadline" (#(endId c s)) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  imod HAU with ⟨%st, %r, Hend, Hk⟩
  icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn, %hcn, Hcc, Hgclose⟩
  icases (connCtx_ends γ cn s).mp $$ Hcc with ⟨%Haddr, Hes, Heo⟩
  rw [endCtx_eq γ s cn]
  icases Hes with ⟨Hgv, Hmono, Hfin, %Hpure⟩
  icases tcpEnd_agree _ c s st r γ cn $$ Hγ Hend Hgv with ⟨%Hagr, Hv, Hgv⟩
  obtain ⟨rfl, rfl⟩ := Hagr
  imodintro
  isplitr
  · ipureintro
    by_cases hc : (cn.endSt s).closed = true
    · refine ⟨Val (#false), h, σ, g, rfl, endId c s, c, s, rfl, ⟨Hγa.2, rfl⟩, ⟨cn, hcn, ?_⟩, rfl⟩
      simp [hc]
    · refine ⟨Val (#true), h, σ, g.setConn c (cn.setEnd s { cn.endSt s with dl := true }), rfl,
        endId c s, c, s, rfl, ⟨Hγa.2, rfl⟩, ⟨cn, hcn, ?_⟩, rfl⟩
      simp [hc]
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, e0, c0, s0, Hv0, ⟨Hb0, He0⟩, ⟨cn0, hcn0, Hcase⟩, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj (V := w64) Hv0
  obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2 Hb0 He0
  rw [hcn] at hcn0; cases hcn0
  by_cases hc : (cn.endSt s).closed = true
  · simp only [hc, ↓reduceIte] at Hcase
    obtain ⟨rfl, Hgg⟩ := Hcase
    imod Hk $$ %false %(cn.endSt s) %(.inl ⟨hc, rfl, rfl⟩) [Hv] with HΦ
    · iapply tcpEnd_intro $$ Hγ Hv
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · rw [Hgg]
      iapply (tcp_global_ctx_eq _).mpr
      iapply tcpCtx_of_eq _ (setConn_self hcn)
      iapply Hgclose $$ %cn %(And.intro rfl rfl)
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_eq γ s cn]
      iframe Heo Hgv Hmono Hfin
      ipureintro; exact ⟨Haddr, Hpure⟩
    iapply wp_value'
    iexact HΦ
  · rw [if_neg hc] at Hcase
    obtain ⟨rfl, rfl⟩ := Hcase
    imod ghostVar_update_halves ({ cn.endSt s with dl := true }, (cn.out (!s)).rcvd) $$ Hv Hgv
      with ⟨Hv, Hgv⟩
    imod Hk $$ %true %({ cn.endSt s with dl := true }) %(.inr ⟨by simpa using hc, rfl, rfl⟩) [Hv]
      with HΦ
    · iapply tcpEnd_intro $$ Hγ Hv
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · iapply (tcp_global_ctx_eq _).mpr
      iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
      iapply (connCtx_ends γ _ s).mpr
      rw [endCtx_setEnd_other, endCtx_setEnd_self]
      dsimp only
      iframe Heo Hgv Hmono Hfin
      ipureintro
      exact ⟨by simpa using Haddr, Hpure.1, fun hf => by simpa using Hpure.2 hf⟩
    iapply wp_value'
    iexact HΦ

/-- `AnyBool`: an arbitrary boolean. -/
theorem wp_tcp_AnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ (#b)) -∗ WP (ExternalOp tcpExt.name "AnyBool" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_extStep "AnyBool" (#()) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, σ, g, rfl, rfl, ⟨true, rfl⟩, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, -, ⟨b, rfl⟩, rfl, rfl⟩ := Hst
  imod Hclose
  imodintro
  iframe Hheap Hl Hg
  iapply wp_value'
  iapply HΦ

/-- `AnyString`: an arbitrary string. -/
theorem wp_tcp_AnyString (Φ : val → IProp GF) :
    (∀ str : GoString, Φ (#str)) -∗
      WP (ExternalOp tcpExt.name "AnyString" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_extStep "AnyString" (#()) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, σ, g, rfl, rfl, ⟨[], rfl⟩, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, -, ⟨str, rfl⟩, rfl, rfl⟩ := Hst
  imod Hclose
  imodintro
  iframe Hheap Hl Hg
  iapply wp_value'
  iapply HΦ

/-- The plan has `a` at `h` (the context is kept). -/
theorem tcpCtx_plan (hG : TcpGS GF) (g : TcpGlobal) (a h : GoString) :
    tcpCtx hG g -∗ tcpPlan hG a h -∗ ⌜g.plan !! a = some h⌝ := by
  letI := hG.allG
  unfold tcpCtx tcpPlan
  iintro ⟨%nm, %pm, Hn, Hp, Hl, %Hpure, Hconns⟩ #Ha
  iapply ghost_map_lookup $$ Hl Ha

/-- `Listen` at `a`, an address of this node's host in the plan: a failure, or a new open
listener. -/
theorem wp_tcp_Listen (a : GoString) (Φ : val → IProp GF) :
    tcpPlan tcpG a (tcpL (L := L)).host -∗
    (Φ (PairV (#(W64 0)) (#false)) ∧ ∀ l : w64, tcpLis (tcpL (L := L)) l a true -∗
      Φ (PairV (#l) (#true))) -∗
    WP (ExternalOp tcpExt.name "Listen" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (tcpL (L := L)).allG
  iintro #Hp HΦ
  iapply wp_extStep "Listen" (#a) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  icases tcpCtx_plan _ g a _ $$ Hg Hp with %Hpa
  unfold tcpLocalCtx
  icases Hl with ⟨%Hhost, Hlis⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ, g, rfl, a, rfl, ⟨by rw [Hpa, Hhost], .inl ⟨rfl, rfl⟩⟩, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, a0, Hv, ⟨-, Hcase⟩, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj (V := GoString) Hv
  imod Hclose
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨-, l, hl, rfl, rfl⟩
  · icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hheap
    isplitl [Hlis]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx; iframe Hlis; ipureintro; exact Hhost
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iexact HΦ
  · imod ghost_map_insert l (a, true) hl $$ Hlis with ⟨Hlis, Hel⟩
    icases HΦ with ⟨-, HΦ⟩
    imodintro
    iframe Hheap
    isplitl [Hlis]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx; iframe Hlis; ipureintro; exact Hhost
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iapply HΦ
    unfold tcpLis
    iexact Hel

/-- `LisClose` of the listener `l`: closed; the result is whether it was open. -/
theorem wp_tcp_LisClose (l : w64) (a : GoString) (o : Bool) (Φ : val → IProp GF) :
    tcpLis (tcpL (L := L)) l a o -∗ (tcpLis (tcpL (L := L)) l a false -∗ Φ (#o)) -∗
    WP (ExternalOp tcpExt.name "LisClose" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (tcpL (L := L)).allG
  iintro Hel HΦ
  iapply wp_extStep "LisClose" (#l) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  unfold tcpLocalCtx tcpLis
  icases Hl with ⟨%Hhost, Hlis⟩
  icases ghost_map_lookup $$ Hlis Hel with %Hll
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases o
    · exact ⟨Val (#false), h, σ, g, rfl, l, a, false, rfl, Hll, rfl, by simp⟩
    · exact ⟨Val (#true), h, { σ with lis := σ.lis.insert l (a, false) }, g, rfl, l, a, true, rfl,
        Hll, rfl, by simp⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, l0, a0, o0, Hv, Hl0, rfl, Hcase⟩ := Hst
  obtain rfl := go.intoVal_inj (V := w64) Hv
  rw [Hll] at Hl0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Hl0)
  imod Hclose
  cases o
  · simp only [Bool.false_eq_true, ↓reduceIte] at Hcase
    obtain ⟨rfl, rfl⟩ := Hcase
    imodintro
    iframe Hheap Hg
    isplitl [Hlis]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx; iframe Hlis; ipureintro; exact Hhost
    iapply wp_value'
    iapply HΦ $$ Hel
  · simp only [↓reduceIte] at Hcase
    obtain ⟨rfl, rfl⟩ := Hcase
    imod ghost_map_update (a, false) $$ Hlis Hel with ⟨Hlis, Hel⟩
    imodintro
    iframe Hheap Hg
    isplitl [Hlis]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx; iframe Hlis; ipureintro; exact Hhost
    iapply wp_value'
    iapply HΦ $$ Hel


/-- The resources of a new connection's end `s`: fresh, nothing read or written. -/
def tcpFreshEnd (hG : TcpGS GF) (c : Nat) (s : Bool) : IProp GF :=
  iprop(tcpEnd hG c s TcpEnd.fresh 0 ∗ tcpOut hG c s [] false)

theorem tcpFresh_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (γ : ConnNames) (gv go gf gt : GName)
    (hv : γ.v s = gv) (ho : γ.out s = go) (hf : γ.fin s = gf) (ht : γ.tk s = gt) :
    tcpNames hG c γ -∗ @ghostVar GF hG.allG _ _ gv (1 : Qp).half (TcpEnd.fresh, 0) -∗
      @monoListAuthOwn GF hG.allG _ _ go (1 : Qp).half ([] : GoString) -∗
      @dghostVar GF hG.allG _ _ gf (.own (1 : Qp).half) (none : Option GoString) -∗
      @token GF hG.allG gt -∗
      tcpFreshEnd hG c s := by
  letI := hG.allG
  subst hv ho hf ht
  unfold tcpFreshEnd tcpEnd tcpOut
  iintro #Hγ Hv Ho Hf Ht
  isplitl [Hv]
  · iexists γ; iframe Hγ Hv
  · iexists γ; iframe Hγ Ho Ht; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hf

theorem connCtx_fresh_intro (hG : TcpGS GF) (a : GoString) (γ : ConnNames)
    (gv0 gv1 go0 go1 gf0 gf1 : GName) (ha : γ.addr = a) (hv0 : γ.v false = gv0)
    (hv1 : γ.v true = gv1) (ho0 : γ.out false = go0) (ho1 : γ.out true = go1)
    (hf0 : γ.fin false = gf0) (hf1 : γ.fin true = gf1) :
    @ghostVar GF hG.allG _ _ gv0 (1 : Qp).half (TcpEnd.fresh, 0) -∗
      @monoListAuthOwn GF hG.allG _ _ go0 (1 : Qp).half ([] : GoString) -∗
      @dghostVar GF hG.allG _ _ gf0 (.own (1 : Qp).half) (none : Option GoString) -∗
      @ghostVar GF hG.allG _ _ gv1 (1 : Qp).half (TcpEnd.fresh, 0) -∗
      @monoListAuthOwn GF hG.allG _ _ go1 (1 : Qp).half ([] : GoString) -∗
      @dghostVar GF hG.allG _ _ gf1 (.own (1 : Qp).half) (none : Option GoString) -∗
      @connCtx GF hG.allG γ (TcpConn.fresh a) := by
  letI := hG.allG
  subst hv0 hv1 ho0 ho1 hf0 hf1
  unfold connCtx
  rw [endCtx_fresh, endCtx_fresh]
  iintro Hv0 Ho0 Hf0 Hv1 Ho1 Hf1
  iframe Hv0 Ho0 Hf0 Hv1 Ho1 Hf1
  ipureintro; simp [TcpConn.fresh, ha]

/-- `Dial` of `a`, an address of the plan: a failure, or a new connection `c` to `a`, pending at
`a` (`tcpPend`, by a logically atomic update), with both ends' resources. -/
theorem wp_tcp_Dial (a h : GoString) (Φ : val → IProp GF) :
    tcpPlan tcpG a h -∗
    (Φ (PairV (#(W64 0)) (#false)) ∧
      |={E,∅}=> ∃ S, tcpPend tcpG a S ∗
        ∀ c, ⌜c ∉ S⌝ -∗ tcpPend tcpG a (S ∪ {[c]}) -∗ tcpConnAt tcpG c a -∗
          tcpFreshEnd tcpG c false -∗ tcpFreshEnd tcpG c true ={∅,E}=∗
          Φ (PairV (#(endId c false)) (#true))) -∗
    WP (ExternalOp tcpExt.name "Dial" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hp HΦ
  iapply wp_extStep "Dial" (#a) Φ (by simp)
  iintro %hh %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  icases tcpCtx_plan _ g a _ $$ Hg Hp with %Hpa
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, hh, σ, g, rfl, a, rfl, ⟨by simp [Hpa], .inl ⟨rfl, rfl⟩⟩, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, a0, Hv, ⟨-, Hcase⟩, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj (V := GoString) Hv
  imod Hclose
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨c, hc, hb, rfl, rfl⟩
  · -- a failure
    icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hheap Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iexact HΦ
  · -- a new connection `c`
    icases HΦ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    unfold tcpCtx
    icases Hg with ⟨%nm, %pm, Hn, Hpm, Hpl, %Hpure, Hconns⟩
    obtain ⟨Hdom, Hpok⟩ := Hpure
    unfold tcpPend
    icases ghost_map_lookup $$ Hpm Hpend with %HS
    have hcS : c ∉ S := by
      rw [Hpok.2.1 a S c HS]; rintro ⟨cn, hcn, -⟩; simp [hc] at hcn
    have hnm : nm.lookup c = none := by
      have := Hdom c; rw [hc] at this
      cases hx : nm !! c with
      | none => rfl
      | some _ => rw [hx] at this; simp at this
    imod ghostVar_alloc_halves (TcpEnd.fresh, 0) with ⟨%γv0, Hv0, Hv0'⟩
    imod ghostVar_alloc_halves (TcpEnd.fresh, 0) with ⟨%γv1, Hv1, Hv1'⟩
    imod mono_alloc_halves ([] : GoString) with ⟨%γo0, Ho0, Ho0'⟩
    imod mono_alloc_halves ([] : GoString) with ⟨%γo1, Ho1, Ho1'⟩
    imod dghostVar_alloc_halves (none : Option GoString) with ⟨%γf0, Hf0, Hf0'⟩
    imod dghostVar_alloc_halves (none : Option GoString) with ⟨%γf1, Hf1, Hf1'⟩
    imod token_alloc (GF := GF) with ⟨%γt0, Ht0⟩
    imod token_alloc (GF := GF) with ⟨%γt1, Ht1⟩
    let γ : ConnNames := ⟨a, γv0, γv1, γo0, γo1, γf0, γf1, γt0, γt1⟩
    imod ghost_map_insert_persist c γ hnm $$ Hn with ⟨Hn, #Hγ⟩
    imod ghost_map_update (S ∪ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
    have Hat : 2 * c + 1 < 2 ^ 64 := hb
    imod Hk $$ %c %hcS [Hpend] [] [Hv0 Ho0 Hf0 Ht0] [Hv1 Ho1 Hf1 Ht1] with HΦ
    · iexact Hpend
    · unfold tcpConnAt tcpNames; iexists γ; iframe Hγ; ipureintro; exact ⟨rfl, Hat⟩
    · iapply tcpFresh_intro _ c false γ γv0 γo0 γf0 γt0 rfl rfl rfl rfl $$ [] Hv0 Ho0 Hf0 Ht0
      unfold tcpNames; iexact Hγ
    · iapply tcpFresh_intro _ c true γ γv1 γo1 γf1 γt1 rfl rfl rfl rfl $$ [] Hv1 Ho1 Hf1 Ht1
      unfold tcpNames; iexact Hγ
    imodintro
    iframe Hheap Hl
    isplitr [HΦ]
    · iapply (tcp_global_ctx_eq _).mpr
      unfold tcpCtx
      iexists nm.insert c γ, pm.insert a (S ∪ {[c]})
      rw [setConn_plan, setConn_conns]
      iframe Hn Hpm Hpl
      isplitr
      · ipureintro
        refine ⟨fun k => ?_, pendOk_dial Hpok hc hb Hpa HS⟩
        simp only [GMap.lookup_insert_eq_iff]
        by_cases hk : c = k
        · subst hk; simp
        · simp [hk, Hdom k]
      iapply (BigSepM.bigSepM_insert hc).mpr
      isplitr [Hconns]
      · iexists γ
        iframe Hγ
        isplitr
        · ipureintro; simp [GMap.lookup_insert_eq_iff]
        iapply connCtx_fresh_intro _ a γ γv0 γv1 γo0 γo1 γf0 γf1 rfl rfl rfl rfl rfl rfl rfl
          $$ Hv0' Ho0' Hf0' Hv1' Ho1' Hf1'
      iapply BigSepM.bigSepM_impl $$ Hconns
      iintro !> %k %cn %Hk ⟨%γ', %Hγ', #Hn', Hcc⟩
      iexists γ'
      iframe Hn' Hcc
      ipureintro
      have hkc : c ≠ k := by rintro rfl; rw [gmap_get?_eq] at Hk; rw [hc] at Hk; cases Hk
      simp [GMap.lookup_insert_eq_iff, hkc, Hγ']
    iapply wp_value'
    iexact HΦ


theorem connCtx_accepted [AllG GF] (γ : ConnNames) (cn : TcpConn) (b : Bool) :
    connCtx (GF := GF) γ { cn with accepted := b } = connCtx γ cn := rfl

theorem connCtx_addr [AllG GF] (γ : ConnNames) (cn : TcpConn) :
    connCtx (GF := GF) γ cn -∗ ⌜γ.addr = cn.addr⌝ := by
  unfold connCtx
  iintro ⟨%H, -, -⟩
  ipureintro; exact H

theorem tcpLocal_lookup (hL : TcpLocalGS GF) (σ : TcpLocal) (l : w64) (a : GoString) (o : Bool) :
    tcpLocalCtx hL σ -∗ tcpLis hL l a o -∗ ⌜σ.lis !! l = some (a, o)⌝ := by
  letI := hL.allG
  unfold tcpLocalCtx tcpLis
  iintro ⟨%Hhost, Hlis⟩ Hel
  iapply ghost_map_lookup $$ Hlis Hel

/-- `Accept` of the listener `l` at `a`: a failure; or a connection `c` pending at `a`, now
accepted (taken out of `tcpPend`, by a logically atomic update). The update is used only when the
accept returns a connection. -/
theorem wp_tcp_Accept (l : w64) (a : GoString) (o : Bool) (Φ : val → IProp GF) :
    tcpLis (tcpL (L := L)) l a o -∗
    ((tcpLis (tcpL (L := L)) l a o -∗ Φ (PairV (#(W64 0)) (#false))) ∧
      (|={E,∅}=> ∃ S, tcpPend tcpG a S ∗ ∀ c, ⌜c ∈ S⌝ -∗ tcpPend tcpG a (S \ {[c]}) ={∅,E}=∗
        (tcpLis (tcpL (L := L)) l a o -∗ tcpConnAt tcpG c a -∗
          Φ (PairV (#(endId c true)) (#true))))) -∗
    WP (ExternalOp tcpExt.name "Accept" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iloeb as IH
  iintro Hel HΦ
  iapply wp_extStep "Accept" (#l) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  icases tcpLocal_lookup _ σ l a o $$ Hl Hel with %Hll
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ, g, rfl, l, a, o, rfl, Hll, .inl ⟨rfl, rfl⟩, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, l0, a0, o0, Hv, Hl0, Hcase, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj (V := w64) Hv
  rw [Hll] at Hl0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Hl0)
  imod Hclose
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, c, cn, hcn, haddr, hacc, hb, rfl, rfl⟩
  · -- it waits
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply IH $$ Hel HΦ
  · -- a failure
    icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iapply HΦ $$ Hel
  · -- the connection `c`
    icases HΦ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    icases (tcp_global_ctx_eq _).mp $$ Hg with Hg
    unfold tcpCtx
    icases Hg with ⟨%nm, %pm, Hn, Hpm, Hpl, %Hpure, Hconns⟩
    obtain ⟨Hdom, Hpok⟩ := Hpure
    unfold tcpPend
    icases ghost_map_lookup $$ Hpm Hpend with %HS
    have hcS : c ∈ S := (Hpok.2.1 a S c HS).2 ⟨cn, hcn, haddr, hacc⟩
    imod ghost_map_update (S \ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
    icases BigSepM.bigSepM_insert_acc hcn $$ Hconns with ⟨⟨%γ, %Hγ, #Hn', Hcc⟩, Hcl⟩
    icases connCtx_addr γ cn $$ Hcc with %Haddr
    imod Hk $$ %c %hcS [Hpend] with HΦ
    · iexact Hpend
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitr [HΦ Hel]
    · iapply (tcp_global_ctx_eq _).mpr
      unfold tcpCtx
      iexists nm, pm.insert a (S \ {[c]})
      rw [setConn_plan, setConn_conns]
      iframe Hn Hpm Hpl
      isplitr
      · ipureintro
        refine ⟨fun k => ?_, ?_⟩
        · rw [Hdom k]; simp only [GMap.lookup_insert_eq_iff]
          by_cases hk : c = k
          · subst hk; simp [hcn]
          · simp [hk]
        · have := pendOk_accept (S := S) Hpok hcn (by rw [haddr]; exact HS)
          rw [← haddr]; exact this
      iapply Hcl
      iexists γ
      iframe Hn'
      isplitr
      · ipureintro; exact Hγ
      rw [connCtx_accepted γ cn true]
      iexact Hcc
    iapply wp_value'
    iapply HΦ $$ Hel
    unfold tcpConnAt
    iexists γ
    unfold tcpNames
    iframe Hn'
    ipureintro
    exact ⟨Haddr.trans haddr, hb⟩

end lifting

end Tcp
end Perennial
