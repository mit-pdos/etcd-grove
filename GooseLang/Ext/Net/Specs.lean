/-
The WP specs of the net extension's operations (`Impl.lean`), over its ghost state (`Ghost.lean`).

Each spec's outcome is the operation's outcome relation in `Impl.lean`, verbatim (`ReadOutcome`,
`WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`): what a program may see is
exactly what the semantics allows, over the resources that are the semantics' state (`netEnd`,
`netDir`). The specs of the operations on a connection end are logically atomic: the end's state
and the direction it reads or writes are taken by an atomic update, so that a program may keep them
in an invariant shared by the threads that use the end (a reader and a writer, as grpc's and
net/http's connections have) or by both ends' nodes (a direction is written by one end and read by
the other). So are `Dial`'s and `Accept`'s, over the address's pending set (`netPend`), which a
program keeps in an invariant with its per-address protocol. Every operation may stutter (D22: a
wait), which one rule handles for all, by Löb induction (`wp_net_op`, as Perennial's Grove specs
do), so an update is opened only at the step that decides; the panics of invalid uses are excluded
there by the resources (the connection or listener exists) and premises (the address is valid,
`addrOk`). Each takes
`netConnAt c a` (persistent, from `Dial` or `Accept`): the connection exists, and its ends' ids are
in range and not `0`. Results are the values the step returns: a failure's kind as its code (`errCode`,
`NetErr.code`, `failV`); a `Dial` that fails may leave its connection, abandoned (D16), whose
resources (the acceptor's end fresh, the dialer's closed with its direction shut) the caller's
update gets as a successful dial's.
-/
module

public import GooseLang.Ext.Net.Ghost
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The record algebra -/

section algebra

@[simp] theorem endSt_setEnd (cn : NetConn) (s t : Bool) (st : NetEnd) :
    (cn.setEnd s st).endSt t = if s = t then st else cn.endSt t := by
  cases s <;> cases t <;> rfl

@[simp] theorem out_setEnd (cn : NetConn) (s t : Bool) (st : NetEnd) :
    (cn.setEnd s st).out t = cn.out t := by
  cases s <;> cases t <;> rfl

@[simp] theorem endSt_setOut (cn : NetConn) (s t : Bool) (d : NetDir) :
    (cn.setOut s d).endSt t = cn.endSt t := by
  cases s <;> cases t <;> rfl

@[simp] theorem out_setOut (cn : NetConn) (s t : Bool) (d : NetDir) :
    (cn.setOut s d).out t = if s = t then d else cn.out t := by
  cases s <;> cases t <;> rfl

@[simp] theorem addr_setEnd (cn : NetConn) (s : Bool) (st : NetEnd) :
    (cn.setEnd s st).addr = cn.addr := by cases s <;> rfl
@[simp] theorem addr_setOut (cn : NetConn) (s : Bool) (d : NetDir) :
    (cn.setOut s d).addr = cn.addr := by cases s <;> rfl
@[simp] theorem accepted_setEnd (cn : NetConn) (s : Bool) (st : NetEnd) :
    (cn.setEnd s st).accepted = cn.accepted := by cases s <;> rfl
@[simp] theorem accepted_setOut (cn : NetConn) (s : Bool) (d : NetDir) :
    (cn.setOut s d).accepted = cn.accepted := by cases s <;> rfl

@[simp] theorem lock_setEnd (cn : NetConn) (s t : Bool) (st : NetEnd) :
    (cn.setEnd s st).lock t = cn.lock t := by cases s <;> cases t <;> rfl
@[simp] theorem lock_setOut (cn : NetConn) (s t : Bool) (d : NetDir) :
    (cn.setOut s d).lock t = cn.lock t := by cases s <;> cases t <;> rfl
@[simp] theorem lock_setLock (cn : NetConn) (s t b : Bool) :
    (cn.setLock s b).lock t = if s = t then b else cn.lock t := by cases s <;> cases t <;> rfl
@[simp] theorem endSt_setLock (cn : NetConn) (s t b : Bool) :
    (cn.setLock s b).endSt t = cn.endSt t := by cases s <;> cases t <;> rfl
@[simp] theorem out_setLock (cn : NetConn) (s t b : Bool) :
    (cn.setLock s b).out t = cn.out t := by cases s <;> cases t <;> rfl
@[simp] theorem addr_setLock (cn : NetConn) (s b : Bool) :
    (cn.setLock s b).addr = cn.addr := by cases s <;> rfl
@[simp] theorem accepted_setLock (cn : NetConn) (s b : Bool) :
    (cn.setLock s b).accepted = cn.accepted := by cases s <;> rfl

theorem setEnd_endSt_self (cn : NetConn) (s : Bool) : cn.setEnd s (cn.endSt s) = cn := by
  cases s <;> rfl

theorem setOut_out_self (cn : NetConn) (s : Bool) : cn.setOut s (cn.out s) = cn := by
  cases s <;> rfl

@[simp] theorem setConn_conns (g : NetGlobal) (c : Nat) (cn : NetConn) :
    (g.setConn c cn).conns = g.conns.insert c cn := rfl

theorem setConn_self {g : NetGlobal} {c : Nat} {cn : NetConn} (h : g.conns !! c = some cn) :
    g.setConn c cn = g := by
  cases g with
  | mk conns =>
    simp only [NetGlobal.setConn, NetGlobal.mk.injEq]
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
theorem pendOk_setConn {g : NetGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {cn cn' : NetConn}
    (hp : PendOk g pm) (hc : g.conns !! c = some cn) (ha : cn'.addr = cn.addr)
    (hacc : cn'.accepted = cn.accepted) : PendOk (g.setConn c cn') pm := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1, fun a S k hS => ?_, fun k cn₀ hk => ?_⟩
  · rw [h2 a S k hS]
    simp only [setConn_conns, GMap.lookup_insert_eq_iff]
    by_cases hk : c = k
    · subst hk; simp [hc, ha, hacc]
    · simp [hk]
  · simp only [setConn_conns, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hck : c = k
    · subst hck; simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      rw [ha]; exact h3 c cn hc
    · simp only [hck, ↓reduceIte] at hk; exact h3 k cn₀ hk


/-- A dial keeps `PendOk`, the new connection pending at its address. -/
theorem pendOk_dial {g : NetGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {a : GoString}
    {S : GSet Nat} {cn : NetConn} (hp : PendOk g pm) (hc : g.conns !! c = none)
    (h0 : c ≠ 0) (hb : 2 * c + 1 < 2 ^ 64) (ha : addrOk a = true) (hS : pm !! a = some S)
    (hca : cn.addr = a) (hacc : cn.accepted = false) :
    PendOk (g.setConn c cn) (pm.insert a (S ∪ {[c]})) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun a' => ?_, fun a' S' k hS' => ?_, fun k cn₁ hk => ?_⟩
  · simp only [GMap.lookup_insert_eq_iff]
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
      · subst hkc; simp [hc, hca, hacc]
      · simp [hkc, Ne.symm hkc]
    · simp only [haa, ↓reduceIte] at hS'
      rw [h2 a' S' k hS']
      by_cases hkc : c = k
      · subst hkc; simp [hc, hca, haa]
      · simp [hkc]
  · simp only [setConn_conns, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hkc : c = k
    · subst hkc
      simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      exact ⟨by rw [hca]; exact ha, h0, hb⟩
    · simp only [hkc, ↓reduceIte] at hk; exact h3 k cn₁ hk

/-- An accept keeps `PendOk`, the connection no longer pending. -/
theorem pendOk_accept {g : NetGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {cn : NetConn}
    {S : GSet Nat} (hp : PendOk g pm) (hcn : g.conns !! c = some cn)
    (hS : pm !! cn.addr = some S) :
    PendOk (g.setConn c { cn with accepted := true }) (pm.insert cn.addr (S \ {[c]})) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun a' => ?_, fun a' S' k hS' => ?_, fun k cn' hk => ?_⟩
  · simp only [GMap.lookup_insert_eq_iff]
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
  · simp only [setConn_conns, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hkc : c = k
    · subst hkc
      simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      exact h3 c cn hcn
    · simp only [hkc, ↓reduceIte] at hk; exact h3 k cn' hk

end algebra


/-! ## Outcome laws -/

section outcomes

/-- A step of a `Write` counts at most the bytes it was given. -/
theorem writeOutcome_le {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    {res : Option NetErr} (h : WriteOutcome st d rs k res d') : k ≤ rs.length := by
  unfold WriteOutcome at h
  split at h
  · rw [h.1]; exact Nat.zero_le _
  · split at h
    · rw [h.1]; exact Nat.zero_le _
    · rcases h.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega

/-- A failing step of a `Write` counts nothing. -/
theorem writeOutcome_fail {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    {e : NetErr} (h : WriteOutcome st d rs k (some e) d') : k = 0 := by
  unfold WriteOutcome at h
  split at h
  · exact h.1
  · split at h
    · exact h.1
    · rcases h.2 with ⟨-, -, h⟩ | ⟨h, -⟩
      · cases h
      · exact h
    · rcases h with ⟨-, -, h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
      · cases h
      · exact h
      · exact h

/-- A step of a `Write` that does not fail counts at least one byte of a non-empty remainder (one
that would count none is a wait, a stutter, D22). -/
theorem writeOutcome_none_pos {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    (h : WriteOutcome st d rs k none d') (hrs : rs ≠ []) : 1 ≤ k := by
  unfold WriteOutcome at h
  split at h
  · cases h.2.1
  · split at h
    · rcases h.2.2 with h | ⟨-, h⟩ <;> cases h
    · rcases h.2 with ⟨-, h1 | h1, -⟩ | ⟨-, h | ⟨-, h⟩⟩
      · exact h1
      · exact absurd h1 hrs
      · cases h
      · cases h
    · rcases h with ⟨-, h1 | h1, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩
      · exact h1
      · exact absurd h1 hrs
      · cases h
      · cases h

end outcomes




/-! ## Opening the network -/

section acc
variable {GF : BundledGFunctors}

/-- The connection `c` with names `γ`: its record, its part of the context, and the context back
for any record of the same address and acceptance. -/
theorem netCtx_acc (hG : NetGS GF) (g : NetGlobal) (c : Nat) (γ : ConnNames) :
    netCtx hG g -∗ netNames hG c γ -∗
      ∃ cn, ⌜g.conns !! c = some cn⌝ ∗ @connCtx GF hG.allG γ cn ∗
        ∀ cn', ⌜cn'.addr = cn.addr ∧ cn'.accepted = cn.accepted⌝ -∗
          @connCtx GF hG.allG γ cn' -∗ netCtx hG (g.setConn c cn') := by
  letI := hG.allG
  unfold netCtx netNames
  iintro ⟨%nm, %pm, Hn, Hp, %Hpure, Hconns⟩ #Hγ
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
  iframe Hn Hp
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

theorem netCtx_of_eq (hG : NetGS GF) {g g' : NetGlobal} (h : g' = g) :
    netCtx hG g' ⊢ netCtx hG g := by subst h; exact .rfl


theorem netNames_agree (hG : NetGS GF) (c : Nat) (γ γ' : ConnNames) :
    netNames hG c γ -∗ netNames hG c γ' -∗ ⌜γ = γ'⌝ := by
  letI := hG.allG
  unfold netNames
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- The connection `c` is in the network (the context is kept). -/
theorem netCtx_lookup (hG : NetGS GF) (g : NetGlobal) (c : Nat) (γ : ConnNames) :
    netCtx hG g -∗ netNames hG c γ -∗ ⌜∃ cn, g.conns !! c = some cn⌝ ∗ netCtx hG g := by
  letI := hG.allG
  unfold netCtx netNames
  iintro ⟨%nm, %pm, Hn, Hp, %Hpure, Hconns⟩ #Hγ
  obtain ⟨Hdom, Hpend⟩ := Hpure
  icases ghost_map_lookup $$ Hn Hγ with %Hnγ
  have hsome : (g.conns !! c).isSome := by rw [← Hdom c]; simp [Hnγ]
  isplitr
  · ipureintro; exact Option.isSome_iff_exists.mp hsome
  iexists nm, pm
  iframe Hn Hp Hconns
  ipureintro; exact ⟨Hdom, Hpend⟩


/-- The connection's part of the context, by the end `s` and the direction `t`: their ghost
variables, and the context back for any new state of them. -/
theorem connCtx_acc [AllG GF] (γ : ConnNames) (cn : NetConn) (s t : Bool) :
    connCtx (GF := GF) γ cn ⊢ ⌜γ.addr = cn.addr⌝ ∗
      ghostVar (γ.v s) (1 : Qp).half (cn.endSt s) ∗ ghostVar (γ.q t) (1 : Qp).half (cn.out t) ∗
      ∀ st' d', ghostVar (γ.v s) (1 : Qp).half st' -∗ ghostVar (γ.q t) (1 : Qp).half d' -∗
        connCtx γ ((cn.setEnd s st').setOut t d') := by
  unfold connCtx
  iintro ⟨%Ha, Hv0, Hv1, Hq0, Hq1, Hl0, Hl1⟩
  cases s <;> cases t
  · iframe Hv0 Hq0
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      lock_setOut, lock_setEnd, ↓reduceIte, Bool.false_eq_true]
    iframe Hv Hq Hv1 Hq1 Hl0 Hl1
    ipureintro; exact Ha
  · iframe Hv0 Hq1
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      lock_setOut, lock_setEnd, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
    iframe Hv Hq Hv1 Hq0 Hl0 Hl1
    ipureintro; exact Ha
  · iframe Hv1 Hq0
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      lock_setOut, lock_setEnd, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
    iframe Hv Hq Hv0 Hq1 Hl0 Hl1
    ipureintro; exact Ha
  · iframe Hv1 Hq1
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      lock_setOut, lock_setEnd, ↓reduceIte, Bool.true_eq_false]
    iframe Hv Hq Hv0 Hq0 Hl0 Hl1
    ipureintro; exact Ha

/-- The connection's part of the context, by the end `s` (its state, the direction from it and its
write lock, D25): their ghost variables and the lock's part, and the context back for any new state
of them. -/
theorem connCtx_accW [AllG GF] (γ : ConnNames) (cn : NetConn) (s : Bool) :
    connCtx (GF := GF) γ cn ⊢ ⌜γ.addr = cn.addr⌝ ∗
      ghostVar (γ.v s) (1 : Qp).half (cn.endSt s) ∗ ghostVar (γ.q s) (1 : Qp).half (cn.out s) ∗
      lockCtx (γ.wl s) (cn.lock s) ∗
      ∀ d' b, ghostVar (γ.v s) (1 : Qp).half (cn.endSt s) -∗ ghostVar (γ.q s) (1 : Qp).half d' -∗
        lockCtx (γ.wl s) b -∗ connCtx γ ((cn.setOut s d').setLock s b) := by
  unfold connCtx
  iintro ⟨%Ha, Hv0, Hv1, Hq0, Hq1, Hl0, Hl1⟩
  cases s
  · iframe Hv0 Hq0 Hl0
    isplitr; · ipureintro; exact Ha
    iintro %d' %b Hv Hq Hl
    simp only [endSt_setOut, endSt_setLock, out_setOut, out_setLock, addr_setOut, addr_setLock,
      lock_setOut, lock_setLock, ↓reduceIte, Bool.false_eq_true]
    iframe Hv Hq Hv1 Hq1 Hl Hl1
    ipureintro; exact Ha
  · iframe Hv1 Hq1 Hl1
    isplitr; · ipureintro; exact Ha
    iintro %d' %b Hv Hq Hl
    simp only [endSt_setOut, endSt_setLock, out_setOut, out_setLock, addr_setOut, addr_setLock,
      lock_setOut, lock_setLock, ↓reduceIte, Bool.true_eq_false]
    iframe Hv Hq Hv0 Hq0 Hl0 Hl
    ipureintro; exact Ha

theorem ghostVar_alloc_halves {A : Type} [Pos.Countable A] [AllG GF] (a : A) :
    ⊢ |==> ∃ γ, ghostVar (GF := GF) γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  imod ghostVar_alloc (GF := GF) a with ⟨%γ, H⟩
  icases (ghostVar_split_half γ 1 a).mp $$ H with ⟨H1, H2⟩
  imodintro
  iexists γ
  iframe H1 H2

end acc

/-! ## The resources' laws -/

section laws
variable {GF : BundledGFunctors}

theorem netEnd_open (hG : NetGS GF) (c : Nat) (s : Bool) (st : NetEnd) (γ : ConnNames) :
    netNames hG c γ -∗ netEnd hG c s st -∗ @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half st := by
  letI := hG.allG
  unfold netEnd
  iintro #Hγ ⟨%γ', #Hγ', Hv⟩
  icases netNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  iexact Hv

theorem netEnd_intro (hG : NetGS GF) (c : Nat) (s : Bool) (st : NetEnd) (γ : ConnNames) :
    netNames hG c γ -∗ @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half st -∗ netEnd hG c s st := by
  letI := hG.allG
  unfold netEnd
  iintro #Hγ Hv
  iexists γ
  iframe Hγ Hv

theorem netDir_open (hG : NetGS GF) (c : Nat) (s : Bool) (d : NetDir) (γ : ConnNames) :
    netNames hG c γ -∗ netDir hG c s d -∗
      @ghostVar GF hG.allG _ _ (γ.q s) (1 : Qp).half d ∗ @token GF hG.allG (γ.tk s) := by
  letI := hG.allG
  unfold netDir
  iintro #Hγ ⟨%γ', #Hγ', Hq, Htk⟩
  icases netNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  iframe Hq Htk

theorem netDir_intro (hG : NetGS GF) (c : Nat) (s : Bool) (d : NetDir) (γ : ConnNames) :
    netNames hG c γ -∗ @ghostVar GF hG.allG _ _ (γ.q s) (1 : Qp).half d -∗
      @token GF hG.allG (γ.tk s) -∗ netDir hG c s d := by
  letI := hG.allG
  unfold netDir
  iintro #Hγ Hq Htk
  iexists γ
  iframe Hγ Hq Htk

/-- A direction's resource is exclusive. -/
theorem netDir_excl (hG : NetGS GF) (c : Nat) (s : Bool) (d d' : NetDir) :
    netDir hG c s d -∗ netDir hG c s d' -∗ False := by
  letI := hG.allG
  unfold netDir
  iintro ⟨%γ, #Hγ, -, Htk⟩ ⟨%γ', #Hγ', -, Htk'⟩
  icases netNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  iapply token_exclusive $$ Htk Htk'


/-- A connection's ends have nonzero ids (no connection is numbered `0`): a zero-value `TCPConn`'s
id `0` is none of them. -/
theorem netConnAt_endId_ne (hG : NetGS GF) (c : Nat) (a : GoString) (s : Bool) :
    netConnAt hG c a ⊢ ⌜endId c s ≠ 0⌝ := by
  letI := hG.allG
  unfold netConnAt
  iintro ⟨%γ, -, %h⟩
  ipureintro
  obtain ⟨-, h0, hb⟩ := h
  intro he
  exact h0 (endId_inj (s' := false) hb (by decide) (by rw [he]; rfl)).1

end laws

/-! ## The specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {sk : Stuckness} {E : CoPset}

/-- The network's ghost state. -/
abbrev netG : NetGS GF := extGlobalGS netExt

/-- This node's ghost state. -/
abbrev netL : NetLocalGS GF := extLocalGS netExt (L := L)

theorem net_local_ctx_eq (σ : NetLocal) :
    ExtInterp.localCtx (E := netExt) (extLocalGS netExt (L := L) (GF := GF)) σ ⊣⊢
      netLocalCtx (netL (L := L)) σ := .rfl

theorem net_global_ctx_eq (g : NetGlobal) :
    ExtInterp.globalCtx (E := netExt) (extGlobalGS netExt (G := G)) g ⊣⊢ netCtx (netG (G := G)) g :=
  .rfl

theorem pair_w64_inj {e e' n n' : w64} (h : PairV (#e) (#n) = PairV (#e') (#n')) :
    e = e' ∧ n = n' := by
  obtain ⟨h1, h2⟩ := val.PairV.inj h
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

/-- D22. The lifting rule of the extension's operations: a WP of an operation from its outcome
rules (`IsNetStep`), each with the node's and the network's interpretations; its stutters
(`NetStep`'s other case) are handled here, by Löb induction, as Perennial's `wp_GroveOp` does. -/
theorem wp_net_op (o : String) (v : val) (hv : v.isPanic = false) (Φ : val → IProp GF) :
    ▷ (∀ σ g e' σ' g', ⌜IsNetStep o v σ g e' σ' g'⌝ -∗ netLocalCtx (netL (L := L)) σ -∗
        netCtx (netG (G := G)) g ={E}=∗
        netLocalCtx (netL (L := L)) σ' ∗ netCtx (netG (G := G)) g' ∗ WP e' @ sk; E {{ Φ }}) ⊢
    WP (ExternalOp netExt.name o (Val v)) @ sk; E {{ Φ }} := by
  iloeb as IH
  iintro HΦ
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  icases (net_local_ctx_eq σ).mp $$ Hl with Hl
  icases (net_global_ctx_eq g).mp $$ Hg with Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ, g, (show NetStep o v h σ g _ h σ g from ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩)⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, Hcase⟩ := (show NetStep o v h σ g e' h' σ' g' from Hst)
  imod Hclose
  rcases Hcase with ⟨rfl, rfl, rfl⟩ | Hop
  · -- a stutter
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (net_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (net_global_ctx_eq _).mpr; iexact Hg
    iapply IH
    inext
    iexact HΦ
  · imod HΦ $$ %_ %_ %_ %_ %_ %Hop Hl Hg with ⟨Hl, Hg, Hwp⟩
    imodintro
    iframe Hheap Hwp
    isplitl [Hl]
    · iapply (net_local_ctx_eq _).mpr; iexact Hl
    · iapply (net_global_ctx_eq _).mpr; iexact Hg

/-- An operation on the end `s` of `c` and the direction from its end `t`, whose outcome rule on
the connection (when it exists) takes an outcome of `Out` (the end's state and the direction
before, the result, the end's state and the direction after) and writes the connection back. The
update is opened only at the outcome (a stutter, a wait, does not open it: `wp_net_op`). -/
theorem wp_net_endOp (o : String) (v : val) (hv : v.isPanic = false) (c : Nat) (s t : Bool)
    (Out : NetEnd → NetDir → val → NetEnd → NetDir → Prop)
    (Hstep : ∀ (σ : NetLocal) (g : NetGlobal) (e' : Expr) (σ' : NetLocal) (g' : NetGlobal)
        (cn0 : NetConn), 2 * c + 1 < 2 ^ 64 → g.conns !! c = some cn0 →
      IsNetStep o v σ g e' σ' g' →
        σ' = σ ∧ ∃ cn st' d' w, g.conns !! c = some cn ∧ Out (cn.endSt s) (cn.out t) w st' d' ∧
          e' = Val w ∧ g' = g.setConn c ((cn.setEnd s st').setOut t d'))
    (a : GoString) (Φ : val → IProp GF) :
    netConnAt netG c a -∗
    (|={E,∅}=> ∃ st d, netEnd netG c s st ∗ netDir netG c t d ∗
      ∀ w st' d', ⌜Out st d w st' d'⌝ -∗ netEnd netG c s st' -∗ netDir netG c t d'
        ={∅,E}=∗ Φ w) -∗
    WP (ExternalOp netExt.name o (Val v)) @ sk; E {{ Φ }} := by
  letI := (netG (G := G)).allG
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold netConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_net_op o v hv Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases netCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
  obtain ⟨cn0, hcn0⟩ := Hcn
  obtain ⟨rfl, cn, st', d', w, hcn, Hout, rfl, rfl⟩ := Hstep σ g e' σ' g' cn0 Hγa.2.2 hcn0 Hst
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  icases netCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn1, %hcn1, Hcc, Hgclose⟩
  rw [hcn] at hcn1
  cases hcn1
  icases connCtx_acc γ cn s t $$ Hcc with ⟨%Haddr, Hv, Hq, Hcclose⟩
  icases netEnd_open _ c s st γ $$ Hγ Hend with Hv'
  icases netDir_open _ c t d γ $$ Hγ Hdir with ⟨Hq', Htk⟩
  icases ghostVar_agree $$ Hv' Hv with %Hst
  icases ghostVar_agree $$ Hq' Hq with %Hd
  subst Hst Hd
  imod ghostVar_update_halves st' $$ Hv' Hv with ⟨Hv', Hv⟩
  imod ghostVar_update_halves d' $$ Hq' Hq with ⟨Hq', Hq⟩
  imod Hk $$ %w %st' %d' %Hout [Hv'] [Hq' Htk] with HΦ
  · iapply netEnd_intro $$ Hγ Hv'
  · iapply netDir_intro $$ Hγ Hq' Htk
  imodintro
  iframe Hl
  isplitr [HΦ]
  · iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
    iapply Hcclose $$ Hv Hq
  iapply wp_value'
  iexact HΦ

/-- The bytes a read returned (none for EOF or an error). -/
def ReadRes.got : ReadRes → List w8
  | .bytes bs => bs
  | _ => []

/-- D1. `Read` of `n` bytes at the end `s` of `c`, from the direction towards it
(`ReadOutcome`). -/
theorem wp_net_Read (c : Nat) (s : Bool) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    netConnAt netG c a -∗
    (|={E,∅}=> ∃ st d, netEnd netG c s st ∗ netDir netG c (!s) d ∗
      ∀ r d', ⌜ReadOutcome st d n.toNat r d'⌝ -∗ netEnd netG c s st -∗
        netDir netG c (!s) d' ={∅,E}=∗ Φ r.toVal) -∗
    WP (ExternalOp netExt.name "Read" (Val (PairV (#(endId c s)) (#n)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_net_endOp "Read" (PairV (#(endId c s)) (#n)) (by simp) c s (!s)
    (fun st d w st' d' => st' = st ∧ ∃ r, ReadOutcome st d n.toNat r d' ∧ w = r.toVal)
    ?_ a Φ $$ Hat
  · intro σ g e' σ' g' cn0 hb hcn0 hst
    rcases hst with ⟨e0, n0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, r, d', hcn, hout, rfl, rfl⟩, rfl⟩ |
      ⟨hnv, -⟩
    · obtain ⟨he, rfl⟩ := pair_w64_inj hv
      obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
      exact ⟨rfl, cn, cn.endSt s, d', r.toVal, hcn, ⟨rfl, r, hout, rfl⟩, rfl,
        by rw [setEnd_endSt_self]⟩
    · exact absurd ⟨endId c s, n, c, s, rfl, ⟨hb, rfl⟩, by simp [hcn0]⟩ hnv
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨rfl, r, Hr, rfl⟩ := Hout
    iapply Hk $$ %r %d' %Hr Hend Hdir

/-- D25. Our write-lock token and the network's part of a free lock: impossible. -/
theorem netWLock_lockCtx_free (hG : NetGS GF) (c : Nat) (s : Bool) (γ : ConnNames) :
    netNames hG c γ -∗ netWLock hG c s -∗ @lockCtx GF hG.allG (γ.wl s) false -∗ False := by
  letI := hG.allG
  unfold netWLock lockCtx
  iintro #Hγ ⟨%γ', #Hγ', Htk⟩ Htk'
  icases netNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  simp only [Bool.false_eq_true, ↓reduceIte]
  iapply token_exclusive $$ Htk Htk'

/-- D2, D25. One step of a `Write`, of the bytes `bs` not yet written, at the end `s` of `c`, into
the direction from it (`WriteOutcome`), `first` whether it is its `Write`'s first step. A first step
takes the end's write lock (it waits, a stutter, while another `Write` holds it); a later one needs
it (`netWLock`). After a step that does not end the loop (`writeLast`) the caller has the lock; the
last gives it back. The caller's update sees only the end's state and the direction, as before
D25. -/
theorem wp_net_Write (c : Nat) (s : Bool) (a : GoString) (bs : List w8) (first : Bool)
    (Φ : val → IProp GF) :
    netConnAt netG c a -∗ (if first then iprop(True) else netWLock netG c s) -∗
    (|={E,∅}=> ∃ st d, netEnd netG c s st ∗ netDir netG c s d ∗
      ∀ k res d', ⌜WriteOutcome st d bs k res d'⌝ -∗ netEnd netG c s st -∗
        netDir netG c s d' ={∅,E}=∗
        ((if writeLast bs k res then iprop(True) else netWLock netG c s) -∗
          Φ (PairV (#(BitVec.ofNat 64 k)) (#(errCode res))))) -∗
    WP (ExternalOp netExt.name "Write" (Val (PairV (#(endId c s)) (PairV (#bs) (#first)))))
      @ sk; E {{ Φ }} := by
  letI := (netG (G := G)).allG
  iintro #Hat Hlk HAU
  ihave #Hat' := Hat
  unfold netConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_net_op "Write" _ (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases netCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn, %hcn, Hcc, Hgclose⟩
  icases connCtx_accW γ cn s $$ Hcc with ⟨%Haddr, Hv, Hq, Hlc, Hcclose⟩
  have hvalid : first = true ∨ cn.lock s = true → (∃ (e0 : w64) (bs0 : List w8) (first0 : Bool)
      (c0 : Nat) (s0 : Bool), PairV (#(endId c s)) (PairV (#bs) (#first)) =
        PairV (#e0) (PairV (#bs0) (#first0)) ∧ EndOf g e0 c0 s0 ∧
        (first0 = true ∨ (g.conns !! c0).any (·.lock s0))) := fun h =>
    ⟨endId c s, bs, first, c, s, rfl, ⟨⟨Hγa.2.2, rfl⟩, by simp [hcn]⟩,
      h.imp_right fun h => by simp [hcn, h]⟩
  rcases Hst with ⟨e0, bs0, first0, c0, s0, hv, ⟨hb0, he0⟩,
      ⟨cn', k, res, d', hcn', hlock, hout, rfl, rfl⟩, rfl⟩ | ⟨hnv, rfl, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := val.PairV.inj hv
    obtain ⟨h2, h3⟩ := val.PairV.inj h2
    have he : endId c s = e0 := go.intoVal_inj h1
    obtain rfl : bs = bs0 := go.intoVal_inj h2
    obtain rfl : first = first0 := go.intoVal_inj h3
    obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2.2 hb0 (he.trans he0)
    rw [hcn] at hcn'
    cases hcn'
    imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    icases netEnd_open _ c s st γ $$ Hγ Hend with Hv'
    icases netDir_open _ c s d γ $$ Hγ Hdir with ⟨Hq', Htk⟩
    icases ghostVar_agree $$ Hv' Hv with %Hst
    icases ghostVar_agree $$ Hq' Hq with %Hd
    subst Hst Hd
    imod ghostVar_update_halves d' $$ Hq' Hq with ⟨Hq', Hq⟩
    imod Hk $$ %k %res %d' %hout [Hv'] [Hq' Htk] with HΦ
    · iapply netEnd_intro $$ Hγ Hv'
    · iapply netDir_intro $$ Hγ Hq' Htk
    -- the lock: the network's part after, and the caller's
    ihave Hlm : iprop(lockCtx (γ.wl s) (!writeLast bs k res) ∗
        (if writeLast bs k res then iprop(True) else netWLock netG c s)) $$ [Hlk Hlc]
    · cases first <;> cases hw : writeLast bs k res <;>
        simp only [Bool.not_true, Bool.not_false] at hlock <;> unfold lockCtx <;>
        simp only [hlock, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      · -- a later step, not the last: the lock stays held, ours
        isplitr [Hlk]
        · itrivial
        · iexact Hlk
      · -- a later step, the last: the token back to the network
        unfold netWLock
        icases Hlk with ⟨%γ', #Hγ', Htk⟩
        icases netNames_agree _ c γ γ' $$ Hγ Hγ' with %Heq
        subst Heq
        isplitl [Htk]
        · iexact Htk
        · itrivial
      · -- a first step, not the last: the token from the network, ours
        isplitr [Hlc]
        · itrivial
        · unfold netWLock
          iexists γ
          iframe Hγ Hlc
      · -- a first step, the last: the lock stays free
        isplitl [Hlc]
        · iexact Hlc
        · itrivial
    icases Hlm with ⟨Hlc, Hmine⟩
    imodintro
    iframe Hl
    isplitr [HΦ Hmine]
    · iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
      iapply Hcclose $$ Hv Hq Hlc
    iapply wp_value'
    iapply HΦ $$ Hmine
  · -- an invalid use: excluded (the end exists; a later step holds the lock)
    by_cases h : first = true ∨ cn.lock s = true
    · exact absurd (hvalid h) hnv
    · have hf : first = false := by cases first <;> simp_all
      have hl : cn.lock s = false := by cases hcl : cn.lock s <;> simp_all
      subst hf
      rw [hl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexfalso
      iapply netWLock_lockCtx_free _ c s γ $$ Hγ Hlk Hlc

/-- D3. `Close` of the end `s` of `c` (`CloseOutcome`). -/
theorem wp_net_Close (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    netConnAt netG c a -∗
    (|={E,∅}=> ∃ st d, netEnd netG c s st ∗ netDir netG c s d ∗
      ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗ netEnd netG c s st' -∗
        netDir netG c s d' ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp netExt.name "Close" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_net_endOp "Close" (#(endId c s)) (by simp) c s s
    (fun st d w st' d' => ∃ res, CloseOutcome st d res st' d' ∧ w = #(errCode res))
    ?_ a Φ $$ Hat
  · intro σ g e' σ' g' cn0 hb hcn0 hst
    rcases hst with ⟨e0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, res, st', d', hcn, hout, rfl, rfl⟩, rfl⟩ |
      ⟨hnv, -⟩
    · have he : endId c s = e0 := go.intoVal_inj hv
      obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
      exact ⟨rfl, cn, st', d', _, hcn, ⟨res, hout, rfl⟩, rfl, rfl⟩
    · exact absurd ⟨endId c s, c, s, rfl, ⟨hb, rfl⟩, by simp [hcn0]⟩ hnv
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨res, Hc, rfl⟩ := Hout
    iapply Hk $$ %res %st' %d' %Hc Hend Hdir

/-- D4. `CloseWrite` of the end `s` of `c` (`CloseWriteOutcome`). -/
theorem wp_net_CloseWrite (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    netConnAt netG c a -∗
    (|={E,∅}=> ∃ st d, netEnd netG c s st ∗ netDir netG c s d ∗
      ∀ res d', ⌜CloseWriteOutcome st d res d'⌝ -∗ netEnd netG c s st -∗
        netDir netG c s d' ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp netExt.name "CloseWrite" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_net_endOp "CloseWrite" (#(endId c s)) (by simp) c s s
    (fun st d w st' d' => st' = st ∧ ∃ res, CloseWriteOutcome st d res d' ∧
      w = #(errCode res))
    ?_ a Φ $$ Hat
  · intro σ g e' σ' g' cn0 hb hcn0 hst
    rcases hst with ⟨e0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, res, d', hcn, hout, rfl, rfl⟩, rfl⟩ |
      ⟨hnv, -⟩
    · have he : endId c s = e0 := go.intoVal_inj hv
      obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
      exact ⟨rfl, cn, cn.endSt s, d', _, hcn, ⟨rfl, res, hout, rfl⟩, rfl,
        by rw [setEnd_endSt_self]⟩
    · exact absurd ⟨endId c s, c, s, rfl, ⟨hb, rfl⟩, by simp [hcn0]⟩ hnv
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨rfl, res, Hc, rfl⟩ := Hout
    iapply Hk $$ %res %d' %Hc Hend Hdir

/-- D5. `SetDeadline` of the deadlines of kind `kind` of the end `s` of `c`, to the time whose
words are `wall` and `ext` (`DeadlineOutcome`; set unless the time is zero). -/
theorem wp_net_SetDeadline (c : Nat) (s : Bool) (a : GoString) (kind wall ext : w64)
    (Φ : val → IProp GF) :
    netConnAt netG c a -∗
    (|={E,∅}=> ∃ st, netEnd netG c s st ∗
      ∀ res st', ⌜DeadlineOutcome st kind (!timeIsZero wall ext) res st'⌝ -∗ netEnd netG c s st'
        ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp netExt.name "SetDeadline"
      (Val (PairV (#(endId c s)) (PairV (#kind) (PairV (#wall) (#ext)))))) @ sk; E {{ Φ }} := by
  letI := (netG (G := G)).allG
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold netConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_net_op "SetDeadline" _ (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases netCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
  obtain ⟨cn0, hcn0⟩ := Hcn
  obtain ⟨e0, kind0, wall0, ext0, c0, s0, hv, ⟨hb0, he0⟩,
    ⟨cn, res, st', hcn, hout, rfl, rfl⟩, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨endId c s, kind, wall, ext, c, s, rfl, ⟨Hγa.2.2, rfl⟩, by simp [hcn0]⟩
  obtain ⟨h1, h2⟩ := val.PairV.inj hv
  obtain ⟨h2, h3⟩ := val.PairV.inj h2
  obtain ⟨h3, h4⟩ := val.PairV.inj h3
  have he : endId c s = e0 := go.intoVal_inj h1
  obtain rfl : kind = kind0 := go.intoVal_inj h2
  obtain rfl : wall = wall0 := go.intoVal_inj h3
  obtain rfl : ext = ext0 := go.intoVal_inj h4
  obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2.2 hb0 (he.trans he0)
  imod HAU with ⟨%st, Hend, Hk⟩
  icases netCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn1, %hcn1, Hcc, Hgclose⟩
  rw [hcn] at hcn1
  cases hcn1
  icases connCtx_acc γ cn s s $$ Hcc with ⟨%Haddr, Hv, Hq, Hcclose⟩
  icases netEnd_open _ c s st γ $$ Hγ Hend with Hv'
  icases ghostVar_agree $$ Hv' Hv with %Hst
  subst Hst
  imod ghostVar_update_halves st' $$ Hv' Hv with ⟨Hv', Hv⟩
  imod Hk $$ %res %st' %hout [Hv'] with HΦ
  · iapply netEnd_intro $$ Hγ Hv'
  imodintro
  iframe Hl
  isplitr [HΦ]
  · have hset : cn.setEnd s st' = (cn.setEnd s st').setOut s (cn.out s) := by
      rw [show cn.out s = (cn.setEnd s st').out s by simp, setOut_out_self]
    rw [hset]
    iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
    iapply Hcclose $$ Hv Hq
  iapply wp_value'
  iexact HΦ

/-- D24. `SetSockopt` of the option `kind` with the value `x` at the end `s` of `c`
(`SockOptOutcome`, `sockOptValid`): nothing changes; the caller's update reads the end's state. -/
theorem wp_net_SetSockopt (c : Nat) (s : Bool) (a : GoString) (kind x : w64)
    (Φ : val → IProp GF) :
    netConnAt netG c a -∗
    (|={E,∅}=> ∃ st, netEnd netG c s st ∗
      ∀ res, ⌜SockOptOutcome st (sockOptValid kind x) res⌝ -∗ netEnd netG c s st
        ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp netExt.name "SetSockopt"
      (Val (PairV (#(endId c s)) (PairV (#kind) (#x))))) @ sk; E {{ Φ }} := by
  letI := (netG (G := G)).allG
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold netConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_net_op "SetSockopt" _ (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases netCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
  obtain ⟨cn0, hcn0⟩ := Hcn
  obtain ⟨e0, kind0, x0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, res, hcn, hout, rfl, hgg⟩, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ =>
      hnv ⟨endId c s, kind, x, c, s, rfl, ⟨Hγa.2.2, rfl⟩, by simp [hcn0]⟩
  obtain ⟨h1, h2⟩ := val.PairV.inj hv
  obtain ⟨h2, h3⟩ := val.PairV.inj h2
  have he : endId c s = e0 := go.intoVal_inj h1
  obtain rfl : kind = kind0 := go.intoVal_inj h2
  obtain rfl : x = x0 := go.intoVal_inj h3
  obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2.2 hb0 (he.trans he0)
  subst g'
  imod HAU with ⟨%st, Hend, Hk⟩
  icases netCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn1, %hcn1, Hcc, Hgclose⟩
  rw [hcn] at hcn1
  cases hcn1
  icases connCtx_acc γ cn s s $$ Hcc with ⟨%Haddr, Hv, Hq, Hcclose⟩
  icases netEnd_open _ c s st γ $$ Hγ Hend with Hv'
  icases ghostVar_agree $$ Hv' Hv with %Hst
  subst Hst
  imod Hk $$ %res %hout [Hv'] with HΦ
  · iapply netEnd_intro $$ Hγ Hv'
  imodintro
  iframe Hl
  isplitr [HΦ]
  · ihave Hcc := Hcclose $$ Hv Hq
    rw [setEnd_endSt_self, setOut_out_self]
    iapply (netCtx_of_eq _ (setConn_self hcn))
    iapply Hgclose $$ %_ %(And.intro rfl rfl) Hcc
  iapply wp_value'
  iexact HΦ

/-- `AnyBool`: an arbitrary boolean. -/
theorem wp_net_AnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ (#b)) -∗ WP (ExternalOp netExt.name "AnyBool" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_net_op "AnyBool" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨b, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyString`: an arbitrary string. -/
theorem wp_net_AnyString (Φ : val → IProp GF) :
    (∀ str : GoString, Φ (#str)) -∗
      WP (ExternalOp netExt.name "AnyString" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_net_op "AnyString" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨str, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

theorem lisAddrs_insert (m : GMap w64 (GoString × Bool)) (l : w64) (x : GoString × Bool) :
    lisAddrs (m.insert l x) = (lisAddrs m).insert l x.1 := by
  unfold lisAddrs
  apply GMap.ext; intro k
  simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
  split <;> simp_all

theorem lisAddrs_lookup (m : GMap w64 (GoString × Bool)) (l : w64) :
    (lisAddrs m).lookup l = (m.lookup l).map Prod.fst := by
  unfold lisAddrs; rw [GMap.lookup_fmap]

/-- D6, D21. `Listen` of `a`, a valid address (`addrOk`) or a wildcard (`listenOk`), by the holder
of the right to listen at `a` (`lisToks`: the listening tokens of the valid addresses `a` takes,
`a`'s alone for a valid address, `lisToks_addrOk`), taken and given back by an atomic update at the
step, so that it may live in an invariant: a failure, or a new open listener at `a` (and its
address, persistent). -/
theorem wp_net_Listen (a : GoString) (Φ : val → IProp GF) :
    ⌜listenOk a = true⌝ -∗
    (|={E,∅}=> lisToks netG a ∗ (lisToks netG a ={∅,E}=∗ True)) -∗
    (Φ (failV .sys) ∧ ∀ l : w64, ⌜l ≠ 0⌝ -∗ netLis (netL (L := L)) l a true -∗
      netLisOn (netL (L := L)) l a -∗ Φ (PairV (#l) (#(W64 0)))) -∗
    WP (ExternalOp netExt.name "Listen" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (netL (L := L)).allG
  iintro %Hok Htok HΦ
  iapply wp_net_op "Listen" (#a) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  imod Htok with ⟨Ht, Hk⟩
  imod Hk $$ Ht with -
  unfold netLocalCtx
  icases Hl with ⟨Hlis, Hat⟩
  obtain ⟨a', Hv, -, Hcase, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨a, rfl, Hok⟩
  obtain rfl := go.intoVal_inj (V := GoString) Hv
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨-, l, hl0, hl, rfl, rfl⟩
  · icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hlis Hat Hg
    iapply wp_value'
    iexact HΦ
  · have hla : (lisAddrs σ.lis).lookup l = none := by rw [lisAddrs_lookup, hl]; rfl
    imod ghost_map_insert l (a, true) hl $$ Hlis with ⟨Hlis, Hel⟩
    imod ghost_map_insert_persist l a hla $$ Hat with ⟨Hat, #Hla⟩
    icases HΦ with ⟨-, HΦ⟩
    imodintro
    isplitl [Hlis Hat]
    · simp only
      rw [lisAddrs_insert]
      iframe Hlis Hat
    iframe Hg
    iapply wp_value'
    iapply HΦ $$ %l %hl0 [Hel]
    · unfold netLis; iexact Hel
    · unfold netLisOn; iframe Hla; ipureintro; exact Hok

theorem netLocal_lookup (hL : NetLocalGS GF) (σ : NetLocal) (l : w64) (a : GoString) (o : Bool) :
    netLocalCtx hL σ -∗ netLis hL l a o -∗ ⌜σ.lis !! l = some (a, o)⌝ := by
  letI := hL.allG
  unfold netLocalCtx netLis
  iintro ⟨Hlis, -⟩ Hel
  iapply ghost_map_lookup $$ Hlis Hel

/-- The listener `l` exists in the node's state, at `a`. -/
theorem netLisOn_lookup (hL : NetLocalGS GF) (σ : NetLocal) (l : w64) (a : GoString) :
    netLocalCtx hL σ -∗ netLisOn hL l a -∗ ⌜∃ o, σ.lis !! l = some (a, o)⌝ := by
  letI := hL.allG
  unfold netLocalCtx netLisOn
  iintro ⟨Hlis, Hat⟩ ⟨Hel, -⟩
  icases ghost_map_lookup $$ Hat Hel with %Hla
  ipureintro
  rw [lisAddrs_lookup] at Hla
  cases hl : σ.lis.lookup l with
  | none => rw [hl] at Hla; cases Hla
  | some x =>
    rw [hl] at Hla
    obtain ⟨a', o⟩ := x
    cases Hla
    exact ⟨o, rfl⟩

/-- D9, D17. `LisClose` of the listener `l` at `a`, by a logically atomic update over its state:
closed, the result `LisCloseOutcome`'s (success if it was open, `closed` if not). -/
theorem wp_net_LisClose (l : w64) (a : GoString) (Φ : val → IProp GF) :
    netLisOn (netL (L := L)) l a -∗
    (|={E,∅}=> ∃ o, netLis (netL (L := L)) l a o ∗
      ∀ res, ⌜LisCloseOutcome o res false⌝ -∗ netLis (netL (L := L)) l a false ={∅,E}=∗
        Φ (#(errCode res))) -∗
    WP (ExternalOp netExt.name "LisClose" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (netL (L := L)).allG
  iintro #Hla HAU
  iapply wp_net_op "LisClose" (#l) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  imod HAU with ⟨%o, Hel, Hk⟩
  ihave %Hll := netLocal_lookup _ σ l a o $$ Hl Hel
  obtain ⟨l0, a0, o0, res, o', Hv, Hl0, rfl, Hout, rfl, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨l, (a, o), rfl, Hll⟩
  obtain rfl := go.intoVal_inj (V := w64) Hv
  rw [Hll] at Hl0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Hl0)
  have ho' : o' = false := by unfold LisCloseOutcome at Hout; split at Hout <;> exact Hout.2
  subst ho'
  unfold netLocalCtx netLis
  icases Hl with ⟨Hlis, Hat⟩
  imod ghost_map_update (a, false) $$ Hlis Hel with ⟨Hlis, Hel⟩
  imod Hk $$ %res %Hout Hel with HΦ
  have hsame : lisAddrs (σ.lis.insert l (a, false)) = lisAddrs σ.lis := by
    rw [lisAddrs_insert]
    apply GMap.ext; intro k
    simp only [GMap.lookup_insert_eq_iff, lisAddrs_lookup]
    split
    · subst_vars; rw [Hll]; rfl
    · rfl
  imodintro
  iframe Hg
  isplitl [Hlis Hat]
  · simp only
    rw [hsame]
    iframe Hlis Hat
  iapply wp_value'
  iexact HΦ

/-- The resources of a new connection's end `s`: its state, fresh, and the direction from it, open
and empty. -/
def netFresh (hG : NetGS GF) (c : Nat) (s : Bool) : IProp GF :=
  iprop(netEnd hG c s NetEnd.fresh ∗ netDir hG c s NetDir.fresh)

/-- A new connection `cn` numbered `c`, dialed to the valid address `a`: the network with it, `c`
pending at `a`, and its ends' and directions' resources. -/
theorem netCtx_dial (hG : NetGS GF) (g : NetGlobal) (a : GoString) (c : Nat) (cn : NetConn)
    (S : GSet Nat) (ha : addrOk a = true) (hc : g.conns !! c = none) (h0 : c ≠ 0)
    (hb : 2 * c + 1 < 2 ^ 64) (hca : cn.addr = a) (hacc : cn.accepted = false)
    (hl0 : cn.lock false = false) (hl1 : cn.lock true = false) :
    netCtx hG g -∗ netPend hG a S ==∗
      ⌜c ∉ S⌝ ∗ netCtx hG (g.setConn c cn) ∗ netPend hG a (S ∪ {[c]}) ∗ netConnAt hG c a ∗
      netEnd hG c false (cn.endSt false) ∗ netDir hG c false (cn.out false) ∗
      netEnd hG c true (cn.endSt true) ∗ netDir hG c true (cn.out true) := by
  letI := hG.allG
  unfold netCtx
  iintro ⟨%nm, %pm, Hn, Hpm, %Hpure, Hconns⟩ Hpend
  obtain ⟨Hdom, Hpok⟩ := Hpure
  unfold netPend
  icases ghost_map_lookup $$ Hpm Hpend with %HS
  have hcS : c ∉ S := by
    rw [Hpok.2.1 a S c HS]; rintro ⟨cn, hcn, -⟩; simp [hc] at hcn
  have hnm : nm.lookup c = none := by
    have := Hdom c; rw [hc] at this
    cases hx : nm !! c with
    | none => rfl
    | some _ => rw [hx] at this; simp at this
  imod ghostVar_alloc_halves (cn.endSt false) with ⟨%γv0, Hv0, Hv0'⟩
  imod ghostVar_alloc_halves (cn.endSt true) with ⟨%γv1, Hv1, Hv1'⟩
  imod ghostVar_alloc_halves (cn.out false) with ⟨%γq0, Hq0, Hq0'⟩
  imod ghostVar_alloc_halves (cn.out true) with ⟨%γq1, Hq1, Hq1'⟩
  imod token_alloc (GF := GF) with ⟨%γt0, Ht0⟩
  imod token_alloc (GF := GF) with ⟨%γt1, Ht1⟩
  imod token_alloc (GF := GF) with ⟨%γw0, Hw0⟩
  imod token_alloc (GF := GF) with ⟨%γw1, Hw1⟩
  let γ : ConnNames := ⟨a, γv0, γv1, γq0, γq1, γt0, γt1, γw0, γw1⟩
  imod ghost_map_insert_persist c γ hnm $$ Hn with ⟨Hn, #Hγ⟩
  imod ghost_map_update (S ∪ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
  imodintro
  isplitr; · ipureintro; exact hcS
  iframe Hpend
  isplitl [Hn Hpm Hconns Hv0' Hv1' Hq0' Hq1' Hw0 Hw1]
  · iexists nm.insert c γ, pm.insert a (S ∪ {[c]})
    rw [setConn_conns]
    iframe Hn Hpm
    isplitr
    · ipureintro
      refine ⟨fun k => ?_, pendOk_dial Hpok hc h0 hb ha HS hca hacc⟩
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
      unfold connCtx lockCtx
      simp only [γ, ConnNames.v, ConnNames.q, ConnNames.wl, hl0, hl1, Bool.false_eq_true,
        ↓reduceIte]
      iframe Hv0' Hv1' Hq0' Hq1' Hw0 Hw1
      ipureintro; exact hca.symm
    iapply BigSepM.bigSepM_impl $$ Hconns
    iintro !> %k %cn' %Hk ⟨%γ', %Hγ', #Hn', Hcc⟩
    iexists γ'
    iframe Hn' Hcc
    ipureintro
    have hkc : c ≠ k := by rintro rfl; rw [gmap_get?_eq] at Hk; rw [hc] at Hk; cases Hk
    simp [GMap.lookup_insert_eq_iff, hkc, Hγ']
  isplitr
  · unfold netConnAt netNames; iexists γ; iframe Hγ; ipureintro; exact ⟨rfl, h0, hb⟩
  unfold netEnd netDir netNames
  simp only [γ, ConnNames.v, ConnNames.q, ConnNames.tk]
  isplitl [Hv0]; · iexists γ; iframe Hγ Hv0
  isplitl [Hq0 Ht0]; · iexists γ; iframe Hγ Hq0 Ht0
  isplitl [Hv1]; · iexists γ; iframe Hγ Hv1
  iexists γ; iframe Hγ Hq1 Ht1

/-- D8, D16. `Dial` of `a`, a valid address (`addrOk`): a failure that leaves nothing; or a new
connection `c` to `a`, pending at `a` (`netPend`, by a logically atomic update), with its
acceptor's end's resources, and either the dialer's (the dial succeeds) or, abandoned, a closed
dialer's end and its shut direction (the dial fails). -/
theorem wp_net_Dial (a : GoString) (Φ : val → IProp GF) :
    ⌜addrOk a = true⌝ -∗
    (Φ (failV .sys) ∧
      |={E,∅}=> ∃ S, netPend netG a S ∗
        ∀ c, ⌜c ∉ S⌝ -∗ netPend netG a (S ∪ {[c]}) -∗ netConnAt netG c a -∗
          netFresh netG c true -∗
          ((netFresh netG c false ={∅,E}=∗ Φ (PairV (#(endId c false)) (#(W64 0)))) ∧
           (netEnd netG c false { NetEnd.fresh with closed := true } -∗
            netDir netG c false ⟨[], .fin⟩ ={∅,E}=∗ Φ (failV .sys)))) -∗
    WP (ExternalOp netExt.name "Dial" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (netG (G := G)).allG
  iintro %Hpa HΦ
  iapply wp_net_op "Dial" (#a) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  obtain ⟨a0, Hv, ⟨-, Hcase⟩, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨a, rfl, Hpa⟩
  obtain rfl := go.intoVal_inj (V := GoString) Hv
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨c, ⟨hc0, hc, hb⟩, rfl, rfl⟩ | ⟨c, ⟨hc0, hc, hb⟩, rfl, rfl⟩
  · -- a failure
    icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- a new connection `c`
    icases HΦ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    imod netCtx_dial _ g a c (NetConn.fresh a) S Hpa hc hc0 hb rfl rfl rfl rfl $$ Hg Hpend
      with ⟨%HcS, Hg, Hpend, #Hat, He0, Hd0, He1, Hd1⟩
    simp only [NetConn.fresh, NetConn.endSt, NetConn.out]
    icases Hk $$ %c %HcS Hpend Hat [He1 Hd1] with Hk
    · unfold netFresh; iframe He1 Hd1
    icases Hk with ⟨Hk, -⟩
    imod Hk $$ [He0 Hd0] with HΦ
    · unfold netFresh; iframe He0 Hd0
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- a failure that leaves the connection `c`, abandoned
    icases HΦ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    imod netCtx_dial _ g a c (NetConn.abandoned a) S Hpa hc hc0 hb rfl rfl rfl rfl $$ Hg Hpend
      with ⟨%HcS, Hg, Hpend, #Hat, He0, Hd0, He1, Hd1⟩
    simp only [NetConn.abandoned, NetConn.endSt, NetConn.out]
    icases Hk $$ %c %HcS Hpend Hat [He1 Hd1] with Hk
    · unfold netFresh; iframe He1 Hd1
    icases Hk with ⟨-, Hk⟩
    imod Hk $$ He0 Hd0 with HΦ
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ

theorem connCtx_accepted [AllG GF] (γ : ConnNames) (cn : NetConn) (b : Bool) :
    connCtx (GF := GF) γ { cn with accepted := b } = connCtx γ cn := rfl

theorem connCtx_addr [AllG GF] (γ : ConnNames) (cn : NetConn) :
    connCtx (GF := GF) γ cn -∗ ⌜γ.addr = cn.addr⌝ := by
  unfold connCtx
  iintro ⟨%H, -⟩
  ipureintro; exact H


/-- D7, D21. `Accept` of the listener `l` at `la` (`netLisOn`: a valid address or a wildcard), by
logically atomic updates: a failure, by one over the listener's state, which it leaves as it was,
`closed` if the listener is closed and `sys` if it is open; or, only if the listener is open, a
connection `c` dialed to an address `a` the listener takes (`lisAccepts`: `la` itself if it is
valid, any valid address with its port if it is a wildcard) and pending there, now accepted, by one
over the listener's state and `a`'s pending set (`c` taken out of it), chosen for that `a`. An update
is opened only at the step that decides (a wait is a stutter, `wp_net_op`). -/
theorem wp_net_Accept (l : w64) (la : GoString) (Φ : val → IProp GF) :
    netLisOn (netL (L := L)) l la -∗
    ((|={E,∅}=> ∃ o, netLis (netL (L := L)) l la o ∗
        (netLis (netL (L := L)) l la o ={∅,E}=∗ Φ (failV (if o then .sys else .closed)))) ∧
      ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
        |={E,∅}=> ∃ o S, netLis (netL (L := L)) l la o ∗ netPend netG a S ∗
          (⌜o = true⌝ -∗ ∀ c, ⌜c ∈ S⌝ -∗ netLis (netL (L := L)) l la o -∗
            netPend netG a (S \ {[c]}) -∗ netConnAt netG c a ={∅,E}=∗
            Φ (PairV (#(endId c true)) (#(W64 0))))) -∗
    WP (ExternalOp netExt.name "Accept" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (netG (G := G)).allG
  iintro #Hla HAU
  iapply wp_net_op "Accept" (#l) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  ihave %Hll := netLisOn_lookup _ σ l la $$ Hl Hla
  obtain ⟨o, Hll⟩ := Hll
  obtain ⟨l0, a0, o0, Hv, Hl0, Hcase, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨l, (la, o), rfl, Hll⟩
  obtain rfl := go.intoVal_inj (V := w64) Hv
  rw [Hll] at Hl0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Hl0)
  rcases Hcase with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, c, cn, hcn, haddr, hacc, hb, rfl, rfl⟩
  · -- a failure, the listener closed
    icases HAU with ⟨HAU, -⟩
    imod HAU with ⟨%o', Hel, HΦ⟩
    icases netLocal_lookup _ _ l la o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    imod HΦ $$ Hel with HΦ
    subst ho
    simp only [Bool.false_eq_true, ↓reduceIte]
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- a failure, the listener open
    icases HAU with ⟨HAU, -⟩
    imod HAU with ⟨%o', Hel, HΦ⟩
    icases netLocal_lookup _ _ l la o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    imod HΦ $$ Hel with HΦ
    subst ho
    simp only [↓reduceIte]
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- the connection `c`, dialed to `cn.addr`
    unfold netCtx
    icases Hg with ⟨%nm, %pm, Hn, Hpm, %Hpure, Hconns⟩
    obtain ⟨Hdom, Hpok⟩ := Hpure
    have hok : addrOk cn.addr = true := (Hpok.2.2 c cn hcn).1
    icases HAU with ⟨-, HAU⟩
    have hp : addrOk cn.addr = true ∧ lisAccepts la cn.addr := ⟨hok, haddr⟩
    imod HAU $$ %cn.addr %hp with ⟨%o', %S, Hel, Hpend, Hk⟩
    icases netLocal_lookup _ _ l la o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    unfold netPend
    icases ghost_map_lookup $$ Hpm Hpend with %HS
    have hcS : c ∈ S := (Hpok.2.1 cn.addr S c HS).2 ⟨cn, hcn, rfl, hacc⟩
    have hc0 : c ≠ 0 := (Hpok.2.2 c cn hcn).2.1
    imod ghost_map_update (S \ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
    icases BigSepM.bigSepM_insert_acc hcn $$ Hconns with ⟨⟨%γ, %Hγ, #Hn', Hcc⟩, Hcl⟩
    icases connCtx_addr γ cn $$ Hcc with %Haddr
    imod Hk $$ %ho %c %hcS Hel [Hpend] [] with HΦ
    · iexact Hpend
    · unfold netConnAt
      iexists γ
      unfold netNames
      iframe Hn'
      ipureintro
      exact ⟨Haddr, hc0, hb⟩
    imodintro
    iframe Hl
    isplitr [HΦ]
    · iexists nm, pm.insert cn.addr (S \ {[c]})
      rw [setConn_conns]
      iframe Hn Hpm
      isplitr
      · ipureintro
        refine ⟨fun k => ?_, ?_⟩
        · rw [Hdom k]; simp only [GMap.lookup_insert_eq_iff]
          by_cases hk : c = k
          · subst hk; simp [hcn]
          · simp [hk]
        · exact pendOk_accept (S := S) Hpok hcn HS
      iapply Hcl
      iexists γ
      iframe Hn'
      isplitr
      · ipureintro; exact Hγ
      rw [connCtx_accepted γ cn true]
      iexact Hcc
    iapply wp_value'
    iexact HΦ

/-- `AnyW64`: an arbitrary word. -/
theorem wp_net_AnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ (#n)) -∗ WP (ExternalOp netExt.name "AnyW64" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_net_op "AnyW64" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨n, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyErrno`: an arbitrary nonzero word. -/
theorem wp_net_AnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ (#n)) -∗
      WP (ExternalOp netExt.name "AnyErrno" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_net_op "AnyErrno" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨n, hn, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ $$ %n %hn
  · exact absurd rfl hnv

end lifting

end Net
end Perennial
