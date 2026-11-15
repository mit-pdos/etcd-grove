/-
The WP specs of the TCP extension's operations (`Impl.lean`), over its ghost state (`Ghost.lean`).

Each spec's outcome is the operation's outcome relation in `Impl.lean`, verbatim (`ReadOutcome`,
`WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`): what a program may see is
exactly what the semantics allows, over the resources that are the semantics' state (`tcpEnd`,
`tcpDir`). The specs of the operations on a connection end are logically atomic: the end's state
and the direction it reads or writes are taken by an atomic update, so that a program may keep them
in an invariant shared by the threads that use the end (a reader and a writer, as grpc's and
net/http's connections have) or by both ends' nodes (a direction is written by one end and read by
the other). So are `Dial`'s and `Accept`'s, over the address's pending set (`tcpPend`), which a
program keeps in an invariant with its per-address protocol. Every operation may stutter (D22: a
wait), which one rule handles for all, by Löb induction (`wp_tcp_op`, as Perennial's Grove specs
do), so an update is opened only at the step that decides; the panics of invalid uses are excluded
there by the resources (the connection or listener exists, the address is the plan's). Each takes
`tcpConnAt c a` (persistent, from `Dial` or `Accept`): the connection exists, and its ends' ids are
in range and not `0`. Results are the values the step returns: a failure's kind as its code (`errCode`,
`TcpErr.code`, `failV`); a `Dial` that fails may leave its connection, abandoned (D16), whose
resources (the acceptor's end fresh, the dialer's closed with its direction shut) the caller's
update gets as a successful dial's.
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

@[simp] theorem endSt_setOut (cn : TcpConn) (s t : Bool) (d : TcpDir) :
    (cn.setOut s d).endSt t = cn.endSt t := by
  cases s <;> cases t <;> rfl

@[simp] theorem out_setOut (cn : TcpConn) (s t : Bool) (d : TcpDir) :
    (cn.setOut s d).out t = if s = t then d else cn.out t := by
  cases s <;> cases t <;> rfl

@[simp] theorem addr_setEnd (cn : TcpConn) (s : Bool) (st : TcpEnd) :
    (cn.setEnd s st).addr = cn.addr := by cases s <;> rfl
@[simp] theorem addr_setOut (cn : TcpConn) (s : Bool) (d : TcpDir) :
    (cn.setOut s d).addr = cn.addr := by cases s <;> rfl
@[simp] theorem accepted_setEnd (cn : TcpConn) (s : Bool) (st : TcpEnd) :
    (cn.setEnd s st).accepted = cn.accepted := by cases s <;> rfl
@[simp] theorem accepted_setOut (cn : TcpConn) (s : Bool) (d : TcpDir) :
    (cn.setOut s d).accepted = cn.accepted := by cases s <;> rfl

theorem setEnd_endSt_self (cn : TcpConn) (s : Bool) : cn.setEnd s (cn.endSt s) = cn := by
  cases s <;> rfl

theorem setOut_out_self (cn : TcpConn) (s : Bool) : cn.setOut s (cn.out s) = cn := by
  cases s <;> rfl

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


/-- A dial keeps `PendOk`, the new connection pending at its address. -/
theorem pendOk_dial {g : TcpGlobal} {pm : GMap GoString (GSet Nat)} {c : Nat} {a h : GoString}
    {S : GSet Nat} {cn : TcpConn} (hp : PendOk g pm) (hc : g.conns !! c = none)
    (h0 : c ≠ 0) (hb : 2 * c + 1 < 2 ^ 64) (ha : g.plan !! a = some h) (hS : pm !! a = some S)
    (hca : cn.addr = a) (hacc : cn.accepted = false) :
    PendOk (g.setConn c cn) (pm.insert a (S ∪ {[c]})) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun a' => ?_, fun a' S' k hS' => ?_, fun k cn₁ hk => ?_⟩
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
      · subst hkc; simp [hc, hca, hacc]
      · simp [hkc, Ne.symm hkc]
    · simp only [haa, ↓reduceIte] at hS'
      rw [h2 a' S' k hS']
      by_cases hkc : c = k
      · subst hkc; simp [hc, hca, haa]
      · simp [hkc]
  · simp only [setConn_conns, setConn_plan, GMap.lookup_insert_eq_iff] at hk ⊢
    by_cases hkc : c = k
    · subst hkc
      simp only [↓reduceIte, Option.some.injEq] at hk; subst hk
      exact ⟨by simp [hca, ha], h0, hb⟩
    · simp only [hkc, ↓reduceIte] at hk; exact h3 k cn₁ hk

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


/-! ## Outcome laws -/

section outcomes

/-- A step of a `Write` counts at most the bytes it was given. -/
theorem writeOutcome_le {st : TcpEnd} {d d' : TcpDir} {rs : List w8} {k : Nat}
    {res : Option TcpErr} (h : WriteOutcome st d rs k res d') : k ≤ rs.length := by
  unfold WriteOutcome at h
  split at h
  · rw [h.1]; exact Nat.zero_le _
  · split at h
    · rw [h.1]; exact Nat.zero_le _
    · rcases h.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega

/-- A failing step of a `Write` counts nothing. -/
theorem writeOutcome_fail {st : TcpEnd} {d d' : TcpDir} {rs : List w8} {k : Nat}
    {e : TcpErr} (h : WriteOutcome st d rs k (some e) d') : k = 0 := by
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

end outcomes




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
  obtain ⟨Hdom, Hpend, Hpln⟩ := Hpure
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
    refine ⟨fun k => ?_, pendOk_setConn Hpend hcn ha hacc, Hpln⟩
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
  obtain ⟨Hdom, Hpend, Hpln⟩ := Hpure
  icases ghost_map_lookup $$ Hn Hγ with %Hnγ
  have hsome : (g.conns !! c).isSome := by rw [← Hdom c]; simp [Hnγ]
  isplitr
  · ipureintro; exact Option.isSome_iff_exists.mp hsome
  iexists nm, pm
  iframe Hn Hp Hl Hconns
  ipureintro; exact ⟨Hdom, Hpend, Hpln⟩


/-- The connection's part of the context, by the end `s` and the direction `t`: their ghost
variables, and the context back for any new state of them. -/
theorem connCtx_acc [AllG GF] (γ : ConnNames) (cn : TcpConn) (s t : Bool) :
    connCtx (GF := GF) γ cn ⊢ ⌜γ.addr = cn.addr⌝ ∗
      ghostVar (γ.v s) (1 : Qp).half (cn.endSt s) ∗ ghostVar (γ.q t) (1 : Qp).half (cn.out t) ∗
      ∀ st' d', ghostVar (γ.v s) (1 : Qp).half st' -∗ ghostVar (γ.q t) (1 : Qp).half d' -∗
        connCtx γ ((cn.setEnd s st').setOut t d') := by
  unfold connCtx
  iintro ⟨%Ha, Hv0, Hv1, Hq0, Hq1⟩
  cases s <;> cases t
  · iframe Hv0 Hq0
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      ↓reduceIte, Bool.false_eq_true]
    iframe Hv Hq Hv1 Hq1
    ipureintro; exact Ha
  · iframe Hv0 Hq1
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
    iframe Hv Hq Hv1 Hq0
    ipureintro; exact Ha
  · iframe Hv1 Hq0
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
    iframe Hv Hq Hv0 Hq1
    ipureintro; exact Ha
  · iframe Hv1 Hq1
    isplitr; · ipureintro; exact Ha
    iintro %st' %d' Hv Hq
    simp only [endSt_setOut, endSt_setEnd, out_setOut, out_setEnd, addr_setOut, addr_setEnd,
      ↓reduceIte, Bool.true_eq_false]
    iframe Hv Hq Hv0 Hq0
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

theorem tcpEnd_open (hG : TcpGS GF) (c : Nat) (s : Bool) (st : TcpEnd) (γ : ConnNames) :
    tcpNames hG c γ -∗ tcpEnd hG c s st -∗ @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half st := by
  letI := hG.allG
  unfold tcpEnd
  iintro #Hγ ⟨%γ', #Hγ', Hv⟩
  icases tcpNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  iexact Hv

theorem tcpEnd_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (st : TcpEnd) (γ : ConnNames) :
    tcpNames hG c γ -∗ @ghostVar GF hG.allG _ _ (γ.v s) (1 : Qp).half st -∗ tcpEnd hG c s st := by
  letI := hG.allG
  unfold tcpEnd
  iintro #Hγ Hv
  iexists γ
  iframe Hγ Hv

theorem tcpDir_open (hG : TcpGS GF) (c : Nat) (s : Bool) (d : TcpDir) (γ : ConnNames) :
    tcpNames hG c γ -∗ tcpDir hG c s d -∗
      @ghostVar GF hG.allG _ _ (γ.q s) (1 : Qp).half d ∗ @token GF hG.allG (γ.tk s) := by
  letI := hG.allG
  unfold tcpDir
  iintro #Hγ ⟨%γ', #Hγ', Hq, Htk⟩
  icases tcpNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  iframe Hq Htk

theorem tcpDir_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (d : TcpDir) (γ : ConnNames) :
    tcpNames hG c γ -∗ @ghostVar GF hG.allG _ _ (γ.q s) (1 : Qp).half d -∗
      @token GF hG.allG (γ.tk s) -∗ tcpDir hG c s d := by
  letI := hG.allG
  unfold tcpDir
  iintro #Hγ Hq Htk
  iexists γ
  iframe Hγ Hq Htk

/-- A direction's resource is exclusive. -/
theorem tcpDir_excl (hG : TcpGS GF) (c : Nat) (s : Bool) (d d' : TcpDir) :
    tcpDir hG c s d -∗ tcpDir hG c s d' -∗ False := by
  letI := hG.allG
  unfold tcpDir
  iintro ⟨%γ, #Hγ, -, Htk⟩ ⟨%γ', #Hγ', -, Htk'⟩
  icases tcpNames_agree hG c γ γ' $$ Hγ Hγ' with %Heq
  subst Heq
  iapply token_exclusive $$ Htk Htk'


/-- A connection's ends have nonzero ids (no connection is numbered `0`): a zero-value `TCPConn`'s
id `0` is none of them. -/
theorem tcpConnAt_endId_ne (hG : TcpGS GF) (c : Nat) (a : GoString) (s : Bool) :
    tcpConnAt hG c a ⊢ ⌜endId c s ≠ 0⌝ := by
  letI := hG.allG
  unfold tcpConnAt
  iintro ⟨%γ, -, %h⟩
  ipureintro
  obtain ⟨-, h0, hb⟩ := h
  intro he
  exact h0 (endId_inj (s' := false) hb (by decide) (by rw [he]; rfl)).1

end laws

/-! ## The specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
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

theorem pair_w64_inj {e e' n n' : w64} (h : PairV (#e) (#n) = PairV (#e') (#n')) :
    e = e' ∧ n = n' := by
  obtain ⟨h1, h2⟩ := val.PairV.inj h
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

/-- D22. The lifting rule of the extension's operations: a WP of an operation from its outcome
rules (`IsTcpStep`), each with the node's and the network's interpretations; its stutters
(`TcpStep`'s other case) are handled here, by Löb induction, as Perennial's `wp_GroveOp` does. -/
theorem wp_tcp_op (o : String) (v : val) (hv : v.isPanic = false) (Φ : val → IProp GF) :
    ▷ (∀ σ g e' σ' g', ⌜IsTcpStep o v σ g e' σ' g'⌝ -∗ tcpLocalCtx (tcpL (L := L)) σ -∗
        tcpCtx (tcpG (G := G)) g ={E}=∗
        tcpLocalCtx (tcpL (L := L)) σ' ∗ tcpCtx (tcpG (G := G)) g' ∗ WP e' @ sk; E {{ Φ }}) ⊢
    WP (ExternalOp tcpExt.name o (Val v)) @ sk; E {{ Φ }} := by
  iloeb as IH
  iintro HΦ
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ, g, (show TcpStep o v h σ g _ h σ g from ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩)⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, Hcase⟩ := (show TcpStep o v h σ g e' h' σ' g' from Hst)
  imod Hclose
  rcases Hcase with ⟨rfl, rfl, rfl⟩ | Hop
  · -- a stutter
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply IH
    inext
    iexact HΦ
  · imod HΦ $$ %_ %_ %_ %_ %_ %Hop Hl Hg with ⟨Hl, Hg, Hwp⟩
    imodintro
    iframe Hheap Hwp
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg

/-- An operation on the end `s` of `c` and the direction from its end `t`, whose outcome rule on
the connection (when it exists) takes an outcome of `Out` (the end's state and the direction
before, the result, the end's state and the direction after) and writes the connection back. The
update is opened only at the outcome (a stutter, a wait, does not open it: `wp_tcp_op`). -/
theorem wp_tcp_endOp (o : String) (v : val) (hv : v.isPanic = false) (c : Nat) (s t : Bool)
    (Out : TcpEnd → TcpDir → val → TcpEnd → TcpDir → Prop)
    (Hstep : ∀ (σ : TcpLocal) (g : TcpGlobal) (e' : Expr) (σ' : TcpLocal) (g' : TcpGlobal)
        (cn0 : TcpConn), 2 * c + 1 < 2 ^ 64 → g.conns !! c = some cn0 →
      IsTcpStep o v σ g e' σ' g' →
        σ' = σ ∧ ∃ cn st' d' w, g.conns !! c = some cn ∧ Out (cn.endSt s) (cn.out t) w st' d' ∧
          e' = Val w ∧ g' = g.setConn c ((cn.setEnd s st').setOut t d'))
    (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c t d ∗
      ∀ w st' d', ⌜Out st d w st' d'⌝ -∗ tcpEnd tcpG c s st' -∗ tcpDir tcpG c t d'
        ={∅,E}=∗ Φ w) -∗
    WP (ExternalOp tcpExt.name o (Val v)) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold tcpConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_tcp_op o v hv Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases tcpCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
  obtain ⟨cn0, hcn0⟩ := Hcn
  obtain ⟨rfl, cn, st', d', w, hcn, Hout, rfl, rfl⟩ := Hstep σ g e' σ' g' cn0 Hγa.2.2 hcn0 Hst
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn1, %hcn1, Hcc, Hgclose⟩
  rw [hcn] at hcn1
  cases hcn1
  icases connCtx_acc γ cn s t $$ Hcc with ⟨%Haddr, Hv, Hq, Hcclose⟩
  icases tcpEnd_open _ c s st γ $$ Hγ Hend with Hv'
  icases tcpDir_open _ c t d γ $$ Hγ Hdir with ⟨Hq', Htk⟩
  icases ghostVar_agree $$ Hv' Hv with %Hst
  icases ghostVar_agree $$ Hq' Hq with %Hd
  subst Hst Hd
  imod ghostVar_update_halves st' $$ Hv' Hv with ⟨Hv', Hv⟩
  imod ghostVar_update_halves d' $$ Hq' Hq with ⟨Hq', Hq⟩
  imod Hk $$ %w %st' %d' %Hout [Hv'] [Hq' Htk] with HΦ
  · iapply tcpEnd_intro $$ Hγ Hv'
  · iapply tcpDir_intro $$ Hγ Hq' Htk
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
theorem wp_tcp_Read (c : Nat) (s : Bool) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c (!s) d ∗
      ∀ r d', ⌜ReadOutcome st d n.toNat r d'⌝ -∗ tcpEnd tcpG c s st -∗
        tcpDir tcpG c (!s) d' ={∅,E}=∗ Φ r.toVal) -∗
    WP (ExternalOp tcpExt.name "Read" (Val (PairV (#(endId c s)) (#n)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "Read" (PairV (#(endId c s)) (#n)) (by simp) c s (!s)
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

/-- D2. One step of a `Write`, of the bytes `bs` not yet written, at the end `s` of `c`, into the
direction from it (`WriteOutcome`). -/
theorem wp_tcp_Write (c : Nat) (s : Bool) (a : GoString) (bs : List w8) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c s d ∗
      ∀ k res d', ⌜WriteOutcome st d bs k res d'⌝ -∗ tcpEnd tcpG c s st -∗
        tcpDir tcpG c s d' ={∅,E}=∗ Φ (PairV (#(BitVec.ofNat 64 k)) (#(errCode res)))) -∗
    WP (ExternalOp tcpExt.name "Write" (Val (PairV (#(endId c s)) (#bs)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "Write" (PairV (#(endId c s)) (#bs)) (by simp) c s s
    (fun st d w st' d' => st' = st ∧ ∃ k res, WriteOutcome st d bs k res d' ∧
      w = PairV (#(BitVec.ofNat 64 k)) (#(errCode res)))
    ?_ a Φ $$ Hat
  · intro σ g e' σ' g' cn0 hb hcn0 hst
    rcases hst with ⟨e0, bs0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, k, res, d', hcn, hout, rfl, rfl⟩, rfl⟩ |
      ⟨hnv, -⟩
    · obtain ⟨h1, h2⟩ := val.PairV.inj hv
      have he : endId c s = e0 := go.intoVal_inj h1
      obtain rfl : bs = bs0 := go.intoVal_inj h2
      obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
      exact ⟨rfl, cn, cn.endSt s, d', _, hcn, ⟨rfl, k, res, hout, rfl⟩, rfl,
        by rw [setEnd_endSt_self]⟩
    · exact absurd ⟨endId c s, bs, c, s, rfl, ⟨hb, rfl⟩, by simp [hcn0]⟩ hnv
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨rfl, k, res, Hw, rfl⟩ := Hout
    iapply Hk $$ %k %res %d' %Hw Hend Hdir

/-- D3. `Close` of the end `s` of `c` (`CloseOutcome`). -/
theorem wp_tcp_Close (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c s d ∗
      ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗ tcpEnd tcpG c s st' -∗
        tcpDir tcpG c s d' ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp tcpExt.name "Close" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "Close" (#(endId c s)) (by simp) c s s
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
theorem wp_tcp_CloseWrite (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c s d ∗
      ∀ res d', ⌜CloseWriteOutcome st d res d'⌝ -∗ tcpEnd tcpG c s st -∗
        tcpDir tcpG c s d' ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp tcpExt.name "CloseWrite" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "CloseWrite" (#(endId c s)) (by simp) c s s
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
theorem wp_tcp_SetDeadline (c : Nat) (s : Bool) (a : GoString) (kind wall ext : w64)
    (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st, tcpEnd tcpG c s st ∗
      ∀ res st', ⌜DeadlineOutcome st kind (!timeIsZero wall ext) res st'⌝ -∗ tcpEnd tcpG c s st'
        ={∅,E}=∗ Φ (#(errCode res))) -∗
    WP (ExternalOp tcpExt.name "SetDeadline"
      (Val (PairV (#(endId c s)) (PairV (#kind) (PairV (#wall) (#ext)))))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold tcpConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_tcp_op "SetDeadline" _ (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases tcpCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
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
  icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn1, %hcn1, Hcc, Hgclose⟩
  rw [hcn] at hcn1
  cases hcn1
  icases connCtx_acc γ cn s s $$ Hcc with ⟨%Haddr, Hv, Hq, Hcclose⟩
  icases tcpEnd_open _ c s st γ $$ Hγ Hend with Hv'
  icases ghostVar_agree $$ Hv' Hv with %Hst
  subst Hst
  imod ghostVar_update_halves st' $$ Hv' Hv with ⟨Hv', Hv⟩
  imod Hk $$ %res %st' %hout [Hv'] with HΦ
  · iapply tcpEnd_intro $$ Hγ Hv'
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

/-- `AnyBool`: an arbitrary boolean. -/
theorem wp_tcp_AnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ (#b)) -∗ WP (ExternalOp tcpExt.name "AnyBool" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_tcp_op "AnyBool" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨b, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyString`: an arbitrary string. -/
theorem wp_tcp_AnyString (Φ : val → IProp GF) :
    (∀ str : GoString, Φ (#str)) -∗
      WP (ExternalOp tcpExt.name "AnyString" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_tcp_op "AnyString" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨str, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- The plan has `a` at `h` (the context is kept). -/
theorem tcpCtx_plan (hG : TcpGS GF) (g : TcpGlobal) (a h : GoString) :
    tcpCtx hG g -∗ tcpPlan hG a h -∗ ⌜g.plan !! a = some h⌝ := by
  letI := hG.allG
  unfold tcpCtx tcpPlan
  iintro ⟨%nm, %pm, Hn, Hp, Hl, %Hpure, Hconns⟩ #Ha
  iapply ghost_map_lookup $$ Hl Ha

/-- The network's plan is the ghost state's (the context is kept). -/
theorem tcpCtx_plan_eq (hG : TcpGS GF) (g : TcpGlobal) :
    tcpCtx hG g -∗ ⌜g.plan = hG.plan⌝ ∗ tcpCtx hG g := by
  letI := hG.allG
  unfold tcpCtx
  iintro ⟨%nm, %pm, Hn, Hp, Hl, %Hpure, Hconns⟩
  isplitr; · ipureintro; exact Hpure.2.2
  iexists nm, pm
  iframe Hn Hp Hl Hconns
  ipureintro; exact Hpure

theorem lisAddrs_insert (m : GMap w64 (GoString × Bool)) (l : w64) (x : GoString × Bool) :
    lisAddrs (m.insert l x) = (lisAddrs m).insert l x.1 := by
  unfold lisAddrs
  apply GMap.ext; intro k
  simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
  split <;> simp_all

theorem lisAddrs_lookup (m : GMap w64 (GoString × Bool)) (l : w64) :
    (lisAddrs m).lookup l = (m.lookup l).map Prod.fst := by
  unfold lisAddrs; rw [GMap.lookup_fmap]

/-- `ListenAt` is functional: a `Listen` of `a` resolves to one address. -/
theorem listenAt_unique {P : GMap GoString GoString} {h a a0 a1 : GoString}
    (h0 : ListenAt P h a a0) (h1 : ListenAt P h a a1) : a0 = a1 := by
  obtain ⟨hp0, rfl | ⟨hn0, p0, hw0, hq0, hu0⟩⟩ := h0 <;>
    obtain ⟨hp1, rfl | ⟨hn1, p1, hw1, hq1, hu1⟩⟩ := h1
  · rfl
  · rw [hn1] at hp0; cases hp0
  · rw [hn0] at hp1; cases hp1
  · rw [hw0] at hw1; cases hw1
    exact (hu0 a1 (by rw [hp1]; rfl) hq1).symm

/-- An address of the plan at `h`: a `Listen` of it listens at it. -/
theorem listenAt_self {P : GMap GoString GoString} {h a : GoString} (hp : P !! a = some h) :
    ListenAt P h a a := ⟨hp, .inl rfl⟩

/-- D6, D21. `Listen` of `a`, which resolves to `a0` (`ListenAt`, over the network's plan, at this
node's host): a failure, or a new open listener at `a0` (and its address, persistent). -/
theorem wp_tcp_Listen (a a0 : GoString) (Φ : val → IProp GF) :
    ⌜ListenAt (tcpG (G := G)).plan (tcpL (L := L)).host a a0⌝ -∗
    (Φ (failV .sys) ∧ ∀ l : w64, ⌜l ≠ 0⌝ -∗ tcpLis (tcpL (L := L)) l a0 true -∗
      tcpLisAt (tcpL (L := L)) l a0 -∗ Φ (PairV (#l) (#(W64 0)))) -∗
    WP (ExternalOp tcpExt.name "Listen" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (tcpL (L := L)).allG
  iintro %Hla HΦ
  iapply wp_tcp_op "Listen" (#a) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases tcpCtx_plan_eq _ g $$ Hg with ⟨%Hpln, Hg⟩
  unfold tcpLocalCtx
  icases Hl with ⟨%Hhost, Hlis, Hat⟩
  have Hla' : ListenAt g.plan σ.host a a0 := by rw [Hpln, Hhost]; exact Hla
  obtain ⟨a', Hv, ⟨a1, Hla1, Hcase⟩, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨a, a0, rfl, Hla'⟩
  obtain rfl := go.intoVal_inj (V := GoString) Hv
  obtain rfl := listenAt_unique Hla' Hla1
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨-, l, hl0, hl, rfl, rfl⟩
  · icases HΦ with ⟨HΦ, -⟩
    imodintro
    isplitl [Hlis Hat]
    · iframe Hlis Hat; ipureintro; exact Hhost
    iframe Hg
    iapply wp_value'
    iexact HΦ
  · have hla : (lisAddrs σ.lis).lookup l = none := by rw [lisAddrs_lookup, hl]; rfl
    imod ghost_map_insert l (a0, true) hl $$ Hlis with ⟨Hlis, Hel⟩
    imod ghost_map_insert_persist l a0 hla $$ Hat with ⟨Hat, #Hla⟩
    icases HΦ with ⟨-, HΦ⟩
    imodintro
    isplitl [Hlis Hat]
    · simp only
      rw [lisAddrs_insert]
      iframe Hlis Hat; ipureintro; exact Hhost
    iframe Hg
    iapply wp_value'
    iapply HΦ $$ %l %hl0 [Hel]
    · unfold tcpLis; iexact Hel
    · unfold tcpLisAt; iexact Hla

theorem tcpLocal_lookup (hL : TcpLocalGS GF) (σ : TcpLocal) (l : w64) (a : GoString) (o : Bool) :
    tcpLocalCtx hL σ -∗ tcpLis hL l a o -∗ ⌜σ.lis !! l = some (a, o)⌝ := by
  letI := hL.allG
  unfold tcpLocalCtx tcpLis
  iintro ⟨%Hhost, Hlis, -⟩ Hel
  iapply ghost_map_lookup $$ Hlis Hel

/-- The listener `l` exists in the node's state, at `a`. -/
theorem tcpLisAt_lookup (hL : TcpLocalGS GF) (σ : TcpLocal) (l : w64) (a : GoString) :
    tcpLocalCtx hL σ -∗ tcpLisAt hL l a -∗ ⌜∃ o, σ.lis !! l = some (a, o)⌝ := by
  letI := hL.allG
  unfold tcpLocalCtx tcpLisAt
  iintro ⟨%Hhost, Hlis, Hat⟩ Hel
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
theorem wp_tcp_LisClose (l : w64) (a : GoString) (Φ : val → IProp GF) :
    tcpLisAt (tcpL (L := L)) l a -∗
    (|={E,∅}=> ∃ o, tcpLis (tcpL (L := L)) l a o ∗
      ∀ res, ⌜LisCloseOutcome o res false⌝ -∗ tcpLis (tcpL (L := L)) l a false ={∅,E}=∗
        Φ (#(errCode res))) -∗
    WP (ExternalOp tcpExt.name "LisClose" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (tcpL (L := L)).allG
  iintro #Hla HAU
  iapply wp_tcp_op "LisClose" (#l) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  imod HAU with ⟨%o, Hel, Hk⟩
  ihave %Hll := tcpLocal_lookup _ σ l a o $$ Hl Hel
  obtain ⟨l0, a0, o0, res, o', Hv, Hl0, rfl, Hout, rfl, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨l, (a, o), rfl, Hll⟩
  obtain rfl := go.intoVal_inj (V := w64) Hv
  rw [Hll] at Hl0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Hl0)
  have ho' : o' = false := by unfold LisCloseOutcome at Hout; split at Hout <;> exact Hout.2
  subst ho'
  unfold tcpLocalCtx tcpLis
  icases Hl with ⟨%Hhost, Hlis, Hat⟩
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
    iframe Hlis Hat; ipureintro; exact Hhost
  iapply wp_value'
  iexact HΦ

/-- The resources of a new connection's end `s`: its state, fresh, and the direction from it, open
and empty. -/
def tcpFresh (hG : TcpGS GF) (c : Nat) (s : Bool) : IProp GF :=
  iprop(tcpEnd hG c s TcpEnd.fresh ∗ tcpDir hG c s TcpDir.fresh)

/-- A new connection `cn` numbered `c`, dialed to the plan address `a`: the network with it, `c`
pending at `a`, and its ends' and directions' resources. -/
theorem tcpCtx_dial (hG : TcpGS GF) (g : TcpGlobal) (a h : GoString) (c : Nat) (cn : TcpConn)
    (S : GSet Nat) (ha : g.plan !! a = some h) (hc : g.conns !! c = none) (h0 : c ≠ 0)
    (hb : 2 * c + 1 < 2 ^ 64) (hca : cn.addr = a) (hacc : cn.accepted = false) :
    tcpCtx hG g -∗ tcpPend hG a S ==∗
      ⌜c ∉ S⌝ ∗ tcpCtx hG (g.setConn c cn) ∗ tcpPend hG a (S ∪ {[c]}) ∗ tcpConnAt hG c a ∗
      tcpEnd hG c false (cn.endSt false) ∗ tcpDir hG c false (cn.out false) ∗
      tcpEnd hG c true (cn.endSt true) ∗ tcpDir hG c true (cn.out true) := by
  letI := hG.allG
  unfold tcpCtx
  iintro ⟨%nm, %pm, Hn, Hpm, Hpl, %Hpure, Hconns⟩ Hpend
  obtain ⟨Hdom, Hpok, Hpln⟩ := Hpure
  unfold tcpPend
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
  let γ : ConnNames := ⟨a, γv0, γv1, γq0, γq1, γt0, γt1⟩
  imod ghost_map_insert_persist c γ hnm $$ Hn with ⟨Hn, #Hγ⟩
  imod ghost_map_update (S ∪ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
  imodintro
  isplitr; · ipureintro; exact hcS
  iframe Hpend
  isplitl [Hn Hpm Hpl Hconns Hv0' Hv1' Hq0' Hq1']
  · iexists nm.insert c γ, pm.insert a (S ∪ {[c]})
    rw [setConn_plan, setConn_conns]
    iframe Hn Hpm Hpl
    isplitr
    · ipureintro
      refine ⟨fun k => ?_, pendOk_dial Hpok hc h0 hb ha HS hca hacc, Hpln⟩
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
      unfold connCtx
      simp only [γ, ConnNames.v, ConnNames.q]
      iframe Hv0' Hv1' Hq0' Hq1'
      ipureintro; exact hca.symm
    iapply BigSepM.bigSepM_impl $$ Hconns
    iintro !> %k %cn' %Hk ⟨%γ', %Hγ', #Hn', Hcc⟩
    iexists γ'
    iframe Hn' Hcc
    ipureintro
    have hkc : c ≠ k := by rintro rfl; rw [gmap_get?_eq] at Hk; rw [hc] at Hk; cases Hk
    simp [GMap.lookup_insert_eq_iff, hkc, Hγ']
  isplitr
  · unfold tcpConnAt tcpNames; iexists γ; iframe Hγ; ipureintro; exact ⟨rfl, h0, hb⟩
  unfold tcpEnd tcpDir tcpNames
  simp only [γ, ConnNames.v, ConnNames.q, ConnNames.tk]
  isplitl [Hv0]; · iexists γ; iframe Hγ Hv0
  isplitl [Hq0 Ht0]; · iexists γ; iframe Hγ Hq0 Ht0
  isplitl [Hv1]; · iexists γ; iframe Hγ Hv1
  iexists γ; iframe Hγ Hq1 Ht1

/-- D8, D16. `Dial` of `a`, an address of the plan: a failure that leaves nothing; or a new
connection `c` to `a`, pending at `a` (`tcpPend`, by a logically atomic update), with its
acceptor's end's resources, and either the dialer's (the dial succeeds) or, abandoned, a closed
dialer's end and its shut direction (the dial fails). -/
theorem wp_tcp_Dial (a h : GoString) (Φ : val → IProp GF) :
    tcpPlan tcpG a h -∗
    (Φ (failV .sys) ∧
      |={E,∅}=> ∃ S, tcpPend tcpG a S ∗
        ∀ c, ⌜c ∉ S⌝ -∗ tcpPend tcpG a (S ∪ {[c]}) -∗ tcpConnAt tcpG c a -∗
          tcpFresh tcpG c true -∗
          ((tcpFresh tcpG c false ={∅,E}=∗ Φ (PairV (#(endId c false)) (#(W64 0)))) ∧
           (tcpEnd tcpG c false { TcpEnd.fresh with closed := true } -∗
            tcpDir tcpG c false ⟨[], .fin⟩ ={∅,E}=∗ Φ (failV .sys)))) -∗
    WP (ExternalOp tcpExt.name "Dial" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hp HΦ
  iapply wp_tcp_op "Dial" (#a) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  icases tcpCtx_plan _ g a _ $$ Hg Hp with %Hpa
  obtain ⟨a0, Hv, ⟨-, Hcase⟩, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨a, rfl, by simp [Hpa]⟩
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
    imod tcpCtx_dial _ g a _ c (TcpConn.fresh a) S Hpa hc hc0 hb rfl rfl $$ Hg Hpend
      with ⟨%HcS, Hg, Hpend, #Hat, He0, Hd0, He1, Hd1⟩
    simp only [TcpConn.fresh, TcpConn.endSt, TcpConn.out]
    icases Hk $$ %c %HcS Hpend Hat [He1 Hd1] with Hk
    · unfold tcpFresh; iframe He1 Hd1
    icases Hk with ⟨Hk, -⟩
    imod Hk $$ [He0 Hd0] with HΦ
    · unfold tcpFresh; iframe He0 Hd0
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- a failure that leaves the connection `c`, abandoned
    icases HΦ with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hpend, Hk⟩
    imod tcpCtx_dial _ g a _ c (TcpConn.abandoned a) S Hpa hc hc0 hb rfl rfl $$ Hg Hpend
      with ⟨%HcS, Hg, Hpend, #Hat, He0, Hd0, He1, Hd1⟩
    simp only [TcpConn.abandoned, TcpConn.endSt, TcpConn.out]
    icases Hk $$ %c %HcS Hpend Hat [He1 Hd1] with Hk
    · unfold tcpFresh; iframe He1 Hd1
    icases Hk with ⟨-, Hk⟩
    imod Hk $$ He0 Hd0 with HΦ
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ

theorem connCtx_accepted [AllG GF] (γ : ConnNames) (cn : TcpConn) (b : Bool) :
    connCtx (GF := GF) γ { cn with accepted := b } = connCtx γ cn := rfl

theorem connCtx_addr [AllG GF] (γ : ConnNames) (cn : TcpConn) :
    connCtx (GF := GF) γ cn -∗ ⌜γ.addr = cn.addr⌝ := by
  unfold connCtx
  iintro ⟨%H, -, -⟩
  ipureintro; exact H


/-- D7. `Accept` of the listener `l` at `a`, by a logically atomic update over its state and the
address's pending set: a failure (both unchanged), `closed` if the listener is closed and `sys` if
it is open; or, only if the listener is open, a connection `c` pending at `a`, now accepted (taken
out of the pending set). The update is opened only at the step that decides (a wait is a stutter,
`wp_tcp_op`). -/
theorem wp_tcp_Accept (l : w64) (a : GoString) (Φ : val → IProp GF) :
    tcpLisAt (tcpL (L := L)) l a -∗
    (|={E,∅}=> ∃ o S, tcpLis (tcpL (L := L)) l a o ∗ tcpPend tcpG a S ∗
      ((tcpLis (tcpL (L := L)) l a o -∗ tcpPend tcpG a S ={∅,E}=∗
          Φ (failV (if o then .sys else .closed))) ∧
        (⌜o = true⌝ -∗ ∀ c, ⌜c ∈ S⌝ -∗ tcpLis (tcpL (L := L)) l a o -∗
          tcpPend tcpG a (S \ {[c]}) -∗ tcpConnAt tcpG c a ={∅,E}=∗
          Φ (PairV (#(endId c true)) (#(W64 0)))))) -∗
    WP (ExternalOp tcpExt.name "Accept" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hla HAU
  iapply wp_tcp_op "Accept" (#l) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  ihave %Hll := tcpLisAt_lookup _ σ l a $$ Hl Hla
  obtain ⟨o, Hll⟩ := Hll
  obtain ⟨l0, a0, o0, Hv, Hl0, Hcase, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨l, (a, o), rfl, Hll⟩
  obtain rfl := go.intoVal_inj (V := w64) Hv
  rw [Hll] at Hl0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj Hl0)
  rcases Hcase with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, c, cn, hcn, haddr, hacc, hb, rfl, rfl⟩
  · -- a failure, the listener closed
    imod HAU with ⟨%o', %S, Hel, Hpend, HΦ⟩
    icases tcpLocal_lookup _ _ l a o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    icases HΦ with ⟨HΦ, -⟩
    imod HΦ $$ Hel Hpend with HΦ
    subst ho
    simp only [Bool.false_eq_true, ↓reduceIte]
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- a failure, the listener open
    imod HAU with ⟨%o', %S, Hel, Hpend, HΦ⟩
    icases tcpLocal_lookup _ _ l a o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    icases HΦ with ⟨HΦ, -⟩
    imod HΦ $$ Hel Hpend with HΦ
    subst ho
    simp only [↓reduceIte]
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · -- the connection `c`
    imod HAU with ⟨%o', %S, Hel, Hpend, HΦ⟩
    icases tcpLocal_lookup _ _ l a o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    icases HΦ with ⟨-, Hk⟩
    unfold tcpCtx
    icases Hg with ⟨%nm, %pm, Hn, Hpm, Hpl, %Hpure, Hconns⟩
    obtain ⟨Hdom, Hpok, Hpln⟩ := Hpure
    unfold tcpPend
    icases ghost_map_lookup $$ Hpm Hpend with %HS
    have hcS : c ∈ S := (Hpok.2.1 a S c HS).2 ⟨cn, hcn, haddr, hacc⟩
    have hc0 : c ≠ 0 := (Hpok.2.2 c cn hcn).2.1
    imod ghost_map_update (S \ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
    icases BigSepM.bigSepM_insert_acc hcn $$ Hconns with ⟨⟨%γ, %Hγ, #Hn', Hcc⟩, Hcl⟩
    icases connCtx_addr γ cn $$ Hcc with %Haddr
    imod Hk $$ %ho %c %hcS Hel [Hpend] [] with HΦ
    · iexact Hpend
    · unfold tcpConnAt
      iexists γ
      unfold tcpNames
      iframe Hn'
      ipureintro
      exact ⟨Haddr.trans haddr, hc0, hb⟩
    imodintro
    iframe Hl
    isplitr [HΦ]
    · iexists nm, pm.insert a (S \ {[c]})
      rw [setConn_plan, setConn_conns]
      iframe Hn Hpm Hpl
      isplitr
      · ipureintro
        refine ⟨fun k => ?_, ?_, Hpln⟩
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
    iexact HΦ

/-- `AnyW64`: an arbitrary word. -/
theorem wp_tcp_AnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ (#n)) -∗ WP (ExternalOp tcpExt.name "AnyW64" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_tcp_op "AnyW64" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨n, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyErrno`: an arbitrary nonzero word. -/
theorem wp_tcp_AnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ (#n)) -∗
      WP (ExternalOp tcpExt.name "AnyErrno" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_tcp_op "AnyErrno" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨n, hn, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ $$ %n %hn
  · exact absurd rfl hnv

end lifting

end Tcp
end Perennial
