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
program keeps in an invariant with its per-address protocol. An operation that may wait (`Read`,
`Accept`) uses its update only at the step that decides (`wp_tcp_endOp`). Each takes
`tcpConnAt c a` (persistent, from `Dial` or `Accept`): the connection exists, and its ends' ids are
in range.
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


/-! ## Every operation has an outcome -/

section outcomes

theorem readOutcome_total (st : TcpEnd) (d : TcpDir) (n : Nat) :
    ∃ r d', ReadOutcome st d n r d' := by
  unfold ReadOutcome
  split
  · exact ⟨_, _, rfl, rfl⟩
  · split
    · exact ⟨_, _, rfl, rfl⟩
    · exact ⟨.err, ⟨d.bytes.take 0, .cut⟩,
        .inr ⟨0, Nat.zero_le _, .inr (.inr (.inr (.inl ⟨rfl, rfl, rfl⟩)))⟩⟩

theorem readAvail_wait {st : TcpEnd} {d d' : TcpDir} {n : Nat}
    (h : ReadAvail st d n .wait d') : d' = d ∧ d.status = .open := by
  rcases h with ⟨_, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h1, _, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
  · cases h
  · cases h
  · exact ⟨h, h1⟩
  · cases h
  · cases h

theorem readOutcome_wait {st : TcpEnd} {d d' : TcpDir} {n : Nat}
    (h : ReadOutcome st d n .wait d') : d' = d := by
  unfold ReadOutcome at h
  split at h
  · cases h.1
  · split at h
    · cases h.1
    · rcases h with h | ⟨k, -, h⟩
      · exact (readAvail_wait h).1
      · cases (readAvail_wait h).2

theorem writeOutcome_total (st : TcpEnd) (d : TcpDir) (bs : List w8) :
    ∃ k ok d', WriteOutcome st d bs k ok d' := by
  unfold WriteOutcome
  split
  · exact ⟨_, _, _, rfl, rfl, rfl⟩
  · split
    · exact ⟨_, _, _, .inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨_, _, _, .inl ⟨rfl, rfl, rfl⟩⟩

theorem closeOutcome_total (st : TcpEnd) (d : TcpDir) :
    ∃ ok st' d', CloseOutcome st d ok st' d' := by
  unfold CloseOutcome
  split
  · exact ⟨_, _, _, rfl, rfl, rfl⟩
  · exact ⟨true, _, _, rfl, rfl⟩

theorem closeWriteOutcome_total (st : TcpEnd) (d : TcpDir) :
    ∃ ok d', CloseWriteOutcome st d ok d' := by
  unfold CloseWriteOutcome
  split
  · exact ⟨_, _, rfl, rfl⟩
  · exact ⟨_, _, .inl ⟨rfl, rfl⟩⟩

theorem deadlineOutcome_total (st : TcpEnd) (kind : w64) (set : Bool) :
    ∃ ok st', DeadlineOutcome st kind set ok st' := by
  unfold DeadlineOutcome
  split
  · exact ⟨_, _, rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl⟩

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

/-- An operation on the end `s` of `c` and the direction from its end `t`, whose step takes an
outcome of `Out` (the end's state and the direction before, the result, the end's state and the
direction after) and writes the connection back; its result is a value, or the operation itself
(it waits, changing nothing). The update is opened only when the operation returns. -/
theorem wp_tcp_endOp (o : String) (v : val) (hv : v.isPanic = false) (c : Nat) (s t : Bool)
    (Out : TcpEnd → TcpDir → Expr → TcpEnd → TcpDir → Prop)
    (Hstep : ∀ (h : GMap Loc (NonAtomic val)) (σ : TcpLocal) (g : TcpGlobal) (e' : Expr)
        (h' : GMap Loc (NonAtomic val)) (σ' : TcpLocal) (g' : TcpGlobal), 2 * c + 1 < 2 ^ 64 →
      ExtSemantics.step (E := tcpExt) o v h σ g e' h' σ' g' →
        h' = h ∧ σ' = σ ∧ ∃ cn st' d', g.conns !! c = some cn ∧
          Out (cn.endSt s) (cn.out t) e' st' d' ∧ g' = g.setConn c ((cn.setEnd s st').setOut t d'))
    (Hex : ∀ (h : GMap Loc (NonAtomic val)) (σ : TcpLocal) (g : TcpGlobal) (cn : TcpConn),
        2 * c + 1 < 2 ^ 64 → g.conns !! c = some cn →
      ∃ e' g', ExtSemantics.step (E := tcpExt) o v h σ g e' h σ g')
    (Hwait : ∀ st d st' d', Out st d (ExternalOp tcpExt.name o (Val v)) st' d' →
      st' = st ∧ d' = d)
    (Hval : ∀ st d e' st' d', Out st d e' st' d' →
      e' = ExternalOp tcpExt.name o (Val v) ∨ ∃ w, e' = Val w)
    (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c t d ∗
      ∀ w st' d', ⌜Out st d (Val w) st' d'⌝ -∗ tcpEnd tcpG c s st' -∗ tcpDir tcpG c t d'
        ={∅,E}=∗ Φ w) -∗
    WP (ExternalOp tcpExt.name o (Val v)) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iloeb as IH
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold tcpConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  icases tcpCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
  obtain ⟨cn0, hcn0⟩ := Hcn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    obtain ⟨e', g', hst⟩ := Hex h σ g cn0 Hγa.2 hcn0
    exact ⟨e', h, σ, g', hst⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, rfl, cn, st', d', hcn, Hout, rfl⟩ := Hstep h σ g e' h' σ' g' Hγa.2 Hst
  imod Hclose
  rcases Hval _ _ _ _ _ Hout with Hw | ⟨w, rfl⟩
  · -- it waits: nothing changes
    subst Hw
    obtain ⟨rfl, rfl⟩ := Hwait _ _ _ _ Hout
    rw [setEnd_endSt_self, setOut_out_self, setConn_self hcn]
    imodintro
    iframe Hheap Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply IH $$ Hat HAU
  · -- it returns `w`
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
    iframe Hheap Hl
    isplitr [HΦ]
    · iapply (tcp_global_ctx_eq _).mpr
      iapply Hgclose $$ %_ %(And.intro (by simp) (by simp))
      iapply Hcclose $$ Hv Hq
    iapply wp_value'
    iexact HΦ

/-- The value a returning read gives (a waiting read gives none: `wait` maps to an error's). -/
def ReadRes.toVal : ReadRes → val
  | .bytes bs => readRes bs 0
  | .eof => readRes [] 1
  | .err => readRes [] 2
  | .wait => readRes [] 2

/-- The bytes a read returned (none for EOF or an error). -/
def ReadRes.got : ReadRes → List w8
  | .bytes bs => bs
  | _ => []

theorem ReadRes.toExpr_val {e0 : Expr} {r : ReadRes} {w : val} (h : Val w = r.toExpr e0)
    (hop : ∀ w', e0 ≠ Val w') : r ≠ .wait ∧ w = r.toVal := by
  cases r with
  | bytes bs => exact ⟨by simp, by simpa [ReadRes.toExpr, ReadRes.toVal] using h⟩
  | eof => exact ⟨by simp, by simpa [ReadRes.toExpr, ReadRes.toVal] using h⟩
  | err => exact ⟨by simp, by simpa [ReadRes.toExpr, ReadRes.toVal] using h⟩
  | wait => exact absurd h.symm (hop w)

/-- D1. `Read` of `n` bytes at the end `s` of `c`, from the direction towards it
(`ReadOutcome`). -/
theorem wp_tcp_Read (c : Nat) (s : Bool) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c (!s) d ∗
      ∀ r d', ⌜ReadOutcome st d n.toNat r d' ∧ r ≠ .wait⌝ -∗ tcpEnd tcpG c s st -∗
        tcpDir tcpG c (!s) d' ={∅,E}=∗ Φ r.toVal) -∗
    WP (ExternalOp tcpExt.name "Read" (Val (PairV (#(endId c s)) (#n)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "Read" (PairV (#(endId c s)) (#n)) (by simp) c s (!s)
    (fun st d e' st' d' => st' = st ∧ ∃ r, ReadOutcome st d n.toNat r d' ∧
      e' = r.toExpr (ExternalOp tcpExt.name "Read" (Val (PairV (#(endId c s)) (#n)))))
    ?_ ?_ ?_ ?_ a Φ $$ Hat
  · intro h σ g e' h' σ' g' hb hst
    obtain ⟨rfl, e0, n0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, r, d', hcn, hout, rfl, rfl⟩, rfl⟩ := hst
    obtain ⟨he, rfl⟩ := pair_w64_inj hv
    obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
    exact ⟨rfl, rfl, cn, cn.endSt s, d', hcn, ⟨rfl, r, hout, rfl⟩, by rw [setEnd_endSt_self]⟩
  · intro h σ g cn hb hcn
    obtain ⟨r, d', hr⟩ := readOutcome_total (cn.endSt s) (cn.out (!s)) n.toNat
    exact ⟨_, _, rfl, endId c s, n, c, s, rfl, ⟨hb, rfl⟩, ⟨cn, r, d', hcn, hr, rfl, rfl⟩, rfl⟩
  · rintro st d st' d' ⟨hst, r, hr, he⟩
    cases r with
    | wait => exact ⟨hst, readOutcome_wait hr⟩
    | bytes => cases he
    | eof => cases he
    | err => cases he
  · rintro st d e' st' d' ⟨-, r, -, rfl⟩
    cases r with
    | wait => exact .inl rfl
    | bytes bs => exact .inr ⟨_, rfl⟩
    | eof => exact .inr ⟨_, rfl⟩
    | err => exact .inr ⟨_, rfl⟩
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨rfl, r, Hr, Hw⟩ := Hout
    obtain ⟨hr, rfl⟩ := ReadRes.toExpr_val Hw (fun _ h => by cases h)
    iapply Hk $$ %r %d' %(And.intro Hr hr) Hend Hdir

/-- D2. `Write` of `bs` at the end `s` of `c`, into the direction from it (`WriteOutcome`). -/
theorem wp_tcp_Write (c : Nat) (s : Bool) (a : GoString) (bs : List w8) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c s d ∗
      ∀ k ok d', ⌜WriteOutcome st d bs k ok d'⌝ -∗ tcpEnd tcpG c s st -∗
        tcpDir tcpG c s d' ={∅,E}=∗ Φ (PairV (#(BitVec.ofNat 64 k)) (#ok))) -∗
    WP (ExternalOp tcpExt.name "Write" (Val (PairV (#(endId c s)) (#bs)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "Write" (PairV (#(endId c s)) (#bs)) (by simp) c s s
    (fun st d e' st' d' => st' = st ∧ ∃ k ok, WriteOutcome st d bs k ok d' ∧
      e' = Val (PairV (#(BitVec.ofNat 64 k)) (#ok)))
    ?_ ?_ ?_ ?_ a Φ $$ Hat
  · intro h σ g e' h' σ' g' hb hst
    obtain ⟨rfl, e0, bs0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, k, ok, d', hcn, hout, rfl, rfl⟩, rfl⟩ := hst
    obtain ⟨h1, h2⟩ := val.PairV.inj hv
    have he : endId c s = e0 := go.intoVal_inj h1
    obtain rfl : bs = bs0 := go.intoVal_inj h2
    obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
    exact ⟨rfl, rfl, cn, cn.endSt s, d', hcn, ⟨rfl, k, ok, hout, rfl⟩, by rw [setEnd_endSt_self]⟩
  · intro h σ g cn hb hcn
    obtain ⟨k, ok, d', hw⟩ := writeOutcome_total (cn.endSt s) (cn.out s) bs
    exact ⟨_, _, rfl, endId c s, bs, c, s, rfl, ⟨hb, rfl⟩, ⟨cn, k, ok, d', hcn, hw, rfl, rfl⟩, rfl⟩
  · rintro st d st' d' ⟨-, k, ok, -, he⟩
    cases he
  · rintro st d e' st' d' ⟨-, k, ok, -, rfl⟩
    exact .inr ⟨_, rfl⟩
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨rfl, k, ok, Hw, Hv⟩ := Hout
    cases Hv
    iapply Hk $$ %k %ok %d' %Hw Hend Hdir

/-- D3. `Close` of the end `s` of `c` (`CloseOutcome`). -/
theorem wp_tcp_Close (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c s d ∗
      ∀ ok st' d', ⌜CloseOutcome st d ok st' d'⌝ -∗ tcpEnd tcpG c s st' -∗
        tcpDir tcpG c s d' ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name "Close" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "Close" (#(endId c s)) (by simp) c s s
    (fun st d e' st' d' => ∃ ok, CloseOutcome st d ok st' d' ∧ e' = Val (#ok))
    ?_ ?_ ?_ ?_ a Φ $$ Hat
  · intro h σ g e' h' σ' g' hb hst
    obtain ⟨rfl, e0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, ok, st', d', hcn, hout, rfl, rfl⟩, rfl⟩ := hst
    have he : endId c s = e0 := go.intoVal_inj hv
    obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
    exact ⟨rfl, rfl, cn, st', d', hcn, ⟨ok, hout, rfl⟩, rfl⟩
  · intro h σ g cn hb hcn
    obtain ⟨ok, st', d', hc⟩ := closeOutcome_total (cn.endSt s) (cn.out s)
    exact ⟨_, _, rfl, endId c s, c, s, rfl, ⟨hb, rfl⟩, ⟨cn, ok, st', d', hcn, hc, rfl, rfl⟩, rfl⟩
  · rintro st d st' d' ⟨ok, -, he⟩
    cases he
  · rintro st d e' st' d' ⟨ok, -, rfl⟩
    exact .inr ⟨_, rfl⟩
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨ok, Hc, Hv⟩ := Hout
    cases Hv
    iapply Hk $$ %ok %st' %d' %Hc Hend Hdir

/-- D4. `CloseWrite` of the end `s` of `c` (`CloseWriteOutcome`). -/
theorem wp_tcp_CloseWrite (c : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st d, tcpEnd tcpG c s st ∗ tcpDir tcpG c s d ∗
      ∀ ok d', ⌜CloseWriteOutcome st d ok d'⌝ -∗ tcpEnd tcpG c s st -∗
        tcpDir tcpG c s d' ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name "CloseWrite" (Val (#(endId c s)))) @ sk; E {{ Φ }} := by
  iintro #Hat HAU
  iapply wp_tcp_endOp "CloseWrite" (#(endId c s)) (by simp) c s s
    (fun st d e' st' d' => st' = st ∧ ∃ ok, CloseWriteOutcome st d ok d' ∧ e' = Val (#ok))
    ?_ ?_ ?_ ?_ a Φ $$ Hat
  · intro h σ g e' h' σ' g' hb hst
    obtain ⟨rfl, e0, c0, s0, hv, ⟨hb0, he0⟩, ⟨cn, ok, d', hcn, hout, rfl, rfl⟩, rfl⟩ := hst
    have he : endId c s = e0 := go.intoVal_inj hv
    obtain ⟨rfl, rfl⟩ := endId_inj hb hb0 (he.trans he0)
    exact ⟨rfl, rfl, cn, cn.endSt s, d', hcn, ⟨rfl, ok, hout, rfl⟩, by rw [setEnd_endSt_self]⟩
  · intro h σ g cn hb hcn
    obtain ⟨ok, d', hc⟩ := closeWriteOutcome_total (cn.endSt s) (cn.out s)
    exact ⟨_, _, rfl, endId c s, c, s, rfl, ⟨hb, rfl⟩, ⟨cn, ok, d', hcn, hc, rfl, rfl⟩, rfl⟩
  · rintro st d st' d' ⟨-, ok, -, he⟩
    cases he
  · rintro st d e' st' d' ⟨-, ok, -, rfl⟩
    exact .inr ⟨_, rfl⟩
  · imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %w %st' %d' %Hout Hend Hdir
    obtain ⟨rfl, ok, Hc, Hv⟩ := Hout
    cases Hv
    iapply Hk $$ %ok %d' %Hc Hend Hdir

/-- D5. `SetDeadline` of the deadlines of kind `kind` of the end `s` of `c`, to the time whose
words are `wall` and `ext` (`DeadlineOutcome`; set unless the time is zero). -/
theorem wp_tcp_SetDeadline (c : Nat) (s : Bool) (a : GoString) (kind wall ext : w64)
    (Φ : val → IProp GF) :
    tcpConnAt tcpG c a -∗
    (|={E,∅}=> ∃ st, tcpEnd tcpG c s st ∗
      ∀ ok st', ⌜DeadlineOutcome st kind (!timeIsZero wall ext) ok st'⌝ -∗ tcpEnd tcpG c s st'
        ={∅,E}=∗ Φ (#ok)) -∗
    WP (ExternalOp tcpExt.name "SetDeadline"
      (Val (PairV (#(endId c s)) (PairV (#kind) (PairV (#wall) (#ext)))))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iintro #Hat HAU
  ihave #Hat' := Hat
  unfold tcpConnAt
  icases Hat' with ⟨%γ, #Hγ, %Hγa⟩
  iapply wp_extStep "SetDeadline" _ Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  icases tcpCtx_lookup _ g c γ $$ Hg Hγ with ⟨%Hcn, Hg⟩
  obtain ⟨cn0, hcn0⟩ := Hcn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    obtain ⟨ok, st', hd⟩ := deadlineOutcome_total (cn0.endSt s) kind (!timeIsZero wall ext)
    exact ⟨_, h, σ, _, rfl, endId c s, kind, wall, ext, c, s, rfl, ⟨Hγa.2, rfl⟩,
      ⟨cn0, ok, st', hcn0, hd, rfl, rfl⟩, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, e0, kind0, wall0, ext0, c0, s0, hv, ⟨hb0, he0⟩,
    ⟨cn, ok, st', hcn, hout, rfl, rfl⟩, rfl⟩ := Hst
  obtain ⟨h1, h2⟩ := val.PairV.inj hv
  obtain ⟨h2, h3⟩ := val.PairV.inj h2
  obtain ⟨h3, h4⟩ := val.PairV.inj h3
  have he : endId c s = e0 := go.intoVal_inj h1
  obtain rfl : kind = kind0 := go.intoVal_inj h2
  obtain rfl : wall = wall0 := go.intoVal_inj h3
  obtain rfl : ext = ext0 := go.intoVal_inj h4
  obtain ⟨rfl, rfl⟩ := endId_inj Hγa.2 hb0 (he.trans he0)
  imod Hclose
  imod HAU with ⟨%st, Hend, Hk⟩
  icases tcpCtx_acc _ g c γ $$ Hg Hγ with ⟨%cn1, %hcn1, Hcc, Hgclose⟩
  rw [hcn] at hcn1
  cases hcn1
  icases connCtx_acc γ cn s s $$ Hcc with ⟨%Haddr, Hv, Hq, Hcclose⟩
  icases tcpEnd_open _ c s st γ $$ Hγ Hend with Hv'
  icases ghostVar_agree $$ Hv' Hv with %Hst
  subst Hst
  imod ghostVar_update_halves st' $$ Hv' Hv with ⟨Hv', Hv⟩
  imod Hk $$ %ok %st' %hout [Hv'] with HΦ
  · iapply tcpEnd_intro $$ Hγ Hv'
  imodintro
  iframe Hheap Hl
  isplitr [HΦ]
  · iapply (tcp_global_ctx_eq _).mpr
    have hset : cn.setEnd s st' = (cn.setEnd s st').setOut s (cn.out s) := by
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

theorem lisAddrs_insert (m : GMap w64 (GoString × Bool)) (l : w64) (x : GoString × Bool) :
    lisAddrs (m.insert l x) = (lisAddrs m).insert l x.1 := by
  unfold lisAddrs
  apply GMap.ext; intro k
  simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
  split <;> simp_all

theorem lisAddrs_lookup (m : GMap w64 (GoString × Bool)) (l : w64) :
    (lisAddrs m).lookup l = (m.lookup l).map Prod.fst := by
  unfold lisAddrs; rw [GMap.lookup_fmap]

/-- `Listen` at `a`, an address of this node's host in the plan: a failure, or a new open
listener (and its address, persistent). -/
theorem wp_tcp_Listen (a : GoString) (Φ : val → IProp GF) :
    tcpPlan tcpG a (tcpL (L := L)).host -∗
    (Φ (PairV (#(W64 0)) (#false)) ∧ ∀ l : w64, tcpLis (tcpL (L := L)) l a true -∗
      tcpLisAt (tcpL (L := L)) l a -∗ Φ (PairV (#l) (#true))) -∗
    WP (ExternalOp tcpExt.name "Listen" (Val (#a))) @ sk; E {{ Φ }} := by
  letI := (tcpL (L := L)).allG
  iintro #Hp HΦ
  iapply wp_extStep "Listen" (#a) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_global_ctx_eq g).mp $$ Hg with Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  icases tcpCtx_plan _ g a _ $$ Hg Hp with %Hpa
  unfold tcpLocalCtx
  icases Hl with ⟨%Hhost, Hlis, Hat⟩
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
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨-, l, -, hl, rfl, rfl⟩
  · icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hheap
    isplitl [Hlis Hat]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx; iframe Hlis Hat; ipureintro; exact Hhost
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iexact HΦ
  · have hla : (lisAddrs σ.lis).lookup l = none := by rw [lisAddrs_lookup, hl]; rfl
    imod ghost_map_insert l (a, true) hl $$ Hlis with ⟨Hlis, Hel⟩
    imod ghost_map_insert_persist l a hla $$ Hat with ⟨Hat, #Hla⟩
    icases HΦ with ⟨-, HΦ⟩
    imodintro
    iframe Hheap
    isplitl [Hlis Hat]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx
      simp only
      rw [lisAddrs_insert]
      iframe Hlis Hat; ipureintro; exact Hhost
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iapply HΦ $$ [Hel]
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

/-- `LisClose` of the listener `l` at `a`, by a logically atomic update over its state: closed; the
result is whether it was open. -/
theorem wp_tcp_LisClose (l : w64) (a : GoString) (Φ : val → IProp GF) :
    tcpLisAt (tcpL (L := L)) l a -∗
    (|={E,∅}=> ∃ o, tcpLis (tcpL (L := L)) l a o ∗
      (tcpLis (tcpL (L := L)) l a false ={∅,E}=∗ Φ (#o))) -∗
    WP (ExternalOp tcpExt.name "LisClose" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (tcpL (L := L)).allG
  iintro #Hla HAU
  iapply wp_extStep "LisClose" (#l) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  imod HAU with ⟨%o, Hel, Hk⟩
  ihave %Hll := tcpLocal_lookup _ σ l a o $$ Hl Hel
  unfold tcpLocalCtx tcpLis
  icases Hl with ⟨%Hhost, Hlis, Hat⟩
  iapply fupd_mask_intro (by simp)
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
    imod Hk $$ Hel with HΦ
    imodintro
    iframe Hheap Hg
    isplitl [Hlis Hat]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx; iframe Hlis Hat; ipureintro; exact Hhost
    iapply wp_value'
    iexact HΦ
  · simp only [↓reduceIte] at Hcase
    obtain ⟨rfl, rfl⟩ := Hcase
    imod ghost_map_update (a, false) $$ Hlis Hel with ⟨Hlis, Hel⟩
    imod Hk $$ Hel with HΦ
    have hsame : lisAddrs (σ.lis.insert l (a, false)) = lisAddrs σ.lis := by
      rw [lisAddrs_insert]
      apply GMap.ext; intro k
      simp only [GMap.lookup_insert_eq_iff, lisAddrs_lookup]
      split
      · subst_vars; rw [Hll]; rfl
      · rfl
    imodintro
    iframe Hheap Hg
    isplitl [Hlis Hat]
    · iapply (tcp_local_ctx_eq _).mpr; unfold tcpLocalCtx
      simp only
      rw [hsame]
      iframe Hlis Hat; ipureintro; exact Hhost
    iapply wp_value'
    iexact HΦ



/-- The resources of a new connection's end `s`: its state, fresh, and the direction from it, open
and empty. -/
def tcpFresh (hG : TcpGS GF) (c : Nat) (s : Bool) : IProp GF :=
  iprop(tcpEnd hG c s TcpEnd.fresh ∗ tcpDir hG c s TcpDir.fresh)

theorem tcpFresh_intro (hG : TcpGS GF) (c : Nat) (s : Bool) (γ : ConnNames) (gv gq gt : GName)
    (hv : γ.v s = gv) (hq : γ.q s = gq) (ht : γ.tk s = gt) :
    tcpNames hG c γ -∗ @ghostVar GF hG.allG _ _ gv (1 : Qp).half TcpEnd.fresh -∗
      @ghostVar GF hG.allG _ _ gq (1 : Qp).half TcpDir.fresh -∗ @token GF hG.allG gt -∗
      tcpFresh hG c s := by
  letI := hG.allG
  subst hv hq ht
  unfold tcpFresh tcpEnd tcpDir
  iintro #Hγ Hv Hq Ht
  isplitl [Hv]
  · iexists γ; iframe Hγ Hv
  · iexists γ; iframe Hγ Hq Ht

theorem connCtx_fresh_intro (hG : TcpGS GF) (a : GoString) (γ : ConnNames)
    (gv0 gv1 gq0 gq1 : GName) (ha : γ.addr = a) (hv0 : γ.v false = gv0) (hv1 : γ.v true = gv1)
    (hq0 : γ.q false = gq0) (hq1 : γ.q true = gq1) :
    @ghostVar GF hG.allG _ _ gv0 (1 : Qp).half TcpEnd.fresh -∗
      @ghostVar GF hG.allG _ _ gv1 (1 : Qp).half TcpEnd.fresh -∗
      @ghostVar GF hG.allG _ _ gq0 (1 : Qp).half TcpDir.fresh -∗
      @ghostVar GF hG.allG _ _ gq1 (1 : Qp).half TcpDir.fresh -∗
      @connCtx GF hG.allG γ (TcpConn.fresh a) := by
  letI := hG.allG
  subst hv0 hv1 hq0 hq1
  unfold connCtx
  simp only [TcpConn.fresh, TcpConn.endSt, TcpConn.out]
  iintro Hv0 Hv1 Hq0 Hq1
  iframe Hv0 Hv1 Hq0 Hq1
  ipureintro; simp [TcpConn.fresh, ha]

/-- D8. `Dial` of `a`, an address of the plan: a failure, or a new connection `c` to `a`, pending at
`a` (`tcpPend`, by a logically atomic update), with both ends' resources. -/
theorem wp_tcp_Dial (a h : GoString) (Φ : val → IProp GF) :
    tcpPlan tcpG a h -∗
    (Φ (PairV (#(W64 0)) (#false)) ∧
      |={E,∅}=> ∃ S, tcpPend tcpG a S ∗
        ∀ c, ⌜c ∉ S⌝ -∗ tcpPend tcpG a (S ∪ {[c]}) -∗ tcpConnAt tcpG c a -∗
          tcpFresh tcpG c false -∗ tcpFresh tcpG c true ={∅,E}=∗
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
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨c, -, hc, hb, rfl, rfl⟩
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
    imod ghostVar_alloc_halves TcpEnd.fresh with ⟨%γv0, Hv0, Hv0'⟩
    imod ghostVar_alloc_halves TcpEnd.fresh with ⟨%γv1, Hv1, Hv1'⟩
    imod ghostVar_alloc_halves TcpDir.fresh with ⟨%γq0, Hq0, Hq0'⟩
    imod ghostVar_alloc_halves TcpDir.fresh with ⟨%γq1, Hq1, Hq1'⟩
    imod token_alloc (GF := GF) with ⟨%γt0, Ht0⟩
    imod token_alloc (GF := GF) with ⟨%γt1, Ht1⟩
    let γ : ConnNames := ⟨a, γv0, γv1, γq0, γq1, γt0, γt1⟩
    imod ghost_map_insert_persist c γ hnm $$ Hn with ⟨Hn, #Hγ⟩
    imod ghost_map_update (S ∪ {[c]}) $$ Hpm Hpend with ⟨Hpm, Hpend⟩
    have Hat : 2 * c + 1 < 2 ^ 64 := hb
    imod Hk $$ %c %hcS [Hpend] [] [Hv0 Hq0 Ht0] [Hv1 Hq1 Ht1] with HΦ
    · iexact Hpend
    · unfold tcpConnAt tcpNames; iexists γ; iframe Hγ; ipureintro; exact ⟨rfl, Hat⟩
    · iapply tcpFresh_intro _ c false γ γv0 γq0 γt0 rfl rfl rfl $$ [] Hv0 Hq0 Ht0
      unfold tcpNames; iexact Hγ
    · iapply tcpFresh_intro _ c true γ γv1 γq1 γt1 rfl rfl rfl $$ [] Hv1 Hq1 Ht1
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
        iapply connCtx_fresh_intro _ a γ γv0 γv1 γq0 γq1 rfl rfl rfl rfl rfl
          $$ Hv0' Hv1' Hq0' Hq1'
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

/-- `Accept` of the listener `l` at `a`, by a logically atomic update over its state and the
address's pending set: a failure (both unchanged); or, only if the listener is open, a connection
`c` pending at `a`, now accepted (taken out of the pending set). The update is opened only at the
step that decides (the accept may first wait). -/
theorem wp_tcp_Accept (l : w64) (a : GoString) (Φ : val → IProp GF) :
    tcpLisAt (tcpL (L := L)) l a -∗
    (|={E,∅}=> ∃ o S, tcpLis (tcpL (L := L)) l a o ∗ tcpPend tcpG a S ∗
      ((tcpLis (tcpL (L := L)) l a o -∗ tcpPend tcpG a S ={∅,E}=∗
          Φ (PairV (#(W64 0)) (#false))) ∧
        (⌜o = true⌝ -∗ ∀ c, ⌜c ∈ S⌝ -∗ tcpLis (tcpL (L := L)) l a o -∗
          tcpPend tcpG a (S \ {[c]}) -∗ tcpConnAt tcpG c a ={∅,E}=∗
          Φ (PairV (#(endId c true)) (#true))))) -∗
    WP (ExternalOp tcpExt.name "Accept" (Val (#l))) @ sk; E {{ Φ }} := by
  letI := (tcpG (G := G)).allG
  iloeb as IH
  iintro #Hla HAU
  iapply wp_extStep "Accept" (#l) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (tcp_local_ctx_eq σ).mp $$ Hl with Hl
  ihave %Hll := tcpLisAt_lookup _ σ l a $$ Hl Hla
  obtain ⟨o, Hll⟩ := Hll
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
  rcases Hcase with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨ho, c, cn, hcn, haddr, hacc, hb, rfl, rfl⟩
  · -- a failure
    imod HAU with ⟨%o', %S, Hel, Hpend, HΦ⟩
    icases HΦ with ⟨HΦ, -⟩
    imod HΦ $$ Hel Hpend with HΦ
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iexact HΦ
  · -- it waits
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (tcp_global_ctx_eq _).mpr; iexact Hg
    iapply IH $$ Hla HAU
  · -- the connection `c`
    imod HAU with ⟨%o', %S, Hel, Hpend, HΦ⟩
    icases tcpLocal_lookup _ _ l a o' $$ Hl Hel with %Hll'
    rw [Hll] at Hll'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj Hll')
    icases HΦ with ⟨-, Hk⟩
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
    imod Hk $$ %ho %c %hcS Hel [Hpend] [] with HΦ
    · iexact Hpend
    · unfold tcpConnAt
      iexists γ
      unfold tcpNames
      iframe Hn'
      ipureintro
      exact ⟨Haddr.trans haddr, hb⟩
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (tcp_local_ctx_eq _).mpr; iexact Hl
    isplitr [HΦ]
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
    iexact HΦ

end lifting

end Tcp
end Perennial
