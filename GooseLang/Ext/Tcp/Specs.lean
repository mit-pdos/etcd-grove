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
  icases BigSepM.bigSepM_insert_acc hcn $$ Hconns with ⟨⟨%γ', %Hγ', Hcc⟩, Hclose⟩
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
    iframe Hcc'
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

end lifting

end Tcp
end Perennial
