/-
**restart3's peer handler swap: its ghost state** (restart3 C3, 2026-11-15; `notes/restart3-handoff.md`,
"C3 plan"; D-R3-4). Lean-first (no Rocq counterpart). No trusted text: what `raftSwap.ServeHTTP` and
`raftSwap.set` need of each other, as ghost state over `http.Serve`'s slot tokens.

`http.Serve(l, sw)` lends each of its request goroutines one of `httpProcSlots` copies of the resource
`sw`'s handler contract names (`http.handlerOk ... Rs sw`). The members' raft handlers each lend
their own incarnation's `srvServeRes γn τ` (`EtcdServer.RaftHandler.spec`), whose transport `τ`
changes at the restart. So the swap's `Rs` is a **slot token** (`swTok`: slot `j` idle), the same
for every incarnation, which a request trades for a copy of the current incarnation's resource and
gets back when the incarnation's handler returns.

**The ghost state.**
- The slots' states (`γS.g`, a ghost map over `j < httpProcSlots`): `0` idle, `c + 1` busy with
  the copy of the incarnation `c`. An idle slot's token is `j ↦ 0` (full), a busy slot's receipt
  `j ↦ c + 1`.
- The current incarnation `c` (`γS.cur`, a ghost variable whose halves the global invariant and
  the mutex's invariant hold).
- Each incarnation `c` has its own invariant (`swIncInv γn c b τ`), holding, for each slot `j`,
  either a copy of its resource with the token `B_j` (`swTokB b j`), or the token `A_j` (`swTokA c j`,
  a claim on that copy).
- The global invariant (`swGInv`) holds the slots' authority and, for each slot `j`, the current
  incarnation's claim `A_j` unless `j` is busy with the current incarnation (`swObl`).

**The moves.**
- *Enter* (`sw_enter`, under the mutex, which names the current incarnation): an idle slot's token
  becomes the receipt; the global invariant's claim `A_j` is traded in the incarnation's invariant
  for its copy and `B_j`.
- *Exit* (`sw_exit`, when the incarnation's handler returns, with no lock): if the incarnation is
  still current, the copy and `B_j` go back to its invariant, which gives back `A_j`, which the global
  invariant keeps for the now idle slot; if not, the global invariant already holds the current
  incarnation's `A_j` for the slot (a busy slot of another incarnation keeps it), and the copy is
  dropped (Scope §2.2 (i)-(ii): the stopped incarnation's handler ran with its own copy, which no
  one else needs). The slot token comes back either way.
- *Install* (`sw_install`, `set`, under the mutex): a new incarnation with `httpProcSlots` fresh
  copies (`BuildServer.specRestart`'s, `memberPeerServeRes ... false`) becomes current; its invariant
  takes the copies, the global invariant its claims, the old incarnation's claims dropped.

No freshness of an incarnation's names is needed: every exclusivity argument is between a thread's
token and one incarnation's invariant.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.net.http.Boundary
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure

/-- **A map of the slots `j < n`, each at `v`.** -/
def rmap {V : Type} (v : V) : Nat → GMap Nat V
  | 0 => ∅
  | n + 1 => (rmap v n).insert n v

theorem rmap_lookup_ge {V : Type} (v : V) : ∀ (n k : Nat), n ≤ k → (rmap v n).lookup k = none
  | 0, _, _ => rfl
  | n + 1, k, h => by
    simp only [rmap]
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact rmap_lookup_ge v n k (by omega)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The swap's ghost names**: the slots' states and the current incarnation. -/
structure SwNames where
  g : GName
  cur : GName
  /-- the slot count (`http.httpProcSlots`; a field, so that no proof here sees a numeral's list) -/
  n : Nat


/-- **Incarnation `c`'s claim on its copy for slot `j`** (exclusive). -/
def swTokA (c : GName) (j : Nat) : IProp GF := ghostMapElem (K := Nat) (V := Bool) c j (.own 1) true

/-- **The token of incarnation `c`'s copy for slot `j` being out** (exclusive). -/
def swTokB (b : GName) (j : Nat) : IProp GF := ghostMapElem (K := Nat) (V := Bool) b j (.own 1) true

instance swTokA_timeless (c : GName) (j : Nat) : Timeless (swTokA (GF := GF) c j) := by
  unfold swTokA ghostMapElem; infer_instance

instance swTokB_timeless (b : GName) (j : Nat) : Timeless (swTokB (GF := GF) b j) := by
  unfold swTokB ghostMapElem; infer_instance

theorem swTokA_excl (c : GName) (j : Nat) : swTokA (GF := GF) c j ∗ swTokA c j ⊢ False := by
  iintro ⟨H1, H2⟩
  unfold swTokA
  ihave %H := ghostMapElem_ne (GF := GF) (K := Nat) (V := Bool) c j j (.own 1) true true $$ H1 H2
  exact absurd rfl H

theorem swTokB_excl (b : GName) (j : Nat) : swTokB (GF := GF) b j ∗ swTokB b j ⊢ False := by
  iintro ⟨H1, H2⟩
  unfold swTokB
  ihave %H := ghostMapElem_ne (GF := GF) (K := Nat) (V := Bool) b j j (.own 1) true true $$ H1 H2
  exact absurd rfl H

/-- **What the global invariant holds for slot `j` in state `v`**, the incarnation `c` current: `c`'s
claim, unless `j` is busy with `c`. -/
def swObl (c : GName) (j : Nat) (v : Option Nat) : IProp GF :=
  if v = some (c + 1) then iprop(emp) else swTokA c j

instance swObl_timeless (c : GName) (j : Nat) (v : Option Nat) : Timeless (swObl (GF := GF) c j v) := by
  unfold swObl; split <;> infer_instance

/-- The namespaces of the incarnations' invariants and of the global one. -/
def swIncN : Namespace := nroot .@ "restart3_swinc"
def swGN : Namespace := nroot .@ "restart3_swg"

/-- **Incarnation `c`'s invariant** (see the file header), at the transport `τ` of the network `γn`. -/
def swIncInv (γn : NetNames GF) (n : Nat) (c b : GName) (τ : SrvTr GF) : IProp GF :=
  inv swIncN iprop([∗list] j ∈ List.range n, (srvServeRes γn τ ∗ swTokB b j) ∨ swTokA c j)

instance swIncInv_persistent (γn : NetNames GF) (n : Nat) (c b : GName) (τ : SrvTr GF) :
    Persistent (swIncInv γn n c b τ) := by
  unfold swIncInv; infer_instance

/-- **The swap's global invariant** (see the file header). -/
def swGInv (γS : SwNames) : IProp GF :=
  inv swGN iprop(∃ (c : GName) (m : GMap Nat Nat),
    dghostVar γS.cur (.own (1 : Qp).half) c ∗ ghostMapAuth γS.g 1 m ∗
    [∗list] j ∈ List.range γS.n, swObl c j (m.lookup j))

instance swGInv_persistent (γS : SwNames) : Persistent (swGInv (GF := GF) γS) := by
  unfold swGInv; infer_instance

/-- **A slot token** (`http.Serve`'s resource for the swap's handler): an idle slot. -/
def swTok (γS : SwNames) : IProp GF :=
  iprop(∃ j : Nat, ⌜j < γS.n⌝ ∗ ghostMapElem (K := Nat) (V := Nat) γS.g j (.own 1) 0)

/-- **The current incarnation, as the mutex's invariant holds it**: the current incarnation's half and
its invariant. -/
def swCur (γS : SwNames) (γn : NetNames GF) (c b : GName) (τ : SrvTr GF) : IProp GF :=
  iprop(dghostVar γS.cur (.own (1 : Qp).half) c ∗ swIncInv γn γS.n c b τ)

/-- **A busy slot's receipt**: slot `j` busy with the incarnation `c`, its token `B_j` out. -/
def swRcpt (γS : SwNames) (γn : NetNames GF) (c b : GName) (τ : SrvTr GF) : IProp GF :=
  iprop(∃ j : Nat, ⌜j < γS.n⌝ ∗ ghostMapElem (K := Nat) (V := Nat) γS.g j (.own 1) (c + 1) ∗
    swTokB b j ∗ swIncInv γn γS.n c b τ)

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem swN_disj : (↑swIncN : CoPset) ⊆ ⊤ \ ↑swGN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- A big separating conjunction of one proposition depends only on the list's length. -/
theorem bigSepL_const_len {A B : Type} (P : IProp GF) :
    ∀ (l₁ : List A) (l₂ : List B), l₁.length = l₂.length →
      ([∗list] _x ∈ l₁, P) ⊢ [∗list] _y ∈ l₂, P
  | [], [], _ => .rfl
  | _ :: xs, _ :: ys, h => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply bigSepL_const_len P xs ys (by simpa using h)
    iexact H2
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The slots `j < n` allocated, with `rmap` (internal: its statement names `rmap`, which recurses on
`n`; `ghostMap_alloc_range` hides it). -/
theorem ghostMap_alloc_rmap {V : Type} [Pos.Countable V] (v : V) (n : Nat) :
    ⊢ |==> ∃ γ, ghostMapAuth (GF := GF) γ 1 (rmap v n) ∗
      [∗list] j ∈ List.range n, ghostMapElem (K := Nat) γ j (.own 1) v := by
  induction n with
  | zero =>
    imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := V) with ⟨%γ, H⟩
    imodintro
    iexists γ
    rw [show rmap v 0 = ∅ from rfl]
    isplitl [H]
    · iexact H
    simp only [List.range_zero]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | succ n ih =>
    imod ih with ⟨%γ, Ha, Hl⟩
    imod ghost_map_insert (GF := GF) n v (rmap_lookup_ge v n n (Nat.le_refl n)) $$ Ha with ⟨Ha, Hn⟩
    imodintro
    iexists γ
    rw [show rmap v (n + 1) = (rmap v n).insert n v from rfl]
    isplitl [Ha]
    · iexact Ha
    rw [List.range_succ]
    iapply BigSepL.bigSepL_snoc.2
    iframe Hl
    iexact Hn

theorem rmap_lookup_lt {V : Type} (v : V) : ∀ (n j : Nat), j < n → (rmap v n).lookup j = some v
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    simp only [rmap]
    by_cases e : n = j
    · subst e; exact GMap.lookup_insert _ _ _
    · rw [GMap.lookup_insert_ne _ _ e]; exact rmap_lookup_lt v n j (by omega)

/-- **The slots `j < n`, allocated** at the value `v`: an authority over a map with each `j < n` at `v`,
and each slot's element. -/
theorem ghostMap_alloc_range {V : Type} [Pos.Countable V] (v : V) (n : Nat) :
    ⊢ |==> ∃ γ, ∃ m : GMap Nat V, ghostMapAuth (GF := GF) γ 1 m ∗ ⌜∀ j, j < n → m.lookup j = some v⌝ ∗
      [∗list] j ∈ List.range n, ghostMapElem (K := Nat) γ j (.own 1) v := by
  imod ghostMap_alloc_rmap (GF := GF) v n with ⟨%γ, Ha, Hl⟩
  imodintro
  iexists γ, rmap v n
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro; exact rmap_lookup_lt v n
  iexact Hl

/-- The obligations of idle slots: the claims. -/
theorem swObl_init (c : GName) (n : Nat) (m : GMap Nat Nat) (hm : ∀ j, j < n → m.lookup j = some 0) :
    ([∗list] j ∈ List.range n, swTokA (GF := GF) c j) ⊢
      [∗list] j ∈ List.range n, swObl c j (m.lookup j) := by
  apply BigSepL.bigSepL_mono
  intro k j hk
  have hj : j < n := List.mem_range.1 (List.mem_of_getElem? hk)
  unfold swObl
  rw [hm j hj, if_neg (by simp)]

/-- **A new incarnation** (see the file header): from `n` copies of its resource, its invariant and
its claims. -/
theorem sw_newInc (γn : NetNames GF) (τ : SrvTr GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), srvServeRes (GF := GF) γn τ) ⊢
      |={⊤}=> ∃ c b, swIncInv γn n c b τ ∗ [∗list] j ∈ List.range n, swTokA c j := by
  iintro Hcp
  imod ghostMap_alloc_range (GF := GF) true n with ⟨%c, %mA, -, -, HA⟩
  imod ghostMap_alloc_range (GF := GF) true n with ⟨%b, %mB, -, -, HB⟩
  ihave Hcp' : [∗list] _j ∈ List.range n, srvServeRes (GF := GF) γn τ $$ [Hcp]
  · iapply bigSepL_const_len _ (List.replicate n ()) (List.range n)
      (by rw [List.length_replicate, List.length_range])
    iexact Hcp
  imod inv_alloc swIncN ⊤
    iprop([∗list] j ∈ List.range n, (srvServeRes γn τ ∗ swTokB b j) ∨ swTokA c j)
    $$ [Hcp' HB] with #Hinv
  · inext
    iapply BigSepL.bigSepL_mono (Φ := fun _ j => iprop(srvServeRes (GF := GF) γn τ ∗ swTokB b j))
    · intro _ _ _; exact or_intro_l
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hcp']
    · iexact Hcp'
    unfold swTokB
    iexact HB
  imodintro
  iexists c, b
  isplitr
  · unfold swIncInv; iexact Hinv
  unfold swTokA
  iexact HA

/-- **The swap's ghost state allocated** with its first incarnation (`newMember`), at `n` slots: the
global invariant, the mutex's view of the current incarnation, and `n` slot tokens. -/
theorem sw_alloc (γn : NetNames GF) (τ : SrvTr GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), srvServeRes (GF := GF) γn τ) ⊢
      |={⊤}=> ∃ (γS : SwNames) (c b : GName), ⌜γS.n = n⌝ ∗ swGInv γS ∗ swCur γS γn c b τ ∗
        [∗list] _x ∈ List.replicate n (), swTok γS := by
  iintro Hcp
  imod sw_newInc γn τ n $$ Hcp with ⟨%c, %b, #Hinc, HA⟩
  imod ghostMap_alloc_range (GF := GF) (0 : Nat) n with ⟨%g, %m0, Hg, %Hm0, Hel⟩
  imod dghostVar_alloc (GF := GF) c with ⟨%cur, Hcur⟩
  icases dghostVar_split (GF := GF) cur c (.own (1 : Qp).half) (.own (1 : Qp).half) $$
    [Hcur] with ⟨Hc1, Hc2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hcur
  imod inv_alloc swGN ⊤ iprop(∃ (c' : GName) (m : GMap Nat Nat),
      dghostVar cur (.own (1 : Qp).half) c' ∗ ghostMapAuth g 1 m ∗
      [∗list] j ∈ List.range n, swObl c' j (m.lookup j)) $$ [Hc1 Hg HA] with #HG
  · inext
    iexists c, m0
    iframe Hc1
    isplitl [Hg]
    · iexact Hg
    iapply (swObl_init c n m0 Hm0)
    iexact HA
  imodintro
  iexists ⟨g, cur, n⟩, c, b
  isplitr
  · ipureintro; rfl
  isplitr
  · unfold swGInv; iexact HG
  isplitl [Hc2]
  · unfold swCur; iframe Hc2; iexact Hinc
  iapply bigSepL_const_len _ (List.range n) (List.replicate n ())
    (by rw [List.length_replicate, List.length_range])
  iapply BigSepL.bigSepL_mono (Φ := fun _ j =>
    ghostMapElem (GF := GF) (K := Nat) (V := Nat) g j (.own 1) 0) $$ [Hel]
  · intro k j hk
    iintro H
    unfold swTok
    iexists j
    iframe H
    ipureintro
    exact List.mem_range.1 (List.mem_of_getElem? hk)
  iexact Hel

end laws

section moves
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem swObl_ne (c : GName) (j : Nat) (v : Option Nat) (h : v ≠ some (c + 1)) :
    swObl (GF := GF) c j v ⊢ swTokA c j := by
  unfold swObl; rw [if_neg h]

theorem swObl_tok (c : GName) (j : Nat) (v : Option Nat) :
    swTokA (GF := GF) c j ⊢ swObl c j v := by
  unfold swObl; split
  · exact Affine.affine
  · exact .rfl

theorem swObl_self (c : GName) (j : Nat) : ⊢ swObl (GF := GF) c j (some (c + 1)) := by
  unfold swObl; rw [if_pos rfl]; exact .rfl

theorem range_get {n j : Nat} (h : j < n) : (List.range n)[j]? = some j := List.getElem?_range h

theorem range_get_eq {n k y : Nat} (h : (List.range n)[k]? = some y) : y = k := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hlt, he⟩ := h
  rw [List.getElem_range] at he
  exact he.symm

/-- The other slots' obligations are kept by an update of slot `j`'s state. -/
theorem swObl_insert_ne (c : GName) (m : GMap Nat Nat) (j k w : Nat) (h : k ≠ j) :
    swObl (GF := GF) c k ((m.insert j w).lookup k) = swObl c k (m.lookup k) := by
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]

/-- The global invariant's obligations after an update of slot `j` to `w`, given slot `j`'s new one. -/
theorem swObl_update (n : Nat) (c : GName) (m : GMap Nat Nat) (j w : Nat) (hj : j < n) :
    ⊢ (∀ Ψ : Nat → Nat → IProp GF,
        □ (∀ k y, ⌜(List.range n)[k]? = some y⌝ → ⌜k ≠ j⌝ → swObl c y (m.lookup y) -∗ Ψ k y) -∗
        Ψ j j -∗ [∗list] k ↦ y ∈ List.range n, Ψ k y) -∗
      swObl c j (some w) -∗ [∗list] y ∈ List.range n, swObl c y ((m.insert j w).lookup y) := by
  iintro Hback Hj
  iapply Hback
  · iintro !> %k %y %hk %hne H
    have hy := range_get_eq hk
    subst hy
    rw [swObl_insert_ne c m j y w hne]
    iexact H
  · rw [GMap.lookup_insert]
    iexact Hj

/-- **Enter** (see the file header): under the mutex, which names the current incarnation `c`, an idle
slot's token for a copy of `c`'s resource and the slot's receipt. -/
theorem sw_enter (γS : SwNames) (γn : NetNames GF) (c b : GName) (τ : SrvTr GF) :
    swGInv γS ∗ swCur γS γn c b τ ∗ swTok γS ∗ £ 1 ⊢
      |={⊤}=> swCur γS γn c b τ ∗ srvServeRes γn τ ∗ swRcpt γS γn c b τ := by
  have Hd := swN_disj
  have Htop : (↑swIncN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  iintro ⟨#HG, Hcur, Htok, Hlc⟩
  iunfold swCur at Hcur
  icases Hcur with ⟨Hc, #Hinc⟩
  iunfold swTok at Htok
  icases Htok with ⟨%j, %hj, Hj⟩
  iunfold swGInv at HG
  iinv HG with >Hi Hclose
  icases Hi with ⟨%c', %m, Hc', Ha, Hobl⟩
  ihave %Hcc := dghostVar_agree (GF := GF) γS.cur c _ c' _ $$ Hc Hc'
  subst Hcc
  ihave %Hl := ghost_map_lookup (GF := GF) $$ Ha Hj
  imod ghost_map_update (GF := GF) (c + 1) $$ Ha Hj with ⟨Ha, Hj⟩
  icases BigSepL.bigSepL_lookup_acc_impl (range_get hj) $$ Hobl with ⟨Hoj, Hback⟩
  ihave HA := swObl_ne c j (m.lookup j) (by rw [Hl]; simp) $$ Hoj
  imod Hclose $$ [Hc' Ha Hback] with -
  · inext
    iexists c, m.insert j (c + 1)
    iframe Hc'
    isplitl [Ha]
    · iexact Ha
    iapply swObl_update γS.n c m j (c + 1) hj $$ Hback
    iapply swObl_self
  -- the incarnation's invariant: the claim traded for the copy and `B_j`
  iunfold swIncInv at Hinc
  imod (inv_acc Htop) $$ Hinc with ⟨Hi, Hclose⟩
  icases (BI.later_mono (BigSepL.bigSepL_mem_acc (List.mem_range.2 hj))) $$ Hi with ⟨Hs, Hw⟩
  icases Hs with (⟨Hcp, HB⟩ | HA')
  · imod HB
    imod lc_fupd_elim_later $$ Hlc Hcp with Hcp
    imod Hclose $$ [Hw HA] with -
    · inext
      iapply Hw
      iright
      iexact HA
    imodintro
    isplitl [Hc]
    · iunfold swCur; iframe Hc; iunfold swIncInv; iexact Hinc
    iframe Hcp
    iunfold swRcpt
    iexists j
    isplitr; · ipureintro; exact hj
    iframe Hj HB
    iunfold swIncInv; iexact Hinc
  · imod HA'
    iexfalso
    iapply swTokA_excl c j
    iframe

/-- **Exit** (see the file header): the receipt and the copy back for the slot token, whichever
incarnation is current. -/
theorem sw_exit (γS : SwNames) (γn : NetNames GF) (c b : GName) (τ : SrvTr GF) :
    swGInv γS ∗ swRcpt γS γn c b τ ∗ srvServeRes γn τ ⊢ |={⊤}=> swTok γS := by
  have Hd := swN_disj
  iintro ⟨#HG, Hr, Hcp⟩
  iunfold swRcpt at Hr
  icases Hr with ⟨%j, %hj, Hj, HB, #Hinc⟩
  iunfold swGInv at HG
  iinv HG with >Hi Hclose
  icases Hi with ⟨%c', %m, Hc', Ha, Hobl⟩
  ihave %Hl := ghost_map_lookup (GF := GF) $$ Ha Hj
  imod ghost_map_update (GF := GF) (0 : Nat) $$ Ha Hj with ⟨Ha, Hj⟩
  icases BigSepL.bigSepL_lookup_acc_impl (range_get hj) $$ Hobl with ⟨Hoj, Hback⟩
  ihave HA : |={⊤ \ ↑swGN}=> swTokA c' j $$ [Hoj HB Hcp]
  · by_cases hc : c' = c
    · subst hc
      iunfold swIncInv at Hinc
      have Hsub : (↑swIncN : CoPset) ⊆ ⊤ \ ↑swGN := Hd
      imod (inv_acc Hsub) $$ Hinc with ⟨Hi, Hclose2⟩
      icases (BI.later_mono (BigSepL.bigSepL_mem_acc (List.mem_range.2 hj))) $$ Hi with ⟨Hs, Hw⟩
      icases Hs with (⟨-, HB'⟩ | HA)
      · imod HB'
        iexfalso
        iapply swTokB_excl b j
        iframe
      · imod HA
        imod Hclose2 $$ [Hw Hcp HB] with -
        · inext
          iapply Hw
          ileft
          iframe
        imodintro
        iexact HA
    · imodintro
      iapply swObl_ne c' j (m.lookup j) (by rw [Hl]; intro h; apply hc; simp only [Option.some.injEq] at h; exact (Nat.add_right_cancel h).symm) $$ Hoj
  imod HA with HA
  imod Hclose $$ [Hc' Ha Hback HA] with -
  · inext
    iexists c', m.insert j 0
    iframe Hc'
    isplitl [Ha]
    · iexact Ha
    iapply swObl_update γS.n c' m j 0 hj $$ Hback
    iapply swObl_tok
    iexact HA
  imodintro
  iunfold swTok
  iexists j
  iframe Hj
  ipureintro
  exact hj

/-- The global invariant's obligations at a new current incarnation `c'`, from its claims. -/
theorem swObl_switch (n : Nat) (c c' : GName) (m : GMap Nat Nat) :
    ([∗list] j ∈ List.range n, swObl (GF := GF) c j (m.lookup j)) ∗
      ([∗list] j ∈ List.range n, swTokA c' j) ⊢
      [∗list] j ∈ List.range n, swObl c' j (m.lookup j) := by
  refine BigSepL.bigSepL_sep_eqv.2.trans (BigSepL.bigSepL_mono ?_)
  intro k j _
  exact BI.sep_elim_right.trans (swObl_tok c' j _)

/-- **Install** (see the file header): under the mutex, a new incarnation with `γS.n` copies of its
resource becomes current. -/
theorem sw_install (γS : SwNames) (γn : NetNames GF) (c b : GName) (τ τ' : SrvTr GF) :
    swGInv γS ∗ swCur γS γn c b τ ∗ ([∗list] _x ∈ List.replicate γS.n (), srvServeRes γn τ') ⊢
      |={⊤}=> ∃ c' b', swCur γS γn c' b' τ' := by
  iintro ⟨#HG, Hcur, Hcp⟩
  imod sw_newInc γn τ' γS.n $$ Hcp with ⟨%c', %b', #Hinc', HA⟩
  iunfold swCur at Hcur
  icases Hcur with ⟨Hc, -⟩
  iunfold swGInv at HG
  iinv HG with >Hi Hclose
  icases Hi with ⟨%c0, %m, Hc0, Ha, Hobl⟩
  imod dghostVar_update_halves (GF := GF) c' γS.cur c c0 $$ Hc Hc0 with ⟨Hc, Hc0⟩
  imod Hclose $$ [Hc0 Ha Hobl HA] with -
  · inext
    iexists c', m
    iframe Hc0
    isplitl [Ha]
    · iexact Ha
    iapply swObl_switch γS.n c0 c' m
    iframe
  imodintro
  iexists c', b'
  iunfold swCur
  iframe Hc
  iexact Hinc'

end moves

end etcd_restart
end EtcdGrove
end Perennial
