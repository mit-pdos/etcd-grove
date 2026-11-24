/-
**Deposit slots over the net library's protocols** (proved, not trusted): one slot per
connection, in which the connection's dialer deposits a resource `D` for the connection's acceptor
and from which it takes back the acceptor's answer (`notes/phase7-plan.md`, "S2 draft signatures",
§1.1, as amended in §0a). The generalization of `remote`'s slot
(`Net/Proof/.../examples/lib/remote/Defs.lean`: `slotOf`, `slotInv`, `slot_register`,
`slot_claim`, `slot_done`, `slot_take`) with what a retrying dialer needs: the acceptor may
**refuse** the connection instead of claiming (it then never claims, and the dialer takes `D` back),
and the dialer may **withdraw** `D` while no acceptor can have read enough of its bytes to claim.

The vocabulary (`[σ : NetSlotGS]`, the library's global ghost names, made once by
`depSlots_alloc`):

* `depSlotsCtx` (persistent): the slot map's invariant. It keeps, for every connection with a slot,
  its dialer's `connFresh cn false` (so a connection has at most one slot), and for every refused
  connection its acceptor's `connFresh cn true` (so a refused connection's slot is never claimed).
* `depSlotOf cn γ k` (persistent): the connection `cn` has the slot `γ`, with the key `k` (of any
  countable type, stored as its code: `depSlotOf_agree`).
* `depSlotInv cn γ ready D Φ` (persistent): the slot's invariant. `ready` is the set of the
  dialer's written prefixes after which an acceptor may claim (closed under extension,
  `SlotReady`), `D` the deposit, `Φ o` what the dialer gets for the acceptor's outcome `o : O`.
* `slotRunTok γ` (exclusive): the acceptor's share of a claimed slot, spent by `depSlot_answer`.
* `slotDone γ o` (persistent): the slot was answered `o`.
* `connRefused cn` (persistent): the acceptor of `cn` refused it (`conn_refuse`).

The laws (each at a mask containing `netSlotN`): `depSlots_alloc`, `depSlot_register` (the dialer,
with the `connFresh cn false` its `Dial` gave, and `D`), `depSlot_claim` (the acceptor, with its
`connFresh cn true` and a `ready` prefix of what the dialer wrote: `D` and `slotRunTok`),
`depSlot_answer`, `depSlot_take` (the dialer, with its token: `Φ o`), `conn_refuse` (the acceptor,
with its `connFresh cn true`), `depSlot_takeRefused` (the dialer, with its token and
`connRefused cn`: `D`), `depSlot_withdraw` (the dialer, with its token and its `sendTok` at a `W`
with `¬ ready W`, which it gives up: `D`).

**The states of a slot** (`depSlotBody`): registered (`D`, the outcome list `γ.d` empty and whole);
claimed (the acceptor's `connFresh cn true` and the claim's `ready` prefix, `slotClaimed`, with half
of `γ.d` at `[]` while the acceptor runs, or `γ.d` at `[o]` with `Φ o` or, once taken, the dialer's
token); withdrawn (the dialer's token, `γ.d` whole at `[]`, and why no claim can come: the
dialer's `sendTok` frozen at a `W` with `¬ ready W`, or `connRefused cn`).

Why a withdraw is sound: a claim needs `sentLb cn false W'` with `ready W'`; the frozen `sendTok`'s
half bounds every lower bound by `W` (`sendTok_sentLb_prefix`), so `W' <+: W` and `ready W` would
follow (`SlotReady.mono`). Why a refusal is: a claim and a refusal both spend the acceptor's one
`connFresh cn true` (`connFresh_excl`).
-/
module

public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace Net

/-! ## Ghost names, namespaces -/

/-- The library's global ghost names: the slot map and the refused connections. -/
class NetSlotGS where
  slots : GName
  refused : GName

/-- A slot's ghost names: its monotone list of outcomes (empty, or the one recorded) and the
dialer's token. -/
structure SlotNames where
  d : GName
  t : GName
deriving DecidableEq

instance SlotNames.countable : Pos.Countable SlotNames :=
  .ofInjective (fun γ : SlotNames => Pos.Countable.encode (γ.d, γ.t))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'; rfl)

/-- A key's code, as the slot map stores it. -/
@[instance_reducible] def posCountable : Pos.Countable Pos := .ofInjective id (fun _ _ h => h)

attribute [local instance] posCountable

/-- The library's namespace: every law's mask contains it. -/
def netSlotN : Namespace := nroot.@"netslot"
/-- The slot map's invariant. -/
def slotsN : Namespace := netSlotN.@"map"
/-- The invariant of the slot of the connection `cn`. -/
def depSlotN (cn : Nat) : Namespace := (netSlotN.@"slot").@cn

theorem depSlotN_sub (cn : Nat) : (↑(depSlotN cn) : CoPset) ⊆ ↑netSlotN :=
  fun p hp => nclose_subseteq _ "slot" p (nclose_subseteq _ cn p hp)

theorem slotsN_sub : (↑slotsN : CoPset) ⊆ ↑netSlotN :=
  fun p hp => nclose_subseteq _ "map" p hp

/-- The slot map's namespace, inside a mask with the slot's opened. -/
theorem slotsN_diff (E : CoPset) (cn : Nat) (hE : (↑netSlotN : CoPset) ⊆ E) :
    (↑slotsN : CoPset) ⊆ E \ ↑(depSlotN cn) := by
  intro p hp
  have h := ndot_sub_mask netSlotN "slot" "map" cn (by decide) p hp
  rw [LawfulSet.mem_diff] at h ⊢
  exact ⟨hE p (slotsN_sub p hp), h.2⟩

/-- **A dialer's prefixes after which an acceptor may claim** (closed under extension). -/
structure SlotReady (ready : List w8 → Prop) : Prop where
  mono : ∀ a b, ready a → a <+: b → ready b

/-! ## The vocabulary -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS] [σ : NetSlotGS]
variable {K O : Type} [Pos.Countable K] [Pos.Countable O]

/-- The slot map: every connection with a slot, with its dialer's fresh token; every refused
connection, with its acceptor's. -/
def slotsInv : IProp GF :=
  iprop(∃ (M : GMap Nat (SlotNames × Pos)) (Rf : GMap Nat Unit),
    ghostMapAuth σ.slots 1 M ∗ ([∗map] cn ↦ _v ∈ M, connFresh (Gg := Gg) cn false) ∗
    ghostMapAuth σ.refused 1 Rf ∗ [∗map] cn ↦ _u ∈ Rf, connFresh (Gg := Gg) cn true)

/-- The slot map's invariant (persistent). -/
def depSlotsCtx : IProp GF := inv slotsN (slotsInv (Gg := Gg))

/-- The connection `cn` has the slot `γ`, with the key `k` (persistent). -/
def depSlotOf (cn : Nat) (γ : SlotNames) (k : K) : IProp GF :=
  ghostMapElem σ.slots cn .discard (γ, Pos.Countable.encode k)

/-- The acceptor of `cn` refused it: it never claims a slot on it (persistent). -/
def connRefused (cn : Nat) : IProp GF := ghostMapElem σ.refused cn .discard ()

/-- A claim of the slot of `cn`: the acceptor's fresh token, and a `ready` prefix the dialer
wrote. -/
def slotClaimed (cn : Nat) (ready : List w8 → Prop) : IProp GF :=
  iprop(connFresh (Gg := Gg) cn true ∗ ∃ W, ⌜ready W⌝ ∗ sentLb (Gg := Gg) cn false W)

/-- The slot's states: registered; claimed (running, or answered `o` with `Φ o` or the dialer's
token); withdrawn (see the file header). -/
def depSlotBody (cn : Nat) (γ : SlotNames) (ready : List w8 → Prop) (D : IProp GF)
    (Φ : O → IProp GF) : IProp GF :=
  iprop((D ∗ monoListAuthOwn (A := O) γ.d 1 []) ∨
    (slotClaimed cn ready ∗
      (monoListAuthOwn (A := O) γ.d (1 : Qp).half [] ∨
        ∃ o : O, monoListAuthOwn γ.d 1 [o] ∗ (Φ o ∨ token γ.t))) ∨
    (token γ.t ∗ monoListAuthOwn (A := O) γ.d 1 [] ∗
      ((∃ (P : Proto GF) (W : List w8), ⌜¬ ready W⌝ ∗ sendTok (Gg := Gg) cn false P W) ∨
        connRefused cn)))

/-- **The slot's invariant** (persistent). -/
def depSlotInv (cn : Nat) (γ : SlotNames) (ready : List w8 → Prop) (D : IProp GF)
    (Φ : O → IProp GF) : IProp GF :=
  inv (depSlotN cn) (depSlotBody cn γ ready D Φ)

/-- The acceptor's share of a claimed slot (exclusive). -/
def slotRunTok (γ : SlotNames) : IProp GF := monoListAuthOwn (A := O) γ.d (1 : Qp).half []

/-- The slot `γ` was answered `o` (persistent). -/
def slotDone (γ : SlotNames) (o : O) : IProp GF := monoListLbOwn γ.d [o]

instance depSlotsCtx_persistent : Persistent (depSlotsCtx (Gg := Gg)) := by
  unfold depSlotsCtx; infer_instance
instance depSlotOf_persistent cn γ (k : K) : Persistent (depSlotOf (Gg := Gg) cn γ k) := by
  unfold depSlotOf; infer_instance
instance depSlotOf_timeless cn γ (k : K) : Timeless (depSlotOf (Gg := Gg) cn γ k) := by
  unfold depSlotOf; infer_instance
instance connRefused_persistent cn : Persistent (connRefused (Gg := Gg) cn) := by
  unfold connRefused; infer_instance
instance connRefused_timeless cn : Timeless (connRefused (Gg := Gg) cn) := by
  unfold connRefused; infer_instance
instance depSlotInv_persistent cn γ ready D (Φ : O → IProp GF) :
    Persistent (depSlotInv (Gg := Gg) cn γ ready D Φ) := by
  unfold depSlotInv; infer_instance
instance slotDone_persistent γ (o : O) : Persistent (slotDone (Gg := Gg) γ o) := by
  unfold slotDone; infer_instance
instance slotDone_timeless γ (o : O) : Timeless (slotDone (Gg := Gg) γ o) := by
  unfold slotDone; infer_instance

end defs

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS]
variable {K O : Type} [Pos.Countable K] [Pos.Countable O]

/-- The slot map, empty. -/
theorem depSlots_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ σ : NetSlotGS, depSlotsCtx (Gg := Gg) (σ := σ) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := SlotNames × Pos) with ⟨%γs, Hs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γr, Hr⟩
  imod inv_alloc slotsN E (slotsInv (Gg := Gg) (σ := ⟨γs, γr⟩)) $$ [Hs Hr] with #Hinv
  · inext
    unfold slotsInv
    iexists ∅, ∅
    iframe Hs Hr
    isplitl []
    · iapply BigSepM.bigSepM_empty.2
      itrivial
    · iapply BigSepM.bigSepM_empty.2
      itrivial
  imodintro
  iexists ⟨γs, γr⟩
  unfold depSlotsCtx
  iexact Hinv

variable [σ : NetSlotGS]

theorem depSlotOf_agree (cn : Nat) (γ γ' : SlotNames) (k k' : K) :
    ⊢ depSlotOf (Gg := Gg) cn γ k -∗ depSlotOf cn γ' k' -∗ ⌜γ = γ' ∧ k = k'⌝ := by
  unfold depSlotOf
  iintro H1 H2
  icases ghostMapElem_agree $$ H1 H2 with %h
  ipureintro
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact ⟨h1, Pos.encode_inj h2⟩

/-- A refused connection's acceptor has no fresh token left. -/
theorem connRefused_fresh (E : CoPset) (cn : Nat) (hE : (↑slotsN : CoPset) ⊆ E) :
    ⊢ depSlotsCtx (Gg := Gg) -∗ connRefused cn -∗ connFresh (Gg := Gg) cn true ={E}=∗
      (False : IProp GF) := by
  iintro #Hm #Hr Hf
  unfold depSlotsCtx
  iinv Hm with Hi Hclose
  iunfold slotsInv at Hi
  icases Hi with ⟨%M, %Rf, >Ha, >Hfs, >Hra, >Hrs⟩
  unfold connRefused
  icases ghost_map_lookup $$ Hra Hr with %hl
  ihave Hf' := BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hl) $$ Hrs
  iexfalso
  iapply connFresh_excl cn true $$ [Hf Hf']
  iframe Hf Hf'

/-- **Register a connection's slot** (its dialer, once per connection, with the fresh token its
`Dial` gave and the deposit): the slot, and the dialer's token. -/
theorem depSlot_register (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat) (k : K)
    (ready : List w8 → Prop) (D : IProp GF) (Φ : O → IProp GF) :
    ⊢ depSlotsCtx (Gg := Gg) -∗ connFresh (Gg := Gg) cn false -∗ D ={E}=∗
      ∃ γ, depSlotOf cn γ k ∗ depSlotInv cn γ ready D Φ ∗ token γ.t := by
  have hM : (↑slotsN : CoPset) ⊆ E := fun p hp => hE p (slotsN_sub p hp)
  iintro #Hm Hf HD
  imod mono_list_own_alloc (GF := GF) ([] : List O) with ⟨%γd, Hd, -⟩
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  unfold depSlotsCtx
  iinv Hm with Hi Hclose
  iunfold slotsInv at Hi
  icases Hi with ⟨%M, %Rf, >Ha, >Hfs, >Hra, >Hrs⟩
  have hnone : M.lookup cn = none ∨ ∃ v, M.lookup cn = some v := by
    cases M.lookup cn with
    | none => exact .inl rfl
    | some v => exact .inr ⟨v, rfl⟩
  rcases hnone with hnone | ⟨v, hv⟩
  · imod ghost_map_insert_persist cn (⟨γd, γt⟩, Pos.Countable.encode k) hnone $$ Ha with ⟨Ha, #He⟩
    imod Hclose $$ [Ha Hfs Hf Hra Hrs] with -
    · inext
      unfold slotsInv
      iexists M.insert cn (⟨γd, γt⟩, Pos.Countable.encode k), Rf
      iframe Ha Hra Hrs
      iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hnone)).2
      iframe Hf Hfs
    imod inv_alloc (depSlotN cn) _ (depSlotBody (Gg := Gg) cn ⟨γd, γt⟩ ready D Φ) $$ [HD Hd]
      with #Hs
    · inext
      unfold depSlotBody
      ileft
      iframe HD Hd
    imodintro
    iexists ⟨γd, γt⟩
    unfold depSlotOf depSlotInv
    iframe He Hs Ht
  · ihave Hf' := BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hv) $$ Hfs
    iexfalso
    iapply connFresh_excl cn false $$ [Hf Hf']
    iframe Hf Hf'

/-- **Claim a slot** (the connection's acceptor, with its fresh token, a `ready` prefix of what
the dialer wrote and a later credit): the deposit, and the acceptor's share. -/
theorem depSlot_claim (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat) (γ : SlotNames)
    {ready : List w8 → Prop} (hr : SlotReady ready) (W : List w8) (hW : ready W)
    (D : IProp GF) (Φ : O → IProp GF) :
    ⊢ depSlotsCtx (Gg := Gg) -∗ depSlotInv cn γ ready D Φ -∗ connFresh (Gg := Gg) cn true -∗
      sentLb (Gg := Gg) cn false W -∗ £ 1 ={E}=∗ D ∗ slotRunTok (Gg := Gg) (O := O) γ := by
  have hS : (↑(depSlotN cn) : CoPset) ⊆ E := fun p hp => hE p (depSlotN_sub cn p hp)
  have hM := slotsN_diff E cn hE
  iintro #Hm #Hs Hf #Hlb Hlc
  unfold depSlotInv
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(depSlotN cn))
    (P := depSlotBody (Gg := Gg) cn γ ready D Φ)) $$ Hlc Hb with Hb
  iunfold depSlotBody at Hb
  iunfold slotClaimed at Hb
  icases Hb with (⟨HD, Hd⟩ | ⟨⟨Hf', -⟩, -⟩ | ⟨Ht, Hd, (⟨%P, %W', %hnr, Hw⟩ | #Hr)⟩)
  · ihave ⟨Hd1, Hd2⟩ := (monoListAuthOwn_fractional (GF := GF) γ.d ([] : List O)).fractional
      (1 : Qp).half (1 : Qp).half |>.1 $$ [Hd]
    · rw [Qp.half_add_half]; iexact Hd
    imod Hclose $$ [Hf Hd1] with -
    · inext
      unfold depSlotBody
      iright; ileft
      unfold slotClaimed
      iframe Hf
      isplitl []
      · iexists W
        iframe Hlb
        ipureintro; exact hW
      · ileft
        iexact Hd1
    imodintro
    unfold slotRunTok
    iframe HD Hd2
  · iexfalso
    iapply connFresh_excl cn true $$ [Hf Hf']
    iframe Hf Hf'
  · icases sendTok_sentLb_prefix cn false P W' W $$ Hw Hlb with %hp
    exfalso
    exact hnr (hr.mono W W' hW hp)
  · imod connRefused_fresh (E \ ↑(depSlotN cn)) cn hM $$ Hm Hr Hf with Hfalse
    iexfalso
    iexact Hfalse

/-- **Answer a slot** (its acceptor, with its share, the outcome `o`, `Φ o` and a later credit):
the slot records `o`. -/
theorem depSlot_answer (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat) (γ : SlotNames)
    (ready : List w8 → Prop) (D : IProp GF) (Φ : O → IProp GF) (o : O) :
    ⊢ depSlotInv (Gg := Gg) cn γ ready D Φ -∗ slotRunTok (Gg := Gg) (O := O) γ -∗ Φ o -∗ £ 1
      ={E}=∗ slotDone (Gg := Gg) γ o := by
  have hS : (↑(depSlotN cn) : CoPset) ⊆ E := fun p hp => hE p (depSlotN_sub cn p hp)
  iintro #Hs Hr HΦ Hlc
  unfold depSlotInv slotRunTok
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(depSlotN cn))
    (P := depSlotBody (Gg := Gg) cn γ ready D Φ)) $$ Hlc Hb with Hb
  iunfold depSlotBody at Hb
  iunfold slotClaimed at Hb
  icases Hb with (⟨-, Hd⟩ | ⟨Hc, (Hd | ⟨%o', Hd, -⟩)⟩ | ⟨-, Hd, -⟩)
  · icases monoListAuthOwn_agree (GF := GF) γ.d _ _ _ _ $$ Hr Hd with %h
    exfalso
    have h1 := h.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h1
    grind
  · ihave Hd := (monoListAuthOwn_fractional (GF := GF) γ.d ([] : List O)).fractional
      (1 : Qp).half (1 : Qp).half |>.2 $$ [Hr Hd]
    · iframe Hr Hd
    rw [Qp.half_add_half]
    imod monoListAuthOwn_update [o] (List.nil_prefix) $$ Hd with ⟨Hd, #Hlb⟩
    imod Hclose $$ [Hc Hd HΦ] with -
    · inext
      unfold depSlotBody slotClaimed
      iright; ileft
      iframe Hc
      iright
      iexists o
      iframe Hd
      ileft
      iexact HΦ
    imodintro
    unfold slotDone
    iexact Hlb
  · icases monoListAuthOwn_agree (GF := GF) γ.d _ _ _ _ $$ Hr Hd with %h
    exfalso
    have h1 := h.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h1
    grind
  · icases monoListAuthOwn_agree (GF := GF) γ.d _ _ _ _ $$ Hr Hd with %h
    exfalso
    have h1 := h.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h1
    grind

/-- **Take a slot's answer** (its dialer, with its token, the slot's record of `o` and a later
credit): `Φ o`. -/
theorem depSlot_take (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat) (γ : SlotNames)
    (ready : List w8 → Prop) (D : IProp GF) (Φ : O → IProp GF) (o : O) :
    ⊢ depSlotInv (Gg := Gg) cn γ ready D Φ -∗ token (GF := GF) γ.t -∗ slotDone (Gg := Gg) γ o -∗
      £ 1 ={E}=∗ Φ o := by
  have hS : (↑(depSlotN cn) : CoPset) ⊆ E := fun p hp => hE p (depSlotN_sub cn p hp)
  iintro #Hs Ht #Hlb Hlc
  unfold depSlotInv slotDone
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(depSlotN cn))
    (P := depSlotBody (Gg := Gg) cn γ ready D Φ)) $$ Hlc Hb with Hb
  iunfold depSlotBody at Hb
  iunfold slotClaimed at Hb
  icases Hb with (⟨-, Hd⟩ | ⟨Hc, (Hd | ⟨%o', Hd, (HΦ | Ht')⟩)⟩ | ⟨-, Hd, -⟩)
  · icases mono_list_auth_lb_valid (GF := GF) γ.d _ _ _ $$ Hd Hlb with %h
    exfalso
    have := List.prefix_nil.mp h.2
    simp at this
  · icases mono_list_auth_lb_valid (GF := GF) γ.d _ _ _ $$ Hd Hlb with %h
    exfalso
    have := List.prefix_nil.mp h.2
    simp at this
  · icases mono_list_auth_lb_valid (GF := GF) γ.d _ _ _ $$ Hd Hlb with %h
    have ho : o = o' := by
      have := h.2
      rw [List.cons_prefix_cons] at this
      exact this.1
    subst ho
    imod Hclose $$ [Hc Hd Ht] with -
    · inext
      unfold depSlotBody slotClaimed
      iright; ileft
      iframe Hc
      iright
      iexists o
      iframe Hd
      iright
      iexact Ht
    imodintro
    iexact HΦ
  · iexfalso
    iapply token_exclusive $$ Ht Ht'
  · icases mono_list_auth_lb_valid (GF := GF) γ.d _ _ _ $$ Hd Hlb with %h
    exfalso
    have := List.prefix_nil.mp h.2
    simp at this

/-- **Refuse a connection** (its acceptor, with its fresh token, instead of claiming): it never
claims a slot on it. -/
theorem conn_refuse (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat) :
    ⊢ depSlotsCtx (Gg := Gg) -∗ connFresh (Gg := Gg) cn true ={E}=∗ connRefused (Gg := Gg) cn := by
  have hM : (↑slotsN : CoPset) ⊆ E := fun p hp => hE p (slotsN_sub p hp)
  iintro #Hm Hf
  unfold depSlotsCtx
  iinv Hm with Hi Hclose
  iunfold slotsInv at Hi
  icases Hi with ⟨%M, %Rf, >Ha, >Hfs, >Hra, >Hrs⟩
  have hnone : Rf.lookup cn = none ∨ ∃ v, Rf.lookup cn = some v := by
    cases Rf.lookup cn with
    | none => exact .inl rfl
    | some v => exact .inr ⟨v, rfl⟩
  rcases hnone with hnone | ⟨v, hv⟩
  · imod ghost_map_insert_persist cn () hnone $$ Hra with ⟨Hra, #He⟩
    imod Hclose $$ [Ha Hfs Hf Hra Hrs] with -
    · inext
      unfold slotsInv
      iexists M, Rf.insert cn ()
      iframe Ha Hfs Hra
      iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hnone)).2
      iframe Hf Hrs
    imodintro
    unfold connRefused
    iexact He
  · ihave Hf' := BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hv) $$ Hrs
    iexfalso
    iapply connFresh_excl cn true $$ [Hf Hf']
    iframe Hf Hf'

/-- **Take the deposit back from a refused connection's slot** (its dialer, with its token and a
later credit). -/
theorem depSlot_takeRefused (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat)
    (γ : SlotNames) (ready : List w8 → Prop) (D : IProp GF) (Φ : O → IProp GF) :
    ⊢ depSlotsCtx (Gg := Gg) -∗ depSlotInv cn γ ready D Φ -∗ token (GF := GF) γ.t -∗
      connRefused (Gg := Gg) cn -∗ £ 1 ={E}=∗ D := by
  have hS : (↑(depSlotN cn) : CoPset) ⊆ E := fun p hp => hE p (depSlotN_sub cn p hp)
  have hM := slotsN_diff E cn hE
  iintro #Hm #Hs Ht #Hr Hlc
  unfold depSlotInv
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(depSlotN cn))
    (P := depSlotBody (Gg := Gg) cn γ ready D Φ)) $$ Hlc Hb with Hb
  iunfold depSlotBody at Hb
  iunfold slotClaimed at Hb
  icases Hb with (⟨HD, Hd⟩ | ⟨⟨Hf, -⟩, -⟩ | ⟨Ht', -, -⟩)
  · imod Hclose $$ [Ht Hd] with -
    · inext
      unfold depSlotBody
      iright; iright
      iframe Ht Hd
      iright
      iexact Hr
    imodintro
    iexact HD
  · imod connRefused_fresh (E \ ↑(depSlotN cn)) cn hM $$ Hm Hr Hf with Hfalse
    iexfalso
    iexact Hfalse
  · iexfalso
    iapply token_exclusive $$ Ht Ht'

/-- **Withdraw the deposit** (its dialer, with its token, a later credit and its `sendTok` at a
`W` after which no acceptor may claim, which it gives up). -/
theorem depSlot_withdraw (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat)
    (γ : SlotNames) {ready : List w8 → Prop} (hr : SlotReady ready) (P : Proto GF)
    (W : List w8) (hW : ¬ ready W) (D : IProp GF) (Φ : O → IProp GF) :
    ⊢ depSlotInv (Gg := Gg) cn γ ready D Φ -∗ token (GF := GF) γ.t -∗
      sendTok (Gg := Gg) cn false P W -∗ £ 1 ={E}=∗ D := by
  have hS : (↑(depSlotN cn) : CoPset) ⊆ E := fun p hp => hE p (depSlotN_sub cn p hp)
  iintro #Hs Ht Hw Hlc
  unfold depSlotInv
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(depSlotN cn))
    (P := depSlotBody (Gg := Gg) cn γ ready D Φ)) $$ Hlc Hb with Hb
  iunfold depSlotBody at Hb
  iunfold slotClaimed at Hb
  icases Hb with (⟨HD, Hd⟩ | ⟨⟨-, ⟨%W', %hW', #Hlb⟩⟩, -⟩ | ⟨Ht', -, -⟩)
  · imod Hclose $$ [Ht Hd Hw] with -
    · inext
      unfold depSlotBody
      iright; iright
      iframe Ht Hd
      ileft
      iexists P, W
      iframe Hw
      ipureintro; exact hW
    imodintro
    iexact HD
  · icases sendTok_sentLb_prefix cn false P W W' $$ Hw Hlb with %hp
    exfalso
    exact hW (hr.mono W' W hW' hp)
  · iexfalso
    iapply token_exclusive $$ Ht Ht'

end laws

end Net
end Perennial
