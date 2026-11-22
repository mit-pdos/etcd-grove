/-
# remote: the slot library (`notes/remote-port-plan.md`, §4)

What crosses a connection of `examples/lib/remote`, over the net extension's protocol library
(`GooseLang/Ext/Net/Proto.lean`):

* **The far side's store** (`RBase`): a deterministic base store `B` (txnlin's `linkv.PendSpec`:
  `step`, `isWrite`; a read does not change the state, `reads_stay`), the base state's predicate
  `sysState st` over the global ghost state (the same proposition at every node), the mask `Eop` of
  the invariants the far side's operation may have open at its linearization point, and the Go
  values and bytes of the model's inputs and outputs: `iv i` (an input), `ov o` (an output),
  `unk i` (the unknown output of `i`), `encIn i` (`EncIn`'s bytes), `encOut v` (`EncOut`'s).
* **The update** `lin R i Φ`: the linearization point of the base operation `i`, a fancy update
  from `⊤ ∖ Eop` (as lintest's atomic triples' updates, without the `▷`) that takes `sysState st`
  to `sysState (step i st).1` and gives `Φ` of the step's output.
* **The slot of a connection** (the lab's spec (R), one slot per connection): after its `Dial`, the
  dialer registers its connection `cn` with ghost names `γ` and the input `i` in the slot map
  (`slotOf cn γ i`, persistent), whose invariant (`mapInv`) keeps every registered connection's
  dialer `connFresh cn false`, so a connection gets one slot (`slot_register`). The slot's invariant
  (`slotInv`, at `slotN cn`) holds the update `slotUpd R i Φ` until the connection's acceptor claims it
  with its own `connFresh cn true` (exclusive, `connFresh_excl`), which stays in the invariant: the
  update is handed out at most once (`slot_claim`). The acceptor keeps half of the slot's monotone
  list `γ.d` (`runTok`), and once its operation answered `o` with `Φ o`, it puts `Φ o` in the slot
  and the list at `[o]` (`slot_done`, giving `doneLb γ o`); the dialer, with its token `γ.t`, takes
  `Φ o` out (`slot_take`).
* **The protocols** of a node's address: `reqP` (what a dialer writes: the frame of `encIn i` for
  the input of its slot) and `repP` (what an acceptor writes: the frame of `encOut v`, `v` the
  slot's input's unknown output, or an output `ov o` the slot has recorded, `doneLb γ o`). Both are
  persistent; a reader that read a whole frame gets the frame the writer meant (`req_read`,
  `rep_read`, by `frame_prefix_eq`).
* **The codec** (`codecOk R cd`): `cd`'s functions compute `R`'s encodings and decodings,
  `IsRead`, `Unknown` and `IsUnknown`.
* **The far side's operation** (`opMaybe R tok op`): given `slotUpd R i Φ` (a write's one-shot
  `lin R i Φ`; a read's `□ lin R i Φ`, which it may fire zero or more times, each firing giving
  `Φ` of its output: the read form), `op(sys, iv i)` either returns `ov o` with `Φ o`, or returns
  `unk i` (a write's update may have fired, may fire later, or never: the lab's `opAwpMaybe`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Wire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.PendModel
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## The far side's store -/

section base
variable [GooseExts]

/-- The far side's base store and the Go values and bytes of its inputs and outputs (see the file
header). -/
structure RBase (GF : BundledGFunctors) (St I O : Type) where
  B : EtcdGrove.linkv.PendSpec St I O
  sysState : St → IProp GF
  Eop : CoPset
  iv : I → GoInterface
  ov : O → GoInterface
  unk : I → GoInterface
  encIn : I → List w8
  encOut : GoInterface → List w8
  reads_stay : ∀ i st, B.isWrite i = false → (B.step i st).1 = st
  encIn_len : ∀ i, (encIn i).length < 2 ^ 63
  encOut_len : ∀ v, (encOut v).length < 2 ^ 63

/-- A value the far side may answer: an output, or an input's unknown output. -/
def RBase.outOk {GF : BundledGFunctors} {St I O : Type} (R : RBase GF St I O) (v : GoInterface) :
    Prop :=
  (∃ o, v = R.ov o) ∨ (∃ i, v = R.unk i)

/-- The bytes `Do`'s second prophecy says (its values: a count `n`, then the bytes, each as a
`uint64`): the first `n` values after the count, as bytes. -/
def prophBytes : List w64 → List w8
  | [] => []
  | n :: t => (t.take (uint.nat n)).map (fun x => W8 (uint.Z x))

theorem prophBytes_eq (l : List w8) (n : w64) (r : List w64) (hn : uint.nat n = l.length) :
    prophBytes (n :: (l.map (fun b => W64 (uint.Z b)) ++ r)) = l := by
  simp only [prophBytes, hn]
  rw [List.take_left' (by simp)]
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, id_eq]
  word

end base

/-! ## Ghost names, namespaces -/

/-- The slot map's ghost name. -/
class RemoteGS where
  slots : GName

/-- A slot's ghost names: its monotone list (nothing, or the output recorded) and the dialer's
token. -/
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

def remoteN : Namespace := nroot.@"remote"
def mapN : Namespace := remoteN.@"map"
def slotN (cn : Nat) : Namespace := (remoteN.@"slot").@cn

/-! ## The vocabulary -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O] (R : RBase GF St I O)

/-- The linearization point of the base operation `i` (see the file header). -/
def lin (i : I) (Φ : O → IProp GF) : IProp GF :=
  iprop(|={⊤ \ R.Eop, ∅}=> ∃ st, R.sysState st ∗
    (R.sysState (R.B.step i st).1 ={∅, ⊤ \ R.Eop}=∗ Φ (R.B.step i st).2))

/-- **The update a slot hands to the far side**: a write's one-shot `lin`; a read's `lin`
persistently, which the far side may fire zero or more times (a read leaves the state unchanged,
`reads_stay`), each firing giving `Φ` of its output (the read form; `notes/specs-only/ledger.md`,
2026-11-22, "`remote.opMaybe`'s read form"). -/
def slotUpd (i : I) (Φ : O → IProp GF) : IProp GF :=
  if R.B.isWrite i then lin R i Φ else iprop(□ lin R i Φ)

omit π ρ in
theorem slotUpd_write {i : I} {Φ : O → IProp GF} (h : R.B.isWrite i = true) :
    slotUpd R i Φ = lin R i Φ := by
  simp [slotUpd, h]

omit π ρ in
theorem slotUpd_read {i : I} {Φ : O → IProp GF} (h : R.B.isWrite i = false) :
    slotUpd R i Φ = iprop(□ lin R i Φ) := by
  simp [slotUpd, h]

/-- The connection `cn` has the slot `γ`, for the input `i` (persistent). -/
def slotOf (cn : Nat) (γ : SlotNames) (i : I) : IProp GF :=
  ghostMapElem ρ.slots cn DFrac.discard (γ, i)

/-- The acceptor's share of a claimed slot. -/
def runTok (γ : SlotNames) : IProp GF := monoListAuthOwn (A := O) γ.d (1 : Qp).half []

/-- The slot `γ` recorded the output `o` (persistent). -/
def doneLb (γ : SlotNames) (o : O) : IProp GF := monoListLbOwn γ.d [o]

/-- The slot's states: the update, unclaimed; claimed (the acceptor's `connFresh` in it);
answered `o`, with `Φ o` or, once the dialer took it, the dialer's token. -/
def slotBody (cn : Nat) (γ : SlotNames) (i : I) (Φ : O → IProp GF) : IProp GF :=
  iprop((slotUpd R i Φ ∗ monoListAuthOwn (A := O) γ.d 1 []) ∨
    (connFresh (Gg := Gg) cn true ∗
      (monoListAuthOwn (A := O) γ.d (1 : Qp).half [] ∨
        ∃ o : O, monoListAuthOwn γ.d 1 [o] ∗ (Φ o ∨ token γ.t))))

/-- The slot's invariant (persistent). -/
def slotInv (cn : Nat) (γ : SlotNames) (i : I) (Φ : O → IProp GF) : IProp GF :=
  inv (slotN cn) (slotBody R cn γ i Φ)

/-- The slot map: the registered connections, each with its dialer's fresh token. -/
def mapInv : IProp GF :=
  iprop(∃ M : GMap Nat (SlotNames × I), ghostMapAuth ρ.slots 1 M ∗
    [∗map] cn ↦ _v ∈ M, connFresh (Gg := Gg) cn false)

/-- The slot map's invariant (persistent). -/
def mapCtx : IProp GF := inv mapN (mapInv (Gg := Gg) (I := I))

/-- What a dialer writes: the frame of its slot's input. -/
def reqP : Proto GF := fun cn W =>
  iprop(∃ (γ : SlotNames) (i : I) (Φ : O → IProp GF), ⌜W = frame (R.encIn i)⌝ ∗ slotOf cn γ i ∗
    slotInv R cn γ i Φ)

/-- What an acceptor writes: the frame of the slot's input's unknown output, or of an output the
slot recorded. -/
def repP : Proto GF := fun cn W =>
  iprop(∃ (γ : SlotNames) (i : I) (v : GoInterface), ⌜W = frame (R.encOut v)⌝ ∗ slotOf cn γ i ∗
    (⌜v = R.unk i⌝ ∨ ∃ o, ⌜v = R.ov o⌝ ∗ doneLb (O := O) γ o))

/-- The node at `a` serves calls: its address's protocols are `reqP` and `repP` (persistent). -/
def remoteAddr (a : GoString) : IProp GF := addrProto (Gg := Gg) a (reqP R) (repP R)

instance remoteAddr_persistent a : Persistent (remoteAddr R a) := by
  unfold remoteAddr; infer_instance

instance slotOf_persistent cn γ i : Persistent (slotOf (Gg := Gg) (I := I) cn γ i) := by
  unfold slotOf; infer_instance
instance doneLb_persistent γ o : Persistent (doneLb (Gg := Gg) γ (O := O) o) := by
  unfold doneLb; infer_instance
instance slotInv_persistent cn γ i Φ : Persistent (slotInv R cn γ i Φ) := by
  unfold slotInv; infer_instance
instance mapCtx_persistent : Persistent (mapCtx (Gg := Gg) (I := I)) := by
  unfold mapCtx; infer_instance
instance reqP_persistent cn W : Persistent (reqP R cn W) := by
  unfold reqP; infer_instance
instance repP_persistent cn W : Persistent (repP R cn W) := by
  unfold repP; infer_instance

end defs

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O] (R : RBase GF St I O)

/-- The slot map, empty. -/
theorem mapCtx_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ ρ : RemoteGS, mapCtx (Gg := Gg) (ρ := ρ) (I := I) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := SlotNames × I) with ⟨%γ, H⟩
  imod inv_alloc mapN E (mapInv (Gg := Gg) (ρ := ⟨γ⟩) (I := I)) $$ [H] with #Hinv
  · inext
    unfold mapInv
    iexists ∅
    iframe H
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iexists ⟨γ⟩
  unfold mapCtx
  iexact Hinv

variable [ρ : RemoteGS]

theorem slotOf_agree (cn : Nat) (γ γ' : SlotNames) (i i' : I) :
    ⊢ slotOf (Gg := Gg) cn γ i -∗ slotOf cn γ' i' -∗ ⌜γ = γ' ∧ i = i'⌝ := by
  unfold slotOf
  iintro H1 H2
  icases ghostMapElem_agree $$ H1 H2 with %h
  ipureintro
  exact Prod.mk.inj h

/-- **Register a connection** (its dialer, once its `Dial` succeeded): its slot, holding the
update, and the dialer's token. -/
theorem slot_register (E : CoPset) (hE : ↑mapN ⊆ E) (cn : Nat) (i : I) (Φ : O → IProp GF) :
    ⊢ mapCtx (Gg := Gg) (I := I) -∗ connFresh (Gg := Gg) cn false -∗ slotUpd R i Φ ={E}=∗
      ∃ γ, slotOf cn γ i ∗ slotInv R cn γ i Φ ∗ token γ.t := by
  iintro #Hm Hf HL
  imod mono_list_own_alloc (GF := GF) ([] : List O) with ⟨%γd, Hd, -⟩
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  unfold mapCtx
  iinv Hm with Hi Hclose
  iunfold mapInv at Hi
  icases Hi with ⟨%M, >Ha, >Hfs⟩
  -- `cn` is not registered: its dialer's fresh token is ours
  have hnone : M.lookup cn = none ∨ ∃ v, M.lookup cn = some v := by
    cases M.lookup cn with
    | none => exact .inl rfl
    | some v => exact .inr ⟨v, rfl⟩
  rcases hnone with hnone | ⟨v, hv⟩
  · imod ghost_map_insert_persist cn (⟨γd, γt⟩, i) hnone $$ Ha with ⟨Ha, #He⟩
    imod Hclose $$ [Ha Hfs Hf] with -
    · inext
      unfold mapInv
      iexists M.insert cn (⟨γd, γt⟩, i)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hnone)).2
      iframe Hf Hfs
    imod inv_alloc (slotN cn) _ (slotBody R cn ⟨γd, γt⟩ i Φ) $$ [HL Hd] with #Hs
    · inext
      unfold slotBody
      ileft
      iframe HL Hd
    imodintro
    iexists ⟨γd, γt⟩
    unfold slotOf slotInv
    iframe He Hs Ht
  · ihave Hf' := BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hv) $$ Hfs
    iexfalso
    iapply connFresh_excl cn false $$ [Hf Hf']
    iframe Hf Hf'

/-- **Claim a slot** (the connection's acceptor, with its fresh token and a later credit): the
update, and the acceptor's share. -/
theorem slot_claim (E : CoPset) (hE : ↑(slotN cn) ⊆ E) (γ : SlotNames) (i : I)
    (Φ : O → IProp GF) :
    ⊢ slotInv R cn γ i Φ -∗ connFresh (Gg := Gg) cn true -∗ £ 1 ={E}=∗
      slotUpd R i Φ ∗ runTok (Gg := Gg) (O := O) γ := by
  iintro #Hs Hf Hlc
  unfold slotInv
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(slotN cn)) (P := slotBody R cn γ i Φ)) $$ Hlc Hb with Hb
  iunfold slotBody at Hb
  icases Hb with (⟨HL, Hd⟩ | ⟨Hf', -⟩)
  · ihave ⟨Hd1, Hd2⟩ := (monoListAuthOwn_fractional (GF := GF) γ.d ([] : List O)).fractional
      (1 : Qp).half (1 : Qp).half |>.1 $$ [Hd]
    · rw [Qp.half_add_half]; iexact Hd
    imod Hclose $$ [Hf Hd1] with -
    · inext
      unfold slotBody
      iright
      iframe Hf
      ileft
      iexact Hd1
    imodintro
    unfold runTok
    iframe HL Hd2
  · iexfalso
    iapply connFresh_excl cn true $$ [Hf Hf']
    iframe Hf Hf'

/-- **Answer a slot** (its acceptor, with the output `o`, `Φ o` and a later credit): the slot records `o`. -/
theorem slot_done (E : CoPset) (hE : ↑(slotN cn) ⊆ E) (γ : SlotNames) (i : I)
    (Φ : O → IProp GF) (o : O) :
    ⊢ slotInv R cn γ i Φ -∗ runTok (Gg := Gg) (O := O) γ -∗ Φ o -∗ £ 1 ={E}=∗
      doneLb (Gg := Gg) γ o := by
  iintro #Hs Hr HΦ Hlc
  unfold slotInv runTok
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(slotN cn)) (P := slotBody R cn γ i Φ)) $$ Hlc Hb with Hb
  iunfold slotBody at Hb
  icases Hb with (⟨-, Hd⟩ | ⟨Hf, (Hd | ⟨%o', Hd, -⟩)⟩)
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
    imod Hclose $$ [Hf Hd HΦ] with -
    · inext
      unfold slotBody
      iright
      iframe Hf
      iright
      iexists o
      iframe Hd
      ileft
      iexact HΦ
    imodintro
    unfold doneLb
    iexact Hlb
  · icases monoListAuthOwn_agree (GF := GF) γ.d _ _ _ _ $$ Hr Hd with %h
    exfalso
    have h1 := h.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h1
    grind

/-- **Take a slot's answer** (its dialer, with its token, the slot's record of `o` and a later
credit): `Φ o`. -/
theorem slot_take (E : CoPset) (hE : ↑(slotN cn) ⊆ E) (γ : SlotNames) (i : I)
    (Φ : O → IProp GF) (o : O) :
    ⊢ slotInv R cn γ i Φ -∗ token (GF := GF) γ.t -∗ doneLb (Gg := Gg) γ o -∗ £ 1 ={E}=∗ Φ o := by
  iintro #Hs Ht #Hlb Hlc
  unfold slotInv doneLb
  iinv Hs with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(slotN cn)) (P := slotBody R cn γ i Φ)) $$ Hlc Hb with Hb
  iunfold slotBody at Hb
  icases Hb with (⟨-, Hd⟩ | ⟨Hf, (Hd | ⟨%o', Hd, (HΦ | Ht')⟩)⟩)
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
    imod Hclose $$ [Hf Hd Ht] with -
    · inext
      unfold slotBody
      iright
      iframe Hf
      iright
      iexists o
      iframe Hd
      iright
      iexact Ht
    imodintro
    iexact HΦ
  · iexfalso
    iapply token_exclusive $$ Ht Ht'

/-- A dialer's request, read whole by the acceptor: the frame of the slot's input. -/
theorem req_read (cn : Nat) (bd : List w8) (hbd : bd.length < 2 ^ 63) :
    protoPrefix (reqP (Gg := Gg) R) cn (frame bd) ⊢
      ∃ (γ : SlotNames) (i : I) (Φ : O → IProp GF), ⌜bd = R.encIn i⌝ ∗ slotOf (Gg := Gg) cn γ i ∗
        slotInv R cn γ i Φ := by
  unfold protoPrefix
  iintro (%h | ⟨%ext, %hext, #HP⟩)
  · exfalso
    have := congrArg List.length h
    simp [frame_length] at this
  · unfold reqP
    icases HP with ⟨%γ, %i, %Φ, %he, #Hso, #Hs⟩
    subst he
    iexists γ, i, Φ
    iframe Hso Hs
    ipureintro
    exact frame_prefix_eq hbd (R.encIn_len i) hext

/-- An acceptor's reply, read whole by the dialer of the slot `γ` of `i`: the frame of `i`'s
unknown output, or of an output the slot recorded. -/
theorem rep_read (cn : Nat) (γ : SlotNames) (i : I) (bd : List w8) (hbd : bd.length < 2 ^ 63) :
    ⊢ slotOf (Gg := Gg) cn γ i -∗ protoPrefix (repP (Gg := Gg) R) cn (frame bd) -∗
      ∃ v, ⌜bd = R.encOut v⌝ ∗ (⌜v = R.unk i⌝ ∨ ∃ o, ⌜v = R.ov o⌝ ∗ doneLb (Gg := Gg) γ o) := by
  unfold protoPrefix
  iintro #Hso (%h | ⟨%ext, %hext, #HP⟩)
  · exfalso
    have := congrArg List.length h
    simp [frame_length] at this
  · unfold repP
    icases HP with ⟨%γ', %i', %v, %he, #Hso', #Hv⟩
    subst he
    icases slotOf_agree cn γ γ' i i' $$ Hso Hso' with %h
    obtain ⟨rfl, rfl⟩ := h
    iexists v
    iframe Hv
    ipureintro
    exact frame_prefix_eq hbd (R.encOut_len v) hext

end laws

/-! ## The codec, the far side's operation -/

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O] (R : RBase GF St I O)

/-- `cd`'s functions compute `R`'s encodings and decodings, which inputs are reads, the unknown
outputs, and which outputs are unknown ones (persistent). A decoder may refuse an encoding; when
it accepts, it returns the value encoded. -/
def codecOk (cd : remote.Codec) : IProp GF :=
  iprop((∀ i : I, {{ True }} (App (Val #cd.EncIn') (Val #(R.iv i)))
      {{ (b : GoSlice), RET #b; b ↦* R.encIn i }}) ∗
    (∀ (i : I) (b : GoSlice) (dq : DFrac), {{ b ↦*{dq} R.encIn i }} (App (Val #cd.DecIn') (Val #b))
      {{ (x : GoInterface) (ok : Bool), RET (PairV #x #ok); ⌜ok = true → x = R.iv i⌝ }}) ∗
    (∀ v : GoInterface, ⌜R.outOk v⌝ -∗ {{ True }} (App (Val #cd.EncOut') (Val #v))
      {{ (b : GoSlice), RET #b; b ↦* R.encOut v }}) ∗
    (∀ (v : GoInterface) (b : GoSlice) (dq : DFrac), ⌜R.outOk v⌝ -∗
      {{ b ↦*{dq} R.encOut v }} (App (Val #cd.DecOut') (Val #b))
      {{ (x : GoInterface) (ok : Bool), RET (PairV #x #ok); ⌜ok = true → x = v⌝ }}) ∗
    (∀ i : I, {{ True }} (App (Val #cd.IsRead') (Val #(R.iv i)))
      {{ RET #(!R.B.isWrite i); True }}) ∗
    (∀ i : I, {{ True }} (App (Val #cd.Unknown') (Val #(R.iv i)))
      {{ RET #(R.unk i); True }}) ∗
    (∀ o : O, {{ True }} (App (Val #cd.IsUnknown') (Val #(R.ov o))) {{ RET #false; True }}) ∗
    (∀ i : I, {{ True }} (App (Val #cd.IsUnknown') (Val #(R.unk i))) {{ RET #true; True }}))

instance codecOk_persistent (cd : remote.Codec) : Persistent (codecOk (hG := hG) R cd) := by
  unfold codecOk; infer_instance

/-- **The far side's operation** `op` over the system `sys` (its resource `tok sys`): given the
update of `i`, it either committed it and returns the step's output with `Φ` of it, or returns
`i`'s unknown output (see the file header). -/
def opMaybe (tok : GoInterface → IProp GF) (op : GoFunc) : IProp GF :=
  iprop(∀ (sys : GoInterface) (i : I) (Φ : O → IProp GF),
    {{ tok sys ∗ slotUpd (Gg := hG.goose_globalGS) R i Φ }}
      (App (App (Val #op) (Val #sys)) (Val #(R.iv i)))
    {{ (v : GoInterface), RET #v; tok sys ∗ ((∃ o, ⌜v = R.ov o⌝ ∗ Φ o) ∨ ⌜v = R.unk i⌝) }})

instance opMaybe_persistent (tok : GoInterface → IProp GF) (op : GoFunc) :
    Persistent (opMaybe (hG := hG) R tok op) := by
  unfold opMaybe; infer_instance

end ops

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
