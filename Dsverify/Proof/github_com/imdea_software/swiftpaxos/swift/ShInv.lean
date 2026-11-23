/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ShInv.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The descriptors' share map `γsh`** (round 21, sv-swb; notes/prove-swift.md §26-27; decision (2)
of §25): a replica-wide ghost map descriptor ↦ its owner's current epoch share `q`. `descSt`
(AcksSpecs.lean) holds half of a running descriptor's element; `descGone`/`descDone` return it;
a descriptor at rest (in the pool, or freed by `handleSync`/a retired goroutine) holds its
element whole (`swift.descRestA`). The authority is in the replica invariant `swift.shInv`
(namespace `swift.shN`), allocated by `New` (NewProof.lean) before the descriptor pool, whose
predicate (`swift.descPoolP (swift.descDFA γsh)`) mentions it.

**Keys are never deleted.** Freshness at the first use of a descriptor (`allocDesc`'s fresh
`&commandDesc{}`, the pool's `New`) comes from the invariant keeping, per key, the descriptor's
`successorsL` mutex (`sync.isMutex`, persistent): a fresh allocation owns `successorsL` whole,
which contradicts the mutex's invariant (`swift.isMutex_own_false`: the lock invariant always
holds a quarter of the cell). No field of `commandDesc` other than `successorsL` is left
unwritten by `newDesc` and the handlers (checked on the fork: every other field is assigned), so
there is no read-only field to key on.

Also here (moved from Deliver.lean/DescState.lean/SyncSpecs.lean so that `New`'s statements can
use them): `swift.dfld`, `swift.succInv`, `swift.descDF`, `swift.descPooled`, `swift.descPoolP`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.hook
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.PoolDefs
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The share map's invariant's namespace. -/
def swift.shN : Namespace := ndot nroot "swiftpaxos.sh"

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- Field `f` of the descriptor at `d`. -/
abbrev swift.dfld (d : Loc) (f : GoString) : Loc := structFieldRef swift.commandDesc f d

/-- `successorsL`'s invariant: the successors' slice. -/
def swift.succInv (d : Loc) : IProp netDistGF :=
  iprop(∃ (sl : GoSlice) (l : List swift.CommandId), swift.dfld d go!"successors" ↦ sl ∗
    sl ↦* l ∗ ownSliceCap swift.CommandId sl (DFrac.own 1))

/-- **The share map's invariant** (see the file header): the authority, and per key the
descriptor's `successorsL` mutex. -/
def swift.shInv (γsh : GName) : IProp netDistGF :=
  iprop(∃ m : GMap Loc Qp, ghostMapAuth γsh 1 m ∗
    [∗map] d ↦ _q ∈ m, sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))

/-- An `*OptCondF` field's value as `ReinitCondF` wants it: nil, or the object (the body of
`hook.ocf.ownOcf` at some condition and store). -/
def swift.ocfAny (cf : Loc) : IProp netDistGF :=
  iprop(⌜cf = null⌝ ∨ ∃ (cond : GoFunc) (fs : List GoFunc) (sl : GoSlice) (L : List GoFunc),
    cf ↦ hook.OptCondF.mk cond sl (W64 fs.length) ∗
    sl ↦* L ∗ ownSliceCap GoFunc sl (DFrac.own 1) ∗ ⌜fs <+: L ∧ fs.length < 2 ^ 62⌝)

/-- A `*MsgSet` field's value as `ReinitMsgSet` wants it: nil, or the set's data. -/
def swift.msetAny (ms : Loc) : IProp netDistGF :=
  iprop(⌜ms = null⌝ ∨ replica.mset.ownAny ms)

/-- **A descriptor at rest, the rest of its fields** (the concrete `DR` of `descDF`, round 21):
its share map's element whole (any share), its `successorsL` mutex, the fields `newDesc` writes
at any value (`afterPropagate` as `ReinitCondF` wants it), `cmd` with its value slice read-only
(`newDesc` does not reset it; the descriptor's state reads it before a proposal sets it), and
`waitingAck` (`newDesc` does not reset it either: see notes/prove-swift.md §27, P12). -/
def swift.descRestA (γsh : GName) (d : Loc) : IProp netDistGF :=
  iprop(∃ (q : Qp) (ph sn : w64) (c : sp.Cmd) (vs dep hs pd sb : GoSlice) (p ap wa : Loc)
      (sl : Bool) (df : GoFunc),
    ghostMapElem γsh d (DFrac.own 1) q ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
    swift.dfld d go!"phase" ↦ ph ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk c.op c.key vs ∗ vs ↦*□ c.val ∗ ⌜c.op ≠ W8 3⌝ ∗
    swift.dfld d go!"dep" ↦ dep ∗ swift.dfld d go!"hs" ↦ hs ∗ swift.dfld d go!"seqnum" ↦ sn ∗
    swift.dfld d go!"propose" ↦ p ∗ swift.dfld d go!"proposeDep" ↦ pd ∗
    swift.dfld d go!"afterPropagate" ↦ ap ∗ swift.ocfAny ap ∗
    swift.dfld d go!"slowPath" ↦ sl ∗ swift.dfld d go!"defered" ↦ df ∗
    swift.dfld d go!"waitingAck" ↦ wa ∗ swift.dfld d go!"storedBallots" ↦ sb)

/-- **The concrete `DF`** (round 18; moved here in round 21): the descriptor's remaining fields
`DR d` and its `active`/`seq` (whole), with `active → seq` (a descriptor at home that is active
is a sequential one: a stopped goroutine wrote `active = false`). -/
def swift.descDF (DR : Loc → IProp netDistGF) (d : Loc) : IProp netDistGF :=
  iprop(∃ (a s : Bool), swift.dfld d go!"active" ↦ a ∗ swift.dfld d go!"seq" ↦ s ∗
    ⌜a = true → s = true⌝ ∗ DR d)

/-- `descDF` at the share map `γsh`'s descriptors at rest. -/
abbrev swift.descDFA (γsh : GName) : Loc → IProp netDistGF := swift.descDF (swift.descRestA γsh)

/-- **A descriptor as the pool keeps it** (round 16, sv-swb; round 21: with the two sets as
`ReinitMsgSet` wants them): the four fields `descFree` lists (handleSync's closure has rewritten
them: `msgs`, `stopChan` nil, the sets freed) and `DF d` (the rest). `freeDesc`'s
precondition. -/
def swift.descPooled (DF : Loc → IProp netDistGF) (d : Loc) : IProp netDistGF :=
  iprop(∃ (m s sl fa : Loc), swift.dfld d go!"msgs" ↦ m ∗ swift.dfld d go!"stopChan" ↦ s ∗
    swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    swift.msetAny sl ∗ swift.msetAny fa ∗ DF d)

/-- The descriptor pool's predicate over `DF` (round 16; round 21: or a fresh zero descriptor,
what the pool's `New` returns). -/
def swift.descPoolP (DF : Loc → IProp netDistGF) (x : GoInterface) : IProp netDistGF :=
  iprop(∃ d : Loc, ⌜x = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
    (swift.descPooled DF d ∨ d ↦ (Perennial.zero_val swift.commandDesc)))

/-- **The descriptor pool as `New` leaves it** (round 21): the share map's invariant at some
`γsh` and `descPool` with predicate `descPoolP (descDFA γsh)` (persistent). -/
def swift.descPoolOk (rp : Loc) : IProp netDistGF :=
  iprop(∃ (γsh : GName) (pf : GoFunc), inv swift.shN (swift.shInv γsh) ∗ ⌜pf ≠ func.nil⌝ ∗
    sync.isPool (swift.fld rp go!"descPool") pf iprop(True) (swift.descPoolP (swift.descDFA γsh)))

instance swift.descPoolOk_persistent (rp : Loc) : Persistent (swift.descPoolOk rp) := by
  unfold swift.descPoolOk; infer_instance

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- **A mutex's cell is never owned whole** (the lock invariant holds a quarter of it). -/
theorem swift.isMutex_own_false (m : Loc) (R : IProp netDistGF) (b : Bool) :
    sync.isMutex m R ∗ typedPointsto m b (DFrac.own 1) ⊢ |={⊤}=> False := by
  iintro ⟨#Hm, Hp⟩
  rw [sync.isMutex_unseal]; unfold sync.isMutexDef
  rw [isLock_unseal]; unfold isLockDef
  icases Hm with ⟨#Hinv, -⟩
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%b', >Hq, -⟩
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  icases Hq with ⟨Hq, _⟩
  icases Hp with ⟨Hp, _⟩
  simp only [typedPointstoDef_heap]
  icombine Hq Hp gives % ⟨Hbad, _⟩
  exfalso
  have h : (Qp.quarter : Rat) + (1 : Qp) ≤ 1 := Hbad
  simp at h
  grind

/-- **A fresh descriptor enters the share map** (its first use: `allocDesc`'s fresh
`&commandDesc{}`): it owns `successorsL` whole (so it is not a key: `isMutex_own_false`); its
mutex is initialised with `succInv d` and kept by the invariant, its element is the caller's. -/
theorem swift.shInv_fresh (γsh : GName) (d : Loc) (q : Qp) :
    inv swift.shN (swift.shInv γsh) ∗ £ 1 ∗
      typedPointsto (swift.dfld d go!"successorsL") (Perennial.zero_val sync.Mutex) (DFrac.own 1) ∗
      ▷ swift.succInv d ⊢
    |={⊤}=> sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
      ghostMapElem γsh d (DFrac.own 1) q := by
  iintro ⟨#Hinv, Hlc, Hl, HR⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.shN) $$ Hlc Hi with Hi
  iunfold swift.shInv at Hi
  icases Hi with ⟨%m, Ha, #Hm⟩
  cases hd : m.lookup d with
  | some q0 =>
    ihave #Hmd := BigSepM.bigSepM_lookup (Φ := fun d _ =>
      sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))
      (show Iris.Std.PartialMap.get? m d = some q0 from hd) $$ Hm
    imod Hclose $$ [Ha] with -
    · inext; iunfold swift.shInv; iexists m; iframe Ha; iexact Hm
    imod swift.isMutex_own_false _ _ _ $$ [Hmd Hl] with Hf
    · iframe Hmd; iexact Hl
    iexfalso; iexact Hf
  | none =>
    imod sync.init_Mutex (swift.succInv d) (⊤ \ ↑swift.shN) _ $$ Hl HR with #Hmx
    imod ghost_map_insert d q hd $$ Ha with ⟨Ha, He⟩
    imod Hclose $$ [Ha] with -
    · inext; iunfold swift.shInv; iexists (m.insert d q); iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun d _ =>
        sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))
        (show Iris.Std.PartialMap.get? m d = none from hd)).2
      iframe Hmx; iexact Hm
    imodintro
    iframe Hmx He

/-- **A descriptor's share is updated** (the owner holds the element whole). -/
theorem swift.shInv_update (γsh : GName) (E : CoPset) (hE : ↑swift.shN ⊆ E) (d : Loc)
    (q q' : Qp) :
    inv swift.shN (swift.shInv γsh) ∗ ghostMapElem γsh d (DFrac.own 1) q ⊢
    |={E}=> ghostMapElem γsh d (DFrac.own 1) q' := by
  iintro ⟨#Hinv, He⟩
  iinv Hinv with Hi Hclose
  iunfold swift.shInv at Hi
  icases Hi with ⟨%m, >Ha, Hm⟩
  ihave %Hd := ghost_map_lookup $$ Ha He
  imod ghost_map_update q' $$ Ha He with ⟨Ha, He⟩
  imod Hclose $$ [Ha Hm] with -
  · inext; iunfold swift.shInv; iexists (m.insert d q'); iframe Ha
    ihave #Hm' := Hm
    ihave #Hmd := BigSepM.bigSepM_lookup (Φ := fun d _ =>
      sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))
      (show Iris.Std.PartialMap.get? m d = some q from Hd) $$ Hm'
    icases (BigSepM.bigSepM_delete (Φ := fun d _ =>
      sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))
      (show Iris.Std.PartialMap.get? m d = some q from Hd)).1 $$ Hm' with ⟨-, Hdel⟩
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun d _ =>
      sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))).2
    iframe Hmd Hdel
  imodintro
  iexact He

/-- The two halves of a descriptor's element agree. -/
theorem swift.sh_agree (γsh : GName) (d : Loc) (q q' : Qp) :
    ghostMapElem γsh d (DFrac.own (1 : Qp).half) q ∗ ghostMapElem γsh d (DFrac.own (1 : Qp).half) q' ⊢
    ⌜q = q'⌝ ∗ ghostMapElem γsh d (DFrac.own 1) q := by
  iintro ⟨H1, H2⟩
  ihave %Hq := ghostMapElem_agree d γsh _ _ q q' $$ H1 H2
  subst Hq
  isplitr
  · ipureintro; rfl
  iapply (ghostMapElem_halves γsh d q).2
  iframe

/-- **The share map's allocation** (by `New`). -/
theorem swift.shInv_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ γsh : GName, inv swift.shN (swift.shInv γsh) := by
  imod ghost_map_alloc_empty (K := Loc) (V := Qp) (GF := netDistGF) with ⟨%γsh, Ha⟩
  imod inv_alloc swift.shN E (swift.shInv γsh) $$ [Ha] with #Hi
  · inext; iunfold swift.shInv; iexists ∅; iframe Ha; iapply BigSepM.bigSepM_empty.2; itrivial
  imodintro
  iexists γsh; iexact Hi

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
