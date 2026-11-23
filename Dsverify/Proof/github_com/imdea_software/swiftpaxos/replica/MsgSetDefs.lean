/-
The definitions, specs and lemmas of `MsgSet.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSetQ
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.mset

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [π : NetProtoGS]
variable [sem : go.Semantics]

/-- The leader message: none, or one with `PL`. -/
def leaderOk (PL : GoInterface → IProp netDistGF) (lm : GoInterface) : IProp netDistGF :=
  iprop(⌜lm = interface.nil⌝ ∨ □ PL lm)

/-- A message accepted relative to the leader message `lm`. -/
def accOk (A : GoInterface → GoInterface → IProp netDistGF) (lm m : GoInterface) : IProp netDistGF :=
  iprop(⌜lm = interface.nil⌝ ∨ □ A lm m)

/-- The `accept` closure: on a message with `P` and the leader message, true only if accepted. -/
def acceptOk (acc : GoFunc) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∀ (k : w32) (m lm : GoInterface),
    {{ R ∗ □ P k m ∗ leaderOk PL lm }}
      (App (App (Val #acc) (Val #m)) (Val #lm))
    {{ (b : Bool), RET #b; R ∗ (⌜b = true⌝ → accOk A lm m) }})

/-- The `freeMsg` closure. -/
def freeOk (fr : GoFunc) (P : w32 → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (R : IProp netDistGF) : IProp netDistGF :=
  iprop(∀ (m : GoInterface),
    {{ R ∗ ((∃ k, □ P k m) ∨ □ PL m) }} (App (Val #fr) (Val #m)) {{ RET #(); R }})

/-- What the handler is called with: the leader message and the set's messages (of distinct
keys), when the quorum is reached (`sz` messages, or `sz - 1` and a leader message). -/
def handlerPre (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (lm : GoInterface) (ms : List GoInterface) : IProp netDistGF :=
  iprop(∃ kms : List (w32 × GoInterface), ⌜ms = kms.map Prod.snd ∧ (kms.map Prod.fst).Nodup ∧
      (sz ≤ ms.length ∨ (lm ≠ interface.nil ∧ sz ≤ ms.length + 1))⌝ ∗ leaderOk PL lm ∗
    □ (∀ k m, ⌜(k, m) ∈ kms⌝ → P k m ∗ accOk A lm m))

/-- The `handler` closure. -/
def handlerOk (hd : GoFunc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∀ (lm : GoInterface) (sl : GoSlice) (ms : List GoInterface),
    {{ R ∗ sl ↦* ms ∗ handlerPre sz P A PL lm ms }}
      (App (App (Val #hd) (Val #lm)) (Val #sl))
    {{ RET #(); R }})

/-- The closures' specs. -/
def closuresOk (acc fr hd : GoFunc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) :
    IProp netDistGF :=
  iprop(acceptOk acc P A PL R ∗ freeOk fr P PL R ∗ handlerOk hd sz P A PL R)

/-- The messages of the set, relative to the leader message. -/
def msgsOk (P : w32 → GoInterface → IProp netDistGF) (A : GoInterface → GoInterface → IProp netDistGF)
    (lm : GoInterface) (msgs : GMap w32 GoInterface) : IProp netDistGF :=
  iprop(□ ∀ k m, ⌜msgs.lookup k = some m⌝ → P k m ∗ accOk A lm m)

/-- What the handler is called with, over a quorum whose members satisfy `mem`: `handlerPre`
and every key a member. -/
def handlerPreQ (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (lm : GoInterface) (ms : List GoInterface) : IProp netDistGF :=
  iprop(∃ kms : List (w32 × GoInterface), ⌜ms = kms.map Prod.snd ∧ (kms.map Prod.fst).Nodup ∧
      (∀ k ∈ kms.map Prod.fst, mem k) ∧
      (sz ≤ ms.length ∨ (lm ≠ interface.nil ∧ sz ≤ ms.length + 1))⌝ ∗ leaderOk PL lm ∗
    □ (∀ k m, ⌜(k, m) ∈ kms⌝ → P k m ∗ accOk A lm m))

/-- The set's data at `ms` (without the handler's spec): its fields, the messages' map with
their facts, the `accept` and `freeMsg` closures' specs (over the state `RA` they read), and the
handler's value `hd`. What the handler is lent during `Add` (it may free the set: `Free` takes
this). -/
def ownD (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (RA : IProp netDistGF) (hd : GoFunc) : IProp netDistGF :=
  iprop(∃ (v : replica.MsgSet) (msgs : GMap w32 GoInterface),
    ms ↦ v ∗ ⌜v.q' = q ∧ v.handler' = hd ∧ ∀ k, (msgs !! k).isSome → mem k⌝ ∗ quorumIs q sz mem ∗
    v.msgs' ↦$ msgs ∗ leaderOk PL v.leaderMsg' ∗ msgsOk P A v.leaderMsg' msgs ∗
    □ acceptOk v.accept' P A PL RA ∗ □ freeOk v.freeMsg' P PL RA)

/-- The `handler` closure of the set at `ms`, over a quorum whose members satisfy `mem`: it is
lent the set's data (`ownD`) with `R`, and gives back both, or `Rdone` (it finished the set's
owner: SWB-2; `Add` touches the set last before calling the handler). -/
def handlerOkQ (ms : Loc) (q : GoInterface) (hd : GoFunc) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (RA R Rdone : IProp netDistGF) : IProp netDistGF :=
  iprop(∀ (lm : GoInterface) (sl : GoSlice) (msl : List GoInterface),
    {{ R ∗ ownD ms q sz mem P A PL RA hd ∗ sl ↦* msl ∗ handlerPreQ sz mem P A PL lm msl }}
      (App (App (Val #hd) (Val #lm)) (Val #sl))
    {{ RET #(); (R ∗ ownD ms q sz mem P A PL RA hd) ∨ Rdone }})

/-- The closures' specs for the set at `ms`, over a quorum whose members satisfy `mem`. -/
def closuresOkQ (ms : Loc) (q : GoInterface) (acc fr hd : GoFunc) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (RA R Rdone : IProp netDistGF) : IProp netDistGF :=
  iprop(acceptOk acc P A PL RA ∗ freeOk fr P PL RA ∗ handlerOkQ ms q hd sz mem P A PL RA R Rdone)

/-- A message set at `ms` over the quorum `q` (`quorumIs q sz mem`: size `sz`, members `mem`);
the messages' keys are members; its closures read `RA`; its handler is lent `R` (and the set's
data) and gives them back or `Rdone`. -/
def ownQ (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (RA R Rdone : IProp netDistGF) : IProp netDistGF :=
  iprop(∃ hd, ownD ms q sz mem P A PL RA hd ∗ □ handlerOkQ ms q hd sz mem P A PL RA R Rdone)

/-- A message set at `ms` over a majority of size `sz` (the client's sets). -/
def own (ms : Loc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) :
    IProp netDistGF :=
  ownQ ms (interface.mkOk replica.Majority.ty #(W64 sz)) sz (fun _ => True) P A PL R R iprop(False)

instance leaderOk_persistent (PL : GoInterface → IProp netDistGF) (lm : GoInterface) :
    Persistent (leaderOk PL lm) := by unfold leaderOk; infer_instance
instance accOk_persistent (A : GoInterface → GoInterface → IProp netDistGF) (lm m : GoInterface) :
    Persistent (accOk A lm m) := by unfold accOk; infer_instance
instance msgsOk_persistent (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (lm : GoInterface)
    (msgs : GMap w32 GoInterface) : Persistent (msgsOk P A lm msgs) := by
  unfold msgsOk; infer_instance
instance handlerPreQ_persistent (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (lm : GoInterface) (ms : List GoInterface) : Persistent (handlerPreQ sz mem P A PL lm ms) := by
  unfold handlerPreQ; infer_instance
instance handlerPre_persistent (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (lm : GoInterface) (ms : List GoInterface) : Persistent (handlerPre sz P A PL lm ms) := by
  unfold handlerPre; infer_instance

end defs

section specs0
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [π : NetProtoGS]
variable [sem : go.Semantics]

theorem ownD_ne_null (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (R : IProp netDistGF) (hd : GoFunc) : ownD ms q sz mem P A PL R hd ⊢ ⌜ms ≠ null⌝ := by
  unfold ownD
  iintro ⟨%v, %msgs, Hv, -⟩
  iapply typedPointsto_not_null $$ Hv

theorem ownQ_ne_null (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (RA R Rdone : IProp netDistGF) : ownQ ms q sz mem P A PL RA R Rdone ⊢ ⌜ms ≠ null⌝ := by
  unfold ownQ
  iintro ⟨%hd, Hd, -⟩
  iapply ownD_ne_null $$ Hd

/-- The set's handler's spec dropped. -/
theorem ownQ_ownD (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (RA R Rdone : IProp netDistGF) :
    ownQ ms q sz mem P A PL RA R Rdone ⊢ ∃ hd, ownD ms q sz mem P A PL RA hd := by
  unfold ownQ
  iintro ⟨%hd, Hd, -⟩
  iexists hd; iexact Hd

/-- Any set's data: what `ReinitMsgSet` needs of a non-nil set (its fields and map). -/
def ownAny (ms : Loc) : IProp netDistGF :=
  iprop(∃ (v : replica.MsgSet) (msgs : GMap w32 GoInterface), ms ↦ v ∗ v.msgs' ↦$ msgs)

theorem ownD_ownAny (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (R : IProp netDistGF) (hd : GoFunc) : ownD ms q sz mem P A PL R hd ⊢ ownAny ms := by
  unfold ownD ownAny
  iintro ⟨%v, %msgs, Hv, -, -, Hm, -⟩
  iexists v, msgs; iframe Hv Hm

theorem own_ne_null (ms : Loc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (R : IProp netDistGF) : own ms sz P A PL R ⊢ ⌜ms ≠ null⌝ := by
  unfold own
  iapply ownQ_ne_null

end specs0

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]

/-- `NewMsgSet(q, accept, freeMsg, handler)` over a quorum `q` (`quorumIs q sz mem`). -/
abbrev NewMsgSet.specQ : Prop :=
  ∀ (q : GoInterface) (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (RA : IProp netDistGF) (R Rdone : Loc → IProp netDistGF)
    (acc fr hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      quorumIs q sz mem ∗ □ (∀ ms, closuresOkQ ms q acc fr hd sz mem P A PL RA (R ms) (Rdone ms)) }}
    (App (App (App (App (Val (@! replica.NewMsgSet)) (Val #q)) (Val #acc)) (Val #fr)) (Val #hd))
  {{ (ms : Loc), RET #ms; ownQ ms q sz mem P A PL RA (R ms) (Rdone ms) }}

/-- `ms.ReinitMsgSet(q, accept, freeMsg, handler)`: `NewMsgSet` for a nil `ms`, else `ms`
emptied with the new quorum and closures. -/
abbrev MsgSet.ReinitMsgSet.specQ : Prop :=
  ∀ (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (RA : IProp netDistGF) (R Rdone : Loc → IProp netDistGF)
    (acc fr hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      quorumIs q sz mem ∗ □ (∀ ms', closuresOkQ ms' q acc fr hd sz mem P A PL RA (R ms') (Rdone ms')) ∗
      (⌜ms = null⌝ ∨ ownAny ms) }}
    (App (App (App (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"ReinitMsgSet"))
      (Val #q)) (Val #acc)) (Val #fr)) (Val #hd))
  {{ (ms' : Loc), RET #ms'; ownQ ms' q sz mem P A PL RA (R ms') (Rdone ms') }}

omit [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] in
theorem set_mid {α : Type} (l : List α) (n : Nat) (z x : α) (h : 0 < n) :
    (l ++ List.replicate n z).set l.length x = (l ++ [x]) ++ List.replicate (n - 1) z := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [List.set_append_right, List.replicate_succ]

/-- `ms.Add(repId, isLeader, msg)`: a leader message with `PL`, or a message of replica
`repId` with `P repId`; the closures read `RA`, a part of `R`; the handler `hd` may run (with
`R` and the set's data lent): the set and `R` back, or `Rdone` (the handler finished the set's
owner; `Add` touches the set last before calling the handler, SWB-2). The set as `ownD` and its
handler's spec (`ownQ` without the existential: the caller keeps `hd`). -/
abbrev MsgSet.Add.specQ : Prop :=
  ∀ (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (RA R Rdone : IProp netDistGF) (hd : GoFunc) (repId : w32)
    (isLeader : Bool) (msg : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ownD ms q sz mem P A PL RA hd ∗ □ handlerOkQ ms q hd sz mem P A PL RA R Rdone ∗ R ∗
      □ (R -∗ RA ∗ (RA -∗ R)) ∗
      (if isLeader then iprop(⌜msg ≠ interface.nil⌝ ∗ □ PL msg) else iprop(□ P repId msg)) }}
    (App (App (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"Add"))
      (Val #repId)) (Val #isLeader)) (Val #msg))
  {{ (added : Bool), RET #added; ⌜added = true → mem repId⌝ ∗
      ((ownD ms q sz mem P A PL RA hd ∗ R) ∨ Rdone) }}

/-- `ms.Free()`: every message of the set (and its leader message) freed. -/
abbrev MsgSet.Free.specQ : Prop :=
  ∀ (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) (hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      (⌜ms = null⌝ ∨ ownD ms q sz mem P A PL R hd) ∗ R }}
    (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"Free")) (Val #()))
  {{ RET #(); R ∗ (⌜ms = null⌝ ∨ ownD ms q sz mem P A PL R hd) }}

/-! ## The majority instances (the client's message sets) -/

theorem quorumIs_majority (sz : Nat) (h : sz < 2 ^ 62) :
    ⊢ quorumIs (interface.mkOk replica.Majority.ty #(W64 sz)) sz (fun _ => True) := by
  unfold quorumIs
  iintro
  isplitr
  · ipureintro; exact h
  ileft; ipureintro; exact ⟨Or.inl rfl, fun _ => trivial⟩

theorem handlerPreQ_handlerPre (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (lm : GoInterface) (ms : List GoInterface) :
    handlerPreQ sz mem P A PL lm ms ⊢ handlerPre sz P A PL lm ms := by
  unfold handlerPreQ handlerPre
  iintro ⟨%kms, %Hk, #HL, #Hm⟩
  iexists kms
  iframe HL Hm
  ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2.2⟩

/-- A handler for the majority's sets serves any membership. -/
theorem closuresOk_Q (acc fr hd : GoFunc) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
    (R : IProp netDistGF) (ms : Loc) (q : GoInterface) :
    closuresOk acc fr hd sz P A PL R ⊢ closuresOkQ ms q acc fr hd sz mem P A PL R R iprop(False) := by
  unfold closuresOk closuresOkQ handlerOk handlerOkQ
  iintro ⟨Ha, Hf, #Hh⟩
  iframe Ha Hf
  iintro %lm %sl %msl
  imodintro
  iintro %Φ ⟨HR, Hd, Hsl, #Hpre⟩ HΦ
  ihave #Hpre' := handlerPreQ_handlerPre $$ Hpre
  iapply Hh $$ [HR Hsl Hpre']
  · iframe HR Hsl Hpre'
  inext; iintro HR
  iapply HΦ; ileft; iframe HR Hd

/-- `NewMsgSet(q, accept, freeMsg, handler)` with `q` a majority of size `sz`. -/
abbrev NewMsgSet.specI : Prop :=
  ∀ (sz : Nat) (P : w32 → GoInterface → IProp netDistGF) (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) (acc fr hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ⌜sz < 2 ^ 62⌝ ∗ □ closuresOk acc fr hd sz P A PL R }}
    (App (App (App (App (Val (@! replica.NewMsgSet))
      (Val #(interface.mkOk replica.Majority.ty #(W64 sz)))) (Val #acc)) (Val #fr)) (Val #hd))
  {{ (ms : Loc), RET #ms; own ms sz P A PL R }}

/-- `ms.ReinitMsgSet(q, accept, freeMsg, handler)` with `q` a majority of size `sz`. -/
abbrev MsgSet.ReinitMsgSet.specI : Prop :=
  ∀ (ms : Loc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) (acc fr hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ⌜sz < 2 ^ 62⌝ ∗ □ closuresOk acc fr hd sz P A PL R ∗
      (⌜ms = null⌝ ∨ ∃ sz' P' A' PL' R', own ms sz' P' A' PL' R') }}
    (App (App (App (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"ReinitMsgSet"))
      (Val #(interface.mkOk replica.Majority.ty #(W64 sz)))) (Val #acc)) (Val #fr)) (Val #hd))
  {{ (ms' : Loc), RET #ms'; own ms' sz P A PL R }}

/-- `ms.Add(repId, isLeader, msg)` on a majority's set. -/
abbrev MsgSet.Add.specI : Prop :=
  ∀ (ms : Loc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) (repId : w32) (isLeader : Bool)
    (msg : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      own ms sz P A PL R ∗ R ∗
      (if isLeader then iprop(⌜msg ≠ interface.nil⌝ ∗ □ PL msg) else iprop(□ P repId msg)) }}
    (App (App (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"Add"))
      (Val #repId)) (Val #isLeader)) (Val #msg))
  {{ (added : Bool), RET #added; own ms sz P A PL R ∗ R }}

/-- `ms.Free()` on a majority's set. -/
abbrev MsgSet.Free.specI : Prop :=
  ∀ (ms : Loc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      (⌜ms = null⌝ ∨ own ms sz P A PL R) ∗ R }}
    (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"Free")) (Val #()))
  {{ RET #(); R }}

/-! ## Round 22 (sv-swb): the forms with the handler's value `hd` exposed (`ownD`)

`newDesc` creates its two sets with one handler whose lent state mentions both sets' locations,
so it cannot be fixed at `ReinitMsgSet`'s call (the second set does not exist yet); these forms
give the set's data with the given `hd` (no handler spec), and the caller states the handler's
spec afterwards. -/

/-- `NewMsgSet(q, accept, freeMsg, handler)`: the set's data with handler `hd`. -/
abbrev NewMsgSet.specD : Prop :=
  ∀ (q : GoInterface) (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (RA : IProp netDistGF) (acc fr hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      quorumIs q sz mem ∗ □ acceptOk acc P A PL RA ∗ □ freeOk fr P PL RA }}
    (App (App (App (App (Val (@! replica.NewMsgSet)) (Val #q)) (Val #acc)) (Val #fr)) (Val #hd))
  {{ (ms : Loc), RET #ms; ownD ms q sz mem P A PL RA hd }}

/-- `ms.ReinitMsgSet(q, accept, freeMsg, handler)`: the set's data with handler `hd`. -/
abbrev MsgSet.ReinitMsgSet.specD : Prop :=
  ∀ (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (RA : IProp netDistGF) (acc fr hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      quorumIs q sz mem ∗ □ acceptOk acc P A PL RA ∗ □ freeOk fr P PL RA ∗
      (⌜ms = null⌝ ∨ ownAny ms) }}
    (App (App (App (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"ReinitMsgSet"))
      (Val #q)) (Val #acc)) (Val #fr)) (Val #hd))
  {{ (ms' : Loc), RET #ms'; ownD ms' q sz mem P A PL RA hd }}

end specs

end replica.mset

end Perennial.github_com.imdea_software.swiftpaxos
