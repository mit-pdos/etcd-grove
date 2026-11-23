/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/MsgSet.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica.MsgSet` (replica/mset.go), the client group's internal spec: a message set over a
majority quorum of size `sz`, whose non-leader messages (keyed by replica id `k`) satisfy
`P k m` and, once a leader message `lm` is set, `A lm m` (the `accept` closure's guarantee),
and whose leader message satisfies `PL`. The closures' specs (`acceptOk`, `freeOk`,
`handlerOk`) pass the caller's state `R` through. All the facts kept are persistent (`□`).

General form (`ownQ`, `*.specQ`): over any `QuorumI` value the replica uses (`quorumIs q sz mem`,
MsgSetQ.lean: a `Majority` or `ThreeQuarters` of size `sz`, every id a member, or a `Quorum`
`qOwn ql □ s` of size `sz = len s`, members `s`); the set's keys are members (`Add` adds a
message only if `q.Contains(repId)`), `handlerPreQ` says so, `Add` returns `added → mem repId`.
The majority forms (`own`, `*.specI`, the client's) are corollaries (`closuresOk_Q`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSetQ
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
variable [hG : HeapGS HasLC.hasLC netDistGF]
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
variable [hG : HeapGS HasLC.hasLC netDistGF]
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
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF]

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

theorem NewMsgSet.wp_proofQ : NewMsgSet.specQ (hG := hG) := by
  intro q sz mem P A PL RA R Rdone acc fr hd
  wp_start as ⟨#Hq, #Hcl⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoInterface)) as %mref Hm
  iapply HΦ
  ihave #Hcl1 := Hcl $$ %(«$r0_ptr» : Loc)
  iunfold closuresOkQ at Hcl1
  icases Hcl1 with ⟨#Hacc, #Hfree, #Hhd⟩
  unfold ownQ ownD
  iexists hd; iframe Hhd; iexists _, ∅
  iframe «$r0» Hm Hacc Hfree Hq
  isplitr
  · ipureintro; refine ⟨rfl, rfl, ?_⟩; intro k hk; simp at hk
  isplitr
  · unfold leaderOk; ileft; ipureintro; rfl
  unfold msgsOk
  imodintro
  iintro %k %m %Hk
  simp at Hk

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

theorem MsgSet.ReinitMsgSet.wp_proofQ (wp_New : NewMsgSet.specQ (hG := hG)) :
    MsgSet.ReinitMsgSet.specQ (hG := hG) := by
  intro ms q sz mem P A PL RA R Rdone acc fr hd
  wp_start as ⟨#Hqi, #Hcl, Hms⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_New $$ [$Hcl $Hqi] as %ms' Hms'
    iapply HΦ $$ Hms'
  icases Hms with (%Hnull | Hms)
  · exact absurd Hnull Hif
  unfold ownAny
  icases Hms with ⟨%v, %msgs, Hv, Hm⟩
  wp_auto
  isimp at Hv
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_mut_keys (fun keys i m' => iprop(
      ⌜∀ k, (m'.lookup k).isSome → ∃ j, i ≤ j ∧ keys[j]? = some k⌝ ∗
      (∃ r : w32, rep_ptr ↦ r) ∗ ms_ptr ↦ ms ∗
      ms ↦ replica.MsgSet.mk q v.msgs' GoInterface.nil acc fr hd))) $$ Hm
  iintro %keys %Hkeys
  isplitl [rep ms Hv]
  · iframe ms Hv
    isplitr
    · ipureintro
      intro k hk
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((Hkeys.1 k).2 hk)
      exact ⟨j, Nat.zero_le _, hj⟩
    · iexists _; iexact rep
  isplitl []
  · imodintro
    iintro %i %key %x %m' ⟨%Hi1, %Hi2, %Hi3⟩ ⟨%Hinv, ⟨%r, rep⟩, ms, Hv⟩ Hm
    wp_auto
    wp_apply (wp_mapDelete (K := w32) (V := GoInterface)) $$ [$Hm] as Hm
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists _
    iframe Hm ms Hv
    isplitl [rep]
    · isplitr
      · ipureintro
        intro k hk
        by_cases hkk : k = key
        · subst hkk; simp at hk
        · have hk' : (m' !! k).isSome = true := by
            rwa [GMap.lookup_delete_ne] at hk; exact Ne.symm hkk
          obtain ⟨j, hj1, hj2⟩ := Hinv k hk'
          refine ⟨j, ?_, hj2⟩
          rcases Nat.lt_or_eq_of_le hj1 with h | h
          · exact h
          · subst h; rw [Hi1] at hj2; cases hj2; exact absurd rfl hkk
      · iexists _; iexact rep
    ipureintro
    intro k hk
    exact GMap.lookup_delete_ne _ (Ne.symm hk)
  iintro %m' ⟨%Hinv, ⟨%r, rep⟩, ms, Hv⟩ Hm
  wp_auto
  iapply HΦ
  ihave #Hcl1 := Hcl $$ %ms
  iunfold closuresOkQ at Hcl1
  icases Hcl1 with ⟨#Hacc, #Hfree, #Hhd⟩
  unfold ownQ ownD
  iexists hd; iframe Hhd; iexists _, m'
  iframe Hv Hm Hacc Hfree Hqi
  isplitr
  · ipureintro; simp only; refine ⟨by trivial, by trivial, ?_⟩
    intro k hk
    obtain ⟨j, hj1, hj2⟩ := Hinv k (by simpa using hk)
    have := List.getElem?_eq_none_iff.mpr hj1
    rw [this] at hj2; cases hj2
  isplitr
  · unfold leaderOk; ileft; ipureintro; rfl
  unfold msgsOk
  imodintro
  iintro %k %m %Hk
  obtain ⟨j, hj1, hj2⟩ := Hinv k (by simp [Hk])
  have := List.getElem?_eq_none_iff.mpr hj1
  rw [this] at hj2; cases hj2
  done

omit [replica.Assumptions] [SwiftNetPkgState netDistGF] in
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

theorem MsgSet.Add.wp_proofQ : MsgSet.Add.specQ (hG := hG) := by
  intro ms q sz mem P A PL RA R Rdone hd repId isLeader msg
  wp_start as ⟨Hown, #Hhd, HR, #HRA, Hmsg⟩
  unfold ownD
  icases Hown with ⟨%v, %msgs, Hv, %Hq, #Hqi, Hm, #HL, #Hmsgs, #Hacc, #Hfree⟩
  obtain ⟨Hq, Hhdv, Hmem⟩ := Hq
  ihave %Hsz := quorumIs_sz $$ Hqi
  ihave %Hok := quorumIs_ok $$ Hqi
  obtain ⟨i, rfl⟩ := Hok
  wp_auto
  rw [Hq]
  wp_auto
  wp_apply wp_qContains i sz mem repId $$ [$Hqi] as %bc %Hbc
  cases bc
  · wp_auto
    iapply HΦ
    isplitr
    · ipureintro; intro h; cases h
    ileft; iframe HR
    iexists v, msgs
    iframe Hv Hm HL Hmsgs Hacc Hfree Hqi
    ipureintro; exact ⟨Hq, Hhdv, Hmem⟩
  have hmr : mem repId := Hbc rfl
  wp_auto
  wp_apply (wp_map_lookup2 (K := w32) (V := GoInterface)) $$ [$Hm] as Hm
  wp_join (v := #(!decide (v.leaderMsg' = GoInterface.nil))) iprop(True) at (GoUnOp GoNot go.bool _)
  · split <;> first | (exfalso; simp_all; done) | (wp_pures; isplitr; ipureintro; simp_all; itrivial)
  iintro -
  by_cases hseen : v.leaderMsg' ≠ GoInterface.nil ∧ (msgs !! repId).isSome = true
  · rw [decide_eq_false hseen.1]
    wp_auto
    rw [decide_eq_true hseen.2]
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; intro h; cases h
    ileft; iframe HR
    iexists v, msgs
    iframe Hv Hm HL Hmsgs Hacc Hfree Hqi
    ipureintro; exact ⟨Hq, Hhdv, Hmem⟩
  wp_join at (if: (if: _ then _ else _) then _ else _) with [seen]
  · by_cases hl : v.leaderMsg' = GoInterface.nil
    · rw [decide_eq_true hl]; wp_auto; wp_join_done
    · rw [decide_eq_false hl]; wp_auto
      rw [decide_eq_false (fun h => hseen ⟨hl, h⟩)]; wp_auto; wp_join_done
  ihave #Hacc0 := Hacc
  ihave #Hfree0 := Hfree
  iunfold acceptOk at Hacc
  iunfold freeOk at Hfree
  ihave ⟨HR, HRback⟩ := HRA $$ HR
  wp_join iprop(∃ (v' : replica.MsgSet) (msgs' : GMap w32 GoInterface) (a : Bool),
      ms ↦ v' ∗ ⌜v'.q' = v.q' ∧ v'.accept' = v.accept' ∧ v'.freeMsg' = v.freeMsg' ∧
        v'.handler' = v.handler' ∧ (a = true → mem repId) ∧
        ∀ k, (msgs' !! k).isSome → mem k⌝ ∗
      v'.msgs' ↦$ msgs' ∗ leaderOk PL v'.leaderMsg' ∗ msgsOk P A v'.leaderMsg' msgs' ∗ RA ∗
      added_ptr ↦ a ∗ ms_ptr ↦ ms)
    with [Hv Hm HR added Hmsg msg ms repId]
    as ⟨%v', %msgs', %a, Hv, %Hv', Hm, #HL', #Hmsgs', HR, added, ms⟩
  · -- a message of replica `repId`
    icases Hmsg with #Hmsg
    wp_bind (App (App (Val #v.accept') _) _)
    iapply Hacc $$ [HR]
    · iframe HR; iframe #
    inext
    iintro %b ⟨HR, #Hb⟩
    wp_if_destruct
    · wp_bind (App (Val #v.freeMsg') _)
      iapply Hfree $$ [HR]
      · iframe HR; ileft; iexists repId; iframe #
      inext; iintro HR
      wp_auto
      wp_join_done
      iexists v, msgs, false
      iframe Hv Hm HR added ms HL Hmsgs
      ipureintro; exact ⟨rfl, rfl, rfl, rfl, fun h => absurd h (by decide), Hmem⟩
    · wp_apply (wp_mapInsert (K := w32) (V := GoInterface)) $$ [$Hm] as Hm
      wp_join_done
      iexists v, (msgs.insert repId msg), true
      iframe Hv Hm HR added ms HL
      isplitr
      · ipureintro
        refine ⟨rfl, rfl, rfl, rfl, fun _ => hmr, ?_⟩
        intro k hk
        by_cases hkr : k = repId
        · subst hkr; exact hmr
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkr)] at hk; exact Hmem k hk
      unfold msgsOk
      imodintro
      iintro %k %m %Hk
      by_cases hk : k = repId
      · subst hk
        rw [GMap.lookup_insert_eq] at Hk; cases Hk
        iframe Hmsg
        iapply Hb; ipureintro; trivial
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at Hk
        iapply Hmsgs; ipureintro; exact Hk
  · -- the leader message
    icases Hmsg with ⟨%Hnn, #Hmsg⟩
    iunfold msgsOk at Hmsgs
    wp_apply (wp_map_make1 (K := w32) (V := GoInterface)) as %nmref Hnm
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range (fun _ _ => iprop(∃ (nm : GMap w32 GoInterface) (fm : GoInterface)
        (fr : w32), nmref ↦$ nm ∗ ⌜∀ k, (nm !! k).isSome → mem k⌝ ∗ msgsOk P A msg nm ∗ RA ∗ fmsg_ptr ↦ fm ∗ frepId_ptr ↦ fr ∗
        newMsgs_ptr ↦ nmref ∗ ms_ptr ↦ ms ∗
        ms ↦ ({ v with leaderMsg' := msg } : replica.MsgSet)))) $$ Hm
    iintro %keys %Hkeys
    isplitl [Hnm HR fmsg frepId newMsgs ms Hv]
    · iexists ∅, _, _
      iframe Hnm HR fmsg frepId newMsgs ms Hv
      isplitr
      · ipureintro; intro k hk; simp at hk
      unfold msgsOk
      imodintro
      iintro %k %m %Hk
      simp at Hk
    isplitl []
    · imodintro
      iintro %i %key %x ⟨%Hi1, %Hi2⟩ ⟨%nm, %fm, %fr, Hnm, %Hnmm, #Hnms, HR, fmsg, frepId, newMsgs, ms, Hv⟩
      wp_auto
      wp_apply (wp_map_lookup2 (K := w32) (V := GoInterface)) $$ [$Hnm] as Hnm
      ihave #Hx := Hmsgs $$ %key %x %Hi2
      icases Hx with ⟨#HPx, -⟩
      by_cases hs : (nm !! key).isSome = true
      · rw [decide_eq_true hs]
        wp_auto
        wp_bind (App (Val #v.freeMsg') _)
        iapply Hfree $$ [HR]
        · iframe HR; ileft; iexists key; iframe #
        inext; iintro HR
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr; · ipureintro; rfl
        iexists nm, x, key
        iframe
        isplitr
        · ipureintro; exact Hnmm
        iexact Hnms
      rw [decide_eq_false hs]
      wp_auto
      wp_bind (App (App (Val #v.accept') _) _)
      iapply Hacc $$ [HR]
      · iframe HR; iframe HPx; unfold leaderOk; iright; iframe #
      inext
      iintro %b ⟨HR, #Hb⟩
      wp_if_destruct
      · wp_bind (App (Val #v.freeMsg') _)
        iapply Hfree $$ [HR]
        · iframe HR; ileft; iexists key; iframe #
        inext; iintro HR
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr; · ipureintro; rfl
        iexists nm, x, key
        iframe
        isplitr
        · ipureintro; exact Hnmm
        iexact Hnms
      wp_apply (wp_mapInsert (K := w32) (V := GoInterface)) $$ [$Hnm] as Hnm
      unfold forMapPostcondition
      iright; ileft
      isplitr; · ipureintro; rfl
      iexists (nm.insert key x), x, key
      iframe
      isplitr
      · ipureintro
        intro k hk
        by_cases hkk : k = key
        · subst hkk; exact Hmem k (by simp [Hi2])
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hk; exact Hnmm k hk
      unfold msgsOk
      imodintro
      iintro %k %m %Hk
      by_cases hk : k = key
      · subst hk
        rw [GMap.lookup_insert_eq] at Hk; cases Hk
        iframe HPx
        iapply Hb; ipureintro; trivial
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at Hk
        iapply Hnms; ipureintro; exact Hk
    iintro ⟨%nm, %fm, %fr, Hnm, %Hnmm, #Hnms, HR, fmsg, frepId, newMsgs, ms, Hv⟩ Hm
    wp_auto
    wp_join_done
    isimp at Hv
    iexists _, nm, true
    iframe Hv Hnm HR added ms Hnms
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl, fun _ => hmr, Hnmm⟩
    unfold leaderOk; iright; iframe #
  obtain ⟨hq', hacc', hfr', hhd', hadd, hmem'⟩ := Hv'
  ihave HR := HRback $$ HR
  wp_join (v := #(decide (sz ≤ msgs'.size) ||
      (decide (sz ≤ msgs'.size + 1) && !decide (v'.leaderMsg' = GoInterface.nil))))
    at ((Convert go.untypedBool go.bool) _) with [Hm Hv ms]
  · wp_apply (wp_map_len_lt (K := w32) (V := GoInterface)) $$ [$Hm] as ⟨Hm, %Hlen⟩
    rw [hq', Hq]
    wp_auto
    wp_apply wp_qSize i sz mem $$ [$Hqi]
    try wp_auto
    by_cases h1 : sz ≤ msgs'.size
    · rw [decide_eq_true (show sint.Z (W64 sz) ≤ sint.Z (W64 msgs'.size) by word)]
      wp_auto
      simp only [decide_eq_true h1, Bool.true_or]
      wp_join_done
    rw [decide_eq_false (show ¬ sint.Z (W64 sz) ≤ sint.Z (W64 msgs'.size) by word)]
    wp_auto
    wp_apply (wp_map_len_lt (K := w32) (V := GoInterface)) $$ [$Hm] as ⟨Hm, -⟩
    rw [hq', Hq]
    wp_auto
    wp_apply wp_qSize i sz mem $$ [$Hqi]
    try wp_auto
    by_cases h2 : sz ≤ msgs'.size + 1
    · rw [decide_eq_true (show sint.Z (W64 sz - W64 1) ≤ sint.Z (W64 msgs'.size) by word)]
      wp_auto
      split <;> first | (exfalso; simp_all; done) |
        (wp_pures; isplitr; (ipureintro; congr 1; simp_all); iframe)
    · rw [decide_eq_false (show ¬ sint.Z (W64 sz - W64 1) ≤ sint.Z (W64 msgs'.size) by word)]
      wp_auto
      simp only [decide_eq_false h1, decide_eq_false h2, Bool.false_or, Bool.false_and]
      wp_join_done
  generalize hthr : (decide (sz ≤ msgs'.size) ||
      (decide (sz ≤ msgs'.size + 1) && !decide (v'.leaderMsg' = GoInterface.nil))) = thr
  cases thr
  · wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact hadd
    ileft; iframe HR
    iexists v', msgs'
    iframe Hv Hm HL' Hmsgs' Hqi
    rw [hacc', hfr']
    iframe Hacc0 Hfree0
    ipureintro; exact ⟨hq'.trans Hq, hhd'.trans Hhdv, hmem'⟩
  wp_auto
  wp_apply (wp_map_len_lt (K := w32) (V := GoInterface)) $$ [$Hm] as ⟨Hm, %Hlen⟩
  wp_apply wp_slice_make2 as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun keys i => iprop(∃ kms : List (w32 × GoInterface),
      ⌜kms.map Prod.fst = keys.take i.toNat ∧ kms.length = i.toNat ∧ 0 ≤ i ∧
        ∀ k m, (k, m) ∈ kms → msgs' !! k = some m⌝ ∗
      i_ptr ↦ W64 i ∗ sl ↦* (kms.map Prod.snd ++
        List.replicate (msgs'.size - i.toNat) (zero_val GoInterface)) ∗
      (∃ x : GoInterface, v_ptr ↦ x) ∗ m_ptr ↦ sl))) $$ Hm
  iintro %keys %Hkeys
  isplitl [i Hsl v m]
  · iexists []
    simp only [List.map_nil, List.nil_append, List.take_zero, List.length_nil]
    iframe i m
    isplitr
    · ipureintro; simp
    isplitl [Hsl]
    · iExactEq Hsl; congr 1; simp; word
    iexists _; iexact v
  isplitl []
  · imodintro
    iintro %i %key %x ⟨%Hi1, %Hi2⟩ ⟨%kms, ⟨%Hk1, %Hk2, %Hk3, %Hk4⟩, i, Hsl, ⟨%y, v⟩, m⟩
    wp_auto
    have hilt : i.toNat < keys.length := by
      rcases Nat.lt_or_ge i.toNat keys.length with h | h
      · exact h
      · rw [List.getElem?_eq_none_iff.mpr h] at Hi1; cases Hi1
    ihave %Hsll := ownSlice_len $$ Hsl
    simp only [List.length_append, List.length_map, List.length_replicate] at Hsll
    have hsize : keys.length = msgs'.size := Hkeys.2.1
    rw [if_pos (by constructor <;> word)]
    wp_apply (wp_store_slice_index (V := GoInterface)) $$ [$Hsl] as Hsl
    · ipureintro; simp only [List.length_append, List.length_map, List.length_replicate]; word
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists kms ++ [(key, x)]
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil, Hk1]
        have : (i + 1).toNat = i.toNat + 1 := by omega
        rw [this, List.take_succ, Hi1]; rfl
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · omega
      · intro k m hkm
        rcases List.mem_append.mp hkm with h | h
        · exact Hk4 k m h
        · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, _root_.or_false] at h
          obtain ⟨rfl, rfl⟩ := h; exact Hi2
    iframe m
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [Hsl]
    · iExactEq Hsl; congr 1
      have hiub : i < 2 ^ 63 := by omega
      have hi64 : sint.Z (W64 i) = i := by word
      have hk : (sint.Z (W64 i)).toNat = (List.map Prod.snd kms).length := by
        rw [hi64, List.length_map]; omega
      rw [hk, set_mid _ _ _ _ (by omega)]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]
      have h3 : msgs'.size - i.toNat - 1 = msgs'.size - (i + 1).toNat := by omega
      rw [h3]
    iexists _; iexact v
  iintro ⟨%kms, ⟨%Hk1, %Hk2, %Hk3, %Hk4⟩, i, Hsl, ⟨%y, v⟩, m⟩ Hm
  wp_auto
  rw [hhd']
  have hsize : keys.length = msgs'.size := Hkeys.2.1
  have hsl : List.map Prod.snd kms ++
      List.replicate (msgs'.size - (GMap.size msgs' : Int).toNat) (zero_val GoInterface) =
      kms.map Prod.snd := by simp
  rw [hsl, Hhdv]
  wp_bind (App (App (Val #hd) _) _)
  iunfold handlerOkQ at Hhd
  iapply Hhd $$ [HR Hsl Hv Hm]
  · iframe HR Hsl
    isplitl [Hv Hm]
    · unfold ownD
      iexists v', msgs'
      iframe Hv Hm HL' Hmsgs' Hqi
      rw [hacc', hfr']
      iframe Hacc0 Hfree0
      ipureintro; exact ⟨hq'.trans Hq, hhd'.trans Hhdv, hmem'⟩
    unfold handlerPreQ
    iexists kms
    iframe HL'
    isplitr
    · ipureintro
      have hk : kms.map Prod.fst = keys := by rw [Hk1]; apply List.take_of_length_le; omega
      refine ⟨rfl, hk ▸ Hkeys.2.2, ?_, ?_⟩
      · intro k hk'
        obtain ⟨⟨k', m'⟩, hkm, rfl⟩ := List.mem_map.mp hk'
        exact hmem' k' (by simp [Hk4 k' m' hkm])
      have hlen : (kms.map Prod.snd).length = msgs'.size := by simp; omega
      rw [hlen]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hthr
      rcases hthr with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩
    imodintro
    iintro %k %m %hkm
    unfold msgsOk
    iapply Hmsgs'
    ipureintro; exact Hk4 k m hkm
  inext
  iintro HR
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact hadd
  icases HR with (⟨HR, Hd⟩ | Hdone)
  · ileft; iframe HR
    iunfold ownD at Hd; iframe Hd
  · iright; iexact Hdone

/-- `ms.Free()`: every message of the set (and its leader message) freed. -/
abbrev MsgSet.Free.specQ : Prop :=
  ∀ (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF) (hd : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      (⌜ms = null⌝ ∨ ownD ms q sz mem P A PL R hd) ∗ R }}
    (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"Free")) (Val #()))
  {{ RET #(); R ∗ (⌜ms = null⌝ ∨ ownD ms q sz mem P A PL R hd) }}

theorem MsgSet.Free.wp_proofQ : MsgSet.Free.specQ (hG := hG) := by
  intro ms q sz mem P A PL R hd
  wp_start as ⟨Hms, HR⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ; iframe HR; ileft; ipureintro; trivial
  icases Hms with (%Hnull | Hown)
  · exact absurd Hnull Hif
  unfold ownD
  icases Hown with ⟨%v, %msgs, Hv, %Hq, #Hqi, Hm, #HL, #Hmsgs, #Hacc, #Hfree⟩
  ihave #Hfree0 := Hfree
  ihave #Hmsgs0 := Hmsgs
  iunfold freeOk at Hfree
  iunfold msgsOk at Hmsgs
  wp_auto
  wp_join at next with [HR Hv ms]
  · split
    · wp_auto; wp_join_done
    · rename_i heq1 heq2; cases heq2
    · rename_i heq1 _ _; wp_auto
      wp_bind (App (Val #v.freeMsg') _)
      iapply Hfree $$ [HR]
      · iframe HR; iright
        unfold leaderOk
        icases HL with (%Hn | #HL)
        · cases v.leaderMsg' <;> simp_all
        · iexact HL
      inext; iintro HR
      wp_auto; wp_join_done
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun _ _ => iprop(R ∗ (∃ x : GoInterface, fmsg_ptr ↦ x) ∗
      ms_ptr ↦ ms ∗ ms ↦ v))) $$ Hm
  iintro %keys %Hkeys
  isplitl [HR fmsg ms Hv]
  · iframe HR ms Hv; iexists _; iexact fmsg
  isplitl []
  · imodintro
    iintro %i %key %x ⟨%Hi1, %Hi2⟩ ⟨HR, ⟨%y, fmsg⟩, ms, Hv⟩
    wp_auto
    ihave #Hx := Hmsgs $$ %key %x %Hi2
    icases Hx with ⟨#HPx, -⟩
    split
    · wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr; · ipureintro; rfl
      iframe HR ms Hv; iexists _; iexact fmsg
    · rename_i heq1 heq2; cases heq2
    · wp_auto
      wp_bind (App (Val #v.freeMsg') _)
      iapply Hfree $$ [HR]
      · iframe HR; ileft; iexists key; iexact HPx
      inext; iintro HR
      wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr; · ipureintro; rfl
      iframe HR ms Hv; iexists _; iexact fmsg
  iintro ⟨HR, ⟨%y, fmsg⟩, ms, Hv⟩ Hm
  wp_auto
  iapply HΦ; iframe HR; iright
  iexists v, msgs
  iframe Hv Hm HL Hmsgs0 Hqi Hacc Hfree0
  ipureintro; exact Hq

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

theorem NewMsgSet.wp_proof : NewMsgSet.specI (hG := hG) := by
  intro sz P A PL R acc fr hd
  iintro %Φ ⟨#Hpkg, %Hsz, #Hcl⟩ HΦ
  ihave #Hq := quorumIs_majority sz Hsz
  unfold own
  iapply (NewMsgSet.wp_proofQ _ sz (fun _ => True) P A PL R (fun _ => R) (fun _ => iprop(False))
    acc fr hd) $$ [Hpkg Hq Hcl] HΦ
  iframe Hpkg Hq
  imodintro; iintro %ms
  iapply closuresOk_Q $$ Hcl

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

theorem MsgSet.ReinitMsgSet.wp_proof (wp_New : NewMsgSet.specQ (hG := hG)) :
    MsgSet.ReinitMsgSet.specI (hG := hG) := by
  intro ms sz P A PL R acc fr hd
  iintro %Φ ⟨#Hpkg, %Hsz, #Hcl, Hms⟩ HΦ
  ihave #Hq := quorumIs_majority sz Hsz
  unfold own
  iapply (MsgSet.ReinitMsgSet.wp_proofQ wp_New ms _ sz (fun _ => True) P A PL R (fun _ => R)
    (fun _ => iprop(False)) acc fr hd) $$ [Hpkg Hq Hcl Hms] HΦ
  iframe Hpkg Hq
  isplitr
  · imodintro; iintro %ms'
    iapply closuresOk_Q $$ Hcl
  icases Hms with (%Hn | ⟨%sz', %P', %A', %PL', %R', Hms⟩)
  · ileft; ipureintro; exact Hn
  · iright
    ihave ⟨%hd', Hd⟩ := ownQ_ownD $$ Hms
    iapply ownD_ownAny $$ Hd

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

theorem MsgSet.Add.wp_proof : MsgSet.Add.specI (hG := hG) := by
  intro ms sz P A PL R repId isLeader msg
  iintro %Φ ⟨#Hpkg, Hown, HR, Hmsg⟩ HΦ
  iunfold own at Hown
  iunfold ownQ at Hown
  icases Hown with ⟨%hd, Hown, #Hhd⟩
  iapply (MsgSet.Add.wp_proofQ ms (interface.mkOk replica.Majority.ty #(W64 sz)) sz (fun _ => True) P A PL R R
    iprop(False) hd repId isLeader msg)
    $$ [Hpkg Hown HR Hmsg]
  · iframe Hpkg Hown HR Hmsg Hhd
    imodintro; iintro HR; iframe HR; iintro HR; iexact HR
  inext
  iintro %added ⟨-, (⟨Hown, HR⟩ | %Hf)⟩
  · iapply HΦ
    unfold own ownQ
    iframe HR
    iexists hd; iframe Hown Hhd
  · exact Hf.elim

/-- `ms.Free()` on a majority's set. -/
abbrev MsgSet.Free.specI : Prop :=
  ∀ (ms : Loc) (sz : Nat) (P : w32 → GoInterface → IProp netDistGF)
    (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (R : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      (⌜ms = null⌝ ∨ own ms sz P A PL R) ∗ R }}
    (App (Val (ms @!! go.GoType.PointerType replica.MsgSet.ty @!! go!"Free")) (Val #()))
  {{ RET #(); R }}

theorem MsgSet.Free.wp_proof : MsgSet.Free.specI (hG := hG) := by
  intro ms sz P A PL R
  iintro %Φ ⟨#Hpkg, Hms, HR⟩ HΦ
  iunfold own at Hms
  icases Hms with (%Hn | Hms)
  · iapply (MsgSet.Free.wp_proofQ ms (interface.mkOk replica.Majority.ty #(W64 sz)) sz (fun _ => True) P A PL R func.nil) $$ [Hpkg HR]
    · iframe Hpkg HR; ileft; ipureintro; exact Hn
    inext; iintro ⟨HR, -⟩; iapply HΦ $$ HR
  ihave ⟨%hd, Hd⟩ := ownQ_ownD $$ Hms
  iapply (MsgSet.Free.wp_proofQ ms (interface.mkOk replica.Majority.ty #(W64 sz)) sz (fun _ => True) P A PL R hd) $$ [Hpkg Hd HR]
  · iframe Hpkg HR; iright; iexact Hd
  inext; iintro ⟨HR, -⟩; iapply HΦ $$ HR



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

theorem NewMsgSet.wp_proofD : NewMsgSet.specD (hG := hG) := by
  intro q sz mem P A PL RA acc fr hd
  wp_start as ⟨#Hq, #Hacc, #Hfree⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoInterface)) as %mref Hm
  iapply HΦ
  unfold ownD
  iexists _, ∅
  iframe «$r0» Hm Hacc Hfree Hq
  isplitr
  · ipureintro; refine ⟨rfl, rfl, ?_⟩; intro k hk; simp at hk
  isplitr
  · unfold leaderOk; ileft; ipureintro; rfl
  unfold msgsOk
  imodintro
  iintro %k %m %Hk
  simp at Hk

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

theorem MsgSet.ReinitMsgSet.wp_proofD : MsgSet.ReinitMsgSet.specD (hG := hG) := by
  intro ms q sz mem P A PL RA acc fr hd
  wp_start as ⟨#Hqi, #Hacc, #Hfree, Hms⟩
  wp_auto
  wp_if_destruct
  · wp_apply NewMsgSet.wp_proofD $$ [$Hacc $Hfree $Hqi] as %ms' Hms'
    iapply HΦ $$ Hms'
  icases Hms with (%Hnull | Hms)
  · exact absurd Hnull Hif
  unfold ownAny
  icases Hms with ⟨%v, %msgs, Hv, Hm⟩
  wp_auto
  isimp at Hv
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_mut_keys (fun keys i m' => iprop(
      ⌜∀ k, (m'.lookup k).isSome → ∃ j, i ≤ j ∧ keys[j]? = some k⌝ ∗
      (∃ r : w32, rep_ptr ↦ r) ∗ ms_ptr ↦ ms ∗
      ms ↦ replica.MsgSet.mk q v.msgs' GoInterface.nil acc fr hd))) $$ Hm
  iintro %keys %Hkeys
  isplitl [rep ms Hv]
  · iframe ms Hv
    isplitr
    · ipureintro
      intro k hk
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((Hkeys.1 k).2 hk)
      exact ⟨j, Nat.zero_le _, hj⟩
    · iexists _; iexact rep
  isplitl []
  · imodintro
    iintro %i %key %x %m' ⟨%Hi1, %Hi2, %Hi3⟩ ⟨%Hinv, ⟨%r, rep⟩, ms, Hv⟩ Hm
    wp_auto
    wp_apply (wp_mapDelete (K := w32) (V := GoInterface)) $$ [$Hm] as Hm
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists _
    iframe Hm ms Hv
    isplitl [rep]
    · isplitr
      · ipureintro
        intro k hk
        by_cases hkk : k = key
        · subst hkk; simp at hk
        · have hk' : (m' !! k).isSome = true := by
            rwa [GMap.lookup_delete_ne] at hk; exact Ne.symm hkk
          obtain ⟨j, hj1, hj2⟩ := Hinv k hk'
          refine ⟨j, ?_, hj2⟩
          rcases Nat.lt_or_eq_of_le hj1 with h | h
          · exact h
          · subst h; rw [Hi1] at hj2; cases hj2; exact absurd rfl hkk
      · iexists _; iexact rep
    ipureintro
    intro k hk
    exact GMap.lookup_delete_ne _ (Ne.symm hk)
  iintro %m' ⟨%Hinv, ⟨%r, rep⟩, ms, Hv⟩ Hm
  wp_auto
  iapply HΦ
  unfold ownD
  iexists _, m'
  iframe Hv Hm Hacc Hfree Hqi
  isplitr
  · ipureintro; simp only; refine ⟨by trivial, by trivial, ?_⟩
    intro k hk
    obtain ⟨j, hj1, hj2⟩ := Hinv k (by simpa using hk)
    have := List.getElem?_eq_none_iff.mpr hj1
    rw [this] at hj2; cases hj2
  isplitr
  · unfold leaderOk; ileft; ipureintro; rfl
  unfold msgsOk
  imodintro
  iintro %k %m %Hk
  obtain ⟨j, hj1, hj2⟩ := Hinv k (by simp [Hk])
  have := List.getElem?_eq_none_iff.mpr hj1
  rw [this] at hj2; cases hj2
  done

/-- The general `ReinitMsgSet`, linked (its one callee, `NewMsgSet`, proved above). -/
theorem MsgSet.wp_ReinitMsgSetQ : MsgSet.ReinitMsgSet.specQ (hG := hG) :=
  MsgSet.ReinitMsgSet.wp_proofQ NewMsgSet.wp_proofQ

end specs

end replica.mset

end Perennial.github_com.imdea_software.swiftpaxos
