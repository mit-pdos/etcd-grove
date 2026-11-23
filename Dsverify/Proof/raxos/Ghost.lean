/-
The run's global ghost state, its invariants and their laws (interface of stages 2-3,
`notes/stage2-plan.md`). Everything here lives in the global ghost state (`GooseGlobalGS`), shared
by the twelve nodes; it is allocated by the run's `start` (package `kit`).

* **The configuration** (`confIs γ c`, persistent): the configuration the orchestrator (node 0) chose
  (`kit.go`'s `New`), which every replica runs; `confTok γ` (exclusive, the client node's) until
  it is chosen.

* **Consensus** (`consInv`, namespace `consN`): the history `W` of QuePaxa's events
  (`Quepaxa/Proof/Pure/Consensus.lean`, a mono-list), empty until the configuration `c` is
  chosen, then reachable with its replicas and epochs (`Reach c.n c.ep W`); each recorder's slot
  states, half in `consInv` and half in the recorder's lock (`recHalf`: they agree with
  `recState W`); each proxy's init frontier (half in `consInv`, half in the proxy's main loop,
  `initFront`) and the init tokens it issues (`initTok`, exclusive: one `init` event per slot and
  proxy). Facts: `evIn γ e` (persistent: `e ∈ W`), `decided γ i ids := evIn γ (.decide i ids)`.
  **The slots' bound** (what `instanceTimeouts[proposeIndex]` and the recorders' slot slices
  need): every init token costs a credit, and a proxy mints one credit per frame of the client's
  it reads, each frame carrying one of the workload's 600 tickets (one per replica and request),
  each ticket carried by one frame (`tixAt`); so at most 600 credits are spent (`spentLb`), and
  every slot is in `[1, 600]` (5 server nodes, 6 clients, 20 requests).
  Laws: one per kind of step (`cons_*`), each appending its event; `decided_agree`,
  `decided_nonempty` (from `pure.agreement`).
* **SMR** (`smrInv`, namespace `smrN`): the batch registry (`batchReg γ x b`, persistent: the batch
  with id `x` is `b`; `"nil"` is `nilBatch`; an epoch summary's id `summaryId p` is the summary's
  batch `⟨x, -1, [x]⟩`; every other is a request of the client, one command of a key-value input
  the kit makes); the globally executed prefix of the decided log (a
  mono-list of slots' ids, `execLb γ D` persistent); the abstract state (the puts executed, half
  here and half `ownState γ σ`); each registered request's atomic update, pending until its batch
  is executed, then its output (`opDone γ x o`, persistent) and the client's commit
  postcondition. Laws: `smr_exec_slot` (a replica executes its next decided slot: the executed
  prefix grows, the requests first executed there are committed, each executed request's
  result is its output's answer), `op_register`, `op_collect` (the client's).

Changed against the lab (notes/dsv-quepaxa.md): **a request's update is remote's linearization
point** (`opAU`: `remote.lin` of the kit's store `kvB`, `Kit.lean`'s `lin_opAU`; a put's one-shot,
a get's persistent, as remote's `slotUpd`), with the caller's postcondition `Φ` of the output, in
place of the lab's atomic update at `clientN` over its `Harness.Models` `kv` with a commit
postcondition `Q σ σ' o`; inputs and outputs are the kit's `KIn`/`KOut`. The proxy's read counters
are keyed by the net extension's connection numbers, with `netFresh` in place of the lab's
`NetConn.connFresh`. (The registry's `cnt` map is kept as the lab's.)
-/
module

public import Dsverify.Proof.raxos.Msg
public import Dsverify.Proof.raxos.Pure.Consensus
public import Dsverify.Proof.raxos.Pure.Conf
public import Dsverify.Proof.raxos.Pure.Smr
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token
public import GooseLang.Ext.Net.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure

/-! ## Countable encodings of the ghost values -/

namespace pure

def Val.toT (v : Val) : Int × Int × Int × List GoString := (v.prio, v.pid, v.tid, v.ids)
theorem Val.toT_inj : Function.Injective Val.toT := by
  rintro ⟨⟩ ⟨⟩ h; simp_all [Val.toT]
instance Val.countable : Pos.Countable Val := .ofInjective (fun v => Pos.Countable.encode v.toT)
  (fun _ _ h => Val.toT_inj (Pos.encode_inj h))

def RecSt.toT (s : RecSt) : Int × Val × Val × Val := (s.S, s.F, s.A, s.M)
theorem RecSt.toT_inj : Function.Injective RecSt.toT := by
  rintro ⟨⟩ ⟨⟩ h; simp_all [RecSt.toT]
instance RecSt.countable : Pos.Countable RecSt := .ofInjective (fun v => Pos.Countable.encode v.toT)
  (fun _ _ h => RecSt.toT_inj (Pos.encode_inj h))

def Ev.toT : Ev → (Int × Int × List GoString × Bool) ⊕ (Int × Int × Bool × Int × Val) ⊕
    (Int × Int × Int × Val) ⊕ (Int × Int × Int × Val × RecSt) ⊕ (Int × List GoString)
  | .init i me ids lead => .inl (i, me, ids, lead)
  | .pstate i me lead s P => .inr (.inl (i, me, lead, s, P))
  | .send i me s v => .inr (.inr (.inl (i, me, s, v)))
  | .record r i s v st => .inr (.inr (.inr (.inl (r, i, s, v, st))))
  | .decide i ids => .inr (.inr (.inr (.inr (i, ids))))
theorem Ev.toT_inj : Function.Injective Ev.toT := by
  intro a b h; cases a <;> cases b <;> simp_all [Ev.toT]
instance Ev.countable : Pos.Countable Ev := .ofInjective (fun v => Pos.Countable.encode v.toT)
  (fun _ _ h => Ev.toT_inj (Pos.encode_inj h))

def QConf.toT (c : QConf) : Nat × Nat × Nat × Nat × Nat := (c.n, c.se, c.pipe, c.ep, c.tmo)
theorem QConf.toT_inj : Function.Injective QConf.toT := by
  rintro ⟨⟩ ⟨⟩ h; simp_all [QConf.toT]
instance QConf.countable : Pos.Countable QConf := .ofInjective (fun v => Pos.Countable.encode v.toT)
  (fun _ _ h => QConf.toT_inj (Pos.encode_inj h))

end pure

def KIn.toT (i : KIn) : Bool × GoString × GoString := (i.put, i.k, i.v)
theorem KIn.toT_inj : Function.Injective KIn.toT := by
  rintro ⟨⟩ ⟨⟩ h; simp_all [KIn.toT]
instance KIn.countable : Pos.Countable KIn :=
  .ofInjective (fun v => Pos.Countable.encode (KIn.toT v)) (fun _ _ h => KIn.toT_inj (Pos.encode_inj h))

def KOut.toT (o : KOut) : Bool × GoString := (o.found, o.v)
theorem KOut.toT_inj : Function.Injective KOut.toT := by
  rintro ⟨⟩ ⟨⟩ h; simp_all [KOut.toT]
instance KOut.countable : Pos.Countable KOut :=
  .ofInjective (fun v => Pos.Countable.encode (KOut.toT v)) (fun _ _ h => KOut.toT_inj (Pos.encode_inj h))

/-- The store of the puts `l`, newest first (the lab's `Harness.Models` `kvAbs`: a key's value is
its newest put's). -/
def kvAbs : List (GoString × GoString) → pure.Store
  | [] => fun _ => none
  | (k, v) :: l => fun k' => if k' = k then some v else kvAbs l k'

/-! ## Names -/

/-- A registry entry: the empty batch `"nil"`, an epoch summary (its id is `summaryId p` for a
permutation `p` of the replicas), or client `c`'s `j`-th request, input `inp`, with the names of
its saved commit postcondition (`q`) and of its collection token (`tok`). -/
inductive RegEntry where
  | nil
  | sum
  | op (c j : Nat) (inp : KIn) (q tok : GName)

def RegEntry.toT : RegEntry → Option (Option (Nat × Nat × KIn × GName × GName))
  | .nil => none
  | .sum => some none
  | .op c j i q t => some (some (c, j, i, q, t))
theorem RegEntry.toT_inj : Function.Injective RegEntry.toT := by
  intro a b h; cases a <;> cases b <;> simp_all [RegEntry.toT]
instance RegEntry.countable : Pos.Countable RegEntry :=
  .ofInjective (fun v => Pos.Countable.encode v.toT) (fun _ _ h => RegEntry.toT_inj (Pos.encode_inj h))

/-- A ticket: replica `k`, client `c`, request `j` (the right to have one frame of client `c`'s
`j`-th request read by replica `k`'s proxy). -/
abbrev Ticket := Int × Nat × Nat

/-- The server nodes' replica names, `1..5` (`MaxReplicas`; a configuration runs `1..c.n`). -/
def serverIds : List Int := [1, 2, 3, 4, 5]

/-- The tickets of the workload: 5 server nodes, 6 clients, 20 requests each. -/
def tickets : List Ticket :=
  serverIds.flatMap (fun k => (List.range 6).flatMap (fun c =>
    (List.range 20).map (fun j => (k, c, j))))

/-- The decimal digits of `n` (`kit.go`'s `digits`, `strconv.Itoa`). -/
def decStr (n : Nat) : GoString := (toString n).toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- Client `c`'s QuePaxa name (kit.toml `ClientName` + c: `21..26`). -/
def clientName (c : Nat) : Int := 21 + c

/-- The id of client `c`'s request with sequence number `n` (`kit.go`'s `Op`:
`digits(s.name) + "." + digits(s.next)`, the name `21 + c`). -/
def opId (c n : Nat) : GoString := decStr (21 + c) ++ go!"." ++ decStr n

/-- The batch of a registry entry with id `x`. -/
def RegEntry.batch (x : GoString) : RegEntry → Batch
  | .nil => nilBatch
  | .sum => ⟨x, -1, [x]⟩
  | .op c _ inp _ _ => ⟨x, clientName c, [cmdOf inp]⟩

/-- The run's ghost names (allocated by `start`). -/
structure QNames where
  /-- the configuration: `()` ↦ the chosen one (ghost map with discarded elements; its auth, empty,
  is the client's token until it chooses) -/
  conf : GName
  /-- the history of consensus events (mono-list of `Ev`) -/
  hist : GName
  /-- recorder `r` ↦ its slot states (ghost map with half elements) -/
  recs : GName
  /-- proxy `me` ↦ its init frontier (ghost map with half elements) -/
  front : GName
  /-- `(me, i)` ↦ `()`: the init tokens issued (exclusive elements) -/
  inits : GName
  /-- the globally executed prefix of the decided log (mono-list of slots' ids) -/
  exec : GName
  /-- the abstract state: the puts executed (ghost variable, halves) -/
  puts : GName
  /-- the registry: id ↦ entry (persistent elements) -/
  reg : GName
  /-- the outputs of executed requests: id ↦ output (persistent elements) -/
  res : GName
  /-- client `c` ↦ the number of requests it registered (ghost map: a half in `smrInv`, a quarter
  in `clientTok`, a quarter in the client node's `isSys` invariant with `s.next`) -/
  cnt : GName
  /-- the gRPC world's registry of connections (`GrpcWorld.reg`) -/
  grpc : GName
  /-- ticket ↦ the client frame carrying it: (connection, frame number) (persistent elements) -/
  tix : GName
  /-- ticket ↦ `()`: the client's ticket tokens (exclusive; spent ones held by `consInv`) -/
  tick : GName
  /-- ticket ↦ `()`: the credits a proxy minted (exclusive; spent ones held by `consInv`) -/
  cred : GName
  /-- connection ↦ the number of frames the proxy has read on it (ghost map, half elements) -/
  rd : GName
  /-- the credits spent (mono-list of tickets) -/
  spent : GName

/-! ## Definitions -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

def raxosN : Namespace := ndot nroot "raxos"
def consN : Namespace := ndot raxosN "cons"
def smrN : Namespace := ndot raxosN "smr"

/-! ### The configuration -/

/-- The orchestrator chose the configuration `c` (persistent). -/
def confIs (γ : QNames) (c : QConf) : IProp GF := ghostMapElem γ.conf () .discard c

/-- The configuration is not chosen yet (exclusive; the client node's until it chooses). -/
def confTok (γ : QNames) : IProp GF := ghostMapAuth γ.conf 1 (∅ : GMap Unit QConf)

/-- The batch with id `x` is `b` (persistent). -/
def batchReg (γ : QNames) (x : GoString) (b : Batch) : IProp GF :=
  iprop(∃ e : RegEntry, ghostMapElem γ.reg x .discard e ∗ ⌜b = e.batch x ∧
    (e = .nil → x = go!"nil") ∧
    (e = .sum → ∃ p : List Nat, x = summaryId p ∧ sumPerm p) ∧
    (∀ c j inp q t, e = .op c j inp q t → x = opId c j ∧ c < 6 ∧ inputOk inp)⌝)

/-! ### Consensus -/

/-- `e` is in the history (persistent). -/
def evIn (γ : QNames) (e : Ev) : IProp GF :=
  iprop(∃ W : World, monoListLbOwn γ.hist W ∗ ⌜e ∈ W⌝)

/-- Slot `i` was decided `ids` (persistent). -/
def decided (γ : QNames) (i : Int) (ids : List GoString) : IProp GF := evIn γ (.decide i ids)

/-- Recorder `r`'s half of its slot states `m` (slot ↦ state; a slot not in `m` is new). -/
def recHalf (γ : QNames) (r : Int) (m : GMap Int RecSt) : IProp GF :=
  ghostMapElem γ.recs r (DFrac.own (1 : Qp).half) m

/-- Proxy `me`'s half of its init frontier `n`: it may issue init tokens for slots `≥ n`. -/
def initFront (γ : QNames) (me : Int) (n : Int) : IProp GF :=
  ghostMapElem γ.front me (DFrac.own (1 : Qp).half) n

/-- Proxy `me` may propose slot `i` once (exclusive). -/
def initTok (γ : QNames) (me i : Int) : IProp GF :=
  ghostMapElem γ.inits (me, i) (DFrac.own 1) ()

/-- The client may send client `c`'s request `j` to replica `k` once (exclusive). -/
def ticketTok (γ : QNames) (t : Ticket) : IProp GF := ghostMapElem γ.tick t (DFrac.own 1) ()

/-- Ticket `t` is carried by frame `n` of connection `cid` (persistent). -/
def tixAt (γ : QNames) (t : Ticket) (cid : Nat) (n : Nat) : IProp GF :=
  ghostMapElem γ.tix t .discard (cid, n)

/-- A credit minted from ticket `t` (exclusive): the right to issue one init token. -/
def credit (γ : QNames) (t : Ticket) : IProp GF := ghostMapElem γ.cred t (DFrac.own 1) ()

/-- The proxy's half of the count `n` of frames it has read on connection `cid`. -/
def rdCtr (γ : QNames) (cid : Nat) (n : Nat) : IProp GF :=
  ghostMapElem γ.rd cid (DFrac.own (1 : Qp).half) n

/-- At least `m` credits are spent (persistent). -/
def spentLb (γ : QNames) (m : Int) : IProp GF :=
  iprop(∃ L : List Ticket, monoListLbOwn γ.spent L ∗ ⌜m ≤ L.length⌝)

/-- The consensus invariant (see the file header): the history is empty until the configuration
is chosen, and then reachable with its replicas and epochs; recorders' states agree with it; every
`init` event's token is spent (held here), and no token was issued at or above a proxy's
frontier. -/
def consInv (γ : QNames) : IProp GF :=
  iprop(∃ (W : World) (R : GMap Int (GMap Int RecSt)) (Fr : GMap Int Int) (T : GMap (Int × Int) Unit)
      (Tix : GMap Ticket (Nat × Nat)) (Cr : GMap Ticket Unit) (Rd : GMap Nat Nat) (S : List Ticket),
    monoListAuthOwn γ.hist 1 W ∗
    (⌜W = []⌝ ∨ ∃ c : QConf, confIs γ c ∗ ⌜c.ok ∧ Reach (c.n : Int) (c.ep : Int) W⌝) ∗
    ghostMapAuth γ.recs 1 R ∗ ([∗map] r ↦ m ∈ R, ghostMapElem γ.recs r (DFrac.own (1 : Qp).half) m) ∗
    ⌜(∀ r, (R !! r).isSome ↔ r ∈ serverIds) ∧
      ∀ r m, R !! r = some m → ∀ i, recState W r i = (m !! i).getD RecSt.init⌝ ∗
    ghostMapAuth γ.front 1 Fr ∗ ([∗map] me ↦ n ∈ Fr, ghostMapElem γ.front me (DFrac.own (1 : Qp).half) n) ∗
    ghostMapAuth γ.inits 1 T ∗
    ghostMapAuth γ.tix 1 Tix ∗ ([∗map] t ↦ p ∈ Tix, ghostMapElem γ.tix t .discard p ∗
      ghostMapElem γ.tick t (DFrac.own 1) ()) ∗
    ghostMapAuth γ.cred 1 Cr ∗ ([∗list] t ∈ S, ghostMapElem γ.cred t (DFrac.own 1) ()) ∗
    ghostMapAuth γ.rd 1 Rd ∗ ([∗map] cid ↦ n ∈ Rd, ghostMapElem γ.rd cid (DFrac.own (1 : Qp).half) n ∗
      netFresh (extGlobalGS netExt) cid true) ∗
    monoListAuthOwn γ.spent 1 S ∗
    ⌜(∀ me, (Fr !! me).isSome ↔ me ∈ serverIds) ∧
      (∀ me n, Fr !! me = some n → 1 ≤ n ∧ n ≤ S.length + 1) ∧
      (∀ me i, (T !! (me, i)).isSome → 1 ≤ i ∧ i ≤ S.length ∧ ∃ n, Fr !! me = some n ∧ i < n) ∧
      (∀ i me ids lead, Ev.init i me ids lead ∈ W → (T !! (me, i)).isSome) ∧
      (∀ t, (Tix !! t).isSome → t ∈ tickets) ∧
      (∀ t, (Cr !! t).isSome → ∃ cid n, Tix !! t = some (cid, n) ∧ ∃ m, Rd !! cid = some m ∧ n < m) ∧
      S.Nodup ∧ (∀ t ∈ S, (Cr !! t).isSome)⌝ ∗
    ([∗list] e ∈ W, match e with
      | .init i me ids _ => ghostMapElem γ.inits (me, i) (DFrac.own 1) () ∗
          [∗list] x ∈ ids, ∃ b, batchReg γ x b
      | _ => iprop(True)))

/-- Replica `me`'s evidence that it leads slot `i` in the configuration `c` (persistent): the
round-robin leader of the first `2n` epochs, or the first replica of the summary decided in the
previous epoch's first slot (`pure.leaderOk`). -/
def leadEv (γ : QNames) (c : QConf) (i me : Int) : IProp GF :=
  iprop(⌜i.tdiv c.ep ≤ 2 * c.n ∧ me = rrLeader c.n c.ep i⌝ ∨
    ∃ p : List Nat, decided γ ((i.tdiv c.ep - 1) * c.ep) [summaryId p] ∗
      ⌜2 * (c.n : Int) < i.tdiv c.ep ∧ isPerm c.n p ∧ p.head?.map (fun k : Nat => (k : Int)) = some me⌝)

/-! ### SMR -/

/-- `D` is a prefix of the globally executed prefix of the decided log (persistent). -/
def execLb (γ : QNames) (D : List (List GoString)) : IProp GF := monoListLbOwn γ.exec D

/-- Request `x` was executed with output `o` (persistent). -/
def opDone (γ : QNames) (x : GoString) (o : KOut) : IProp GF :=
  ghostMapElem γ.res x .discard o

/-- The abstract state of the client spec: the store of the puts `l` (`kvAbs`). -/
def ownState (γ : QNames) (σ : pure.Store) : IProp GF :=
  iprop(∃ l : List (GoString × GoString), ghostVar γ.puts (1 : Qp).half l ∗ ⌜σ = kvAbs l⌝)

/-- The puts executed by the decided prefix `D`, newest first (`kvAbs` reads the first put of a
key). -/
def putsOf (B : GoString → Option Batch) (D : List (List GoString)) : List (GoString × GoString) :=
  (execLog B D).puts.reverse

/-- **A request's update** (input `inp`, the caller's postcondition `Φ` of the output): the
store's step on the abstract state, remote's linearization point (`remote.lin` of the kit's store,
`Kit.lean`'s `lin_opAU`), outside QuePaxa's invariants (`raxosN`). -/
def opAU (γ : QNames) (inp : KIn) (Φ : KOut → IProp GF) : IProp GF :=
  iprop(|={⊤ \ ↑raxosN, ∅}=> ∃ σ, ownState γ σ ∗
    (ownState γ (kvB.step inp σ).1 ={∅, ⊤ \ ↑raxosN}=∗ Φ (kvB.step inp σ).2))

/-- The update a registered request holds until it is executed: a put's `opAU`, one-shot; a
get's, persistent (a read: remote's `slotUpd`). -/
def opUpd (γ : QNames) (inp : KIn) (Φ : KOut → IProp GF) : IProp GF :=
  if inp.put then opAU γ inp Φ else iprop(□ opAU γ inp Φ)

/-- The SMR invariant (see the file header). -/
def smrInv (γ : QNames) : IProp GF :=
  iprop(∃ (D : List (List GoString)) (Reg : GMap GoString RegEntry)
      (Res : GMap GoString (KOut)) (Cnt : GMap Nat Nat),
    monoListAuthOwn γ.exec 1 D ∗
    ([∗list] k ↦ ids ∈ D, decided γ (k + 1) ids) ∗
    ghostVar γ.puts (1 : Qp).half (putsOf (fun x => (Reg !! x).map (RegEntry.batch x)) D) ∗
    ghostMapAuth γ.reg 1 Reg ∗ ([∗map] x ↦ e ∈ Reg, ghostMapElem γ.reg x .discard e) ∗
    ghostMapAuth γ.res 1 Res ∗ ([∗map] x ↦ o ∈ Res, ghostMapElem γ.res x .discard o) ∗
    ghostMapAuth γ.cnt 1 Cnt ∗ ([∗map] c ↦ n ∈ Cnt, ghostMapElem γ.cnt c (DFrac.own (1 : Qp).half) n) ∗
    ⌜(∀ c n, Cnt !! c = some n → c < 6 ∧ n ≤ 20) ∧
      Reg !! go!"nil" = some RegEntry.nil ∧
      (∀ x e, Reg !! x = some e → e = RegEntry.nil → x = go!"nil") ∧
      (∀ x, Reg !! x = some RegEntry.sum → ∃ p : List Nat, x = summaryId p ∧ sumPerm p) ∧
      (∀ x c j inp q t, Reg !! x = some (.op c j inp q t) →
        x = opId c j ∧ inputOk inp ∧ ∃ n, Cnt !! c = some n ∧ j < n) ∧
      (∀ x, (Res !! x).isSome ↔
        (∃ c j inp q tok, Reg !! x = some (.op c j inp q tok)) ∧
          x ∈ (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).done) ∧
      (∀ x ∈ (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).done,
        ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x)) ∧
      (∀ x o, Res !! x = some o → ∃ c j inp q tok, Reg !! x = some (.op c j inp q tok) ∧
        (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).results x = some [ansOf inp o] ∧
        ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil")⌝ ∗
    ([∗map] x ↦ e ∈ Reg, match e with
      | .nil => iprop(True)
      | .sum => iprop(True)
      | .op _ _ inp q tok =>
        ∃ Φ : KOut → IProp GF,
          savedPredOwn q .discard Φ ∗
          match Res !! x with
          | none => ▷ opUpd γ inp Φ
          | some o => ▷ Φ o ∨ token tok))

/-! ### Facts derived for the answers -/

/-- The answer `r` (the store's result) of request `x`, as its output: `x` is client `c`'s
request with input `inp`, executed with output `o`, and `r` is `o`'s answer (persistent). Whether
`r` is valid UTF-8 (so that the answer can be sent) is not said: the proxy learns it from
`Marshal` (P4). -/
def opAns (γ : QNames) (x : GoString) (r : GoString) : IProp GF :=
  iprop(∃ (c j : Nat) (inp : KIn) (q tok : GName) (o : KOut),
    ghostMapElem γ.reg x .discard (RegEntry.op c j inp q tok) ∗ opDone γ x o ∗
    ⌜r = ansOf inp o ∧ ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil"⌝)

end defs

/-! ## Persistence -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

instance evIn_persistent (γ : QNames) (e : Ev) : Persistent (evIn (GF := GF) γ e) := by
  unfold evIn; infer_instance
instance batchReg_persistent (γ : QNames) (x : GoString) (b : Batch) :
    Persistent (batchReg (GF := GF) γ x b) := by
  unfold batchReg; infer_instance
instance execLb_persistent (γ : QNames) (D : List (List GoString)) :
    Persistent (execLb (GF := GF) γ D) := by
  unfold execLb; infer_instance
instance opDone_persistent (γ : QNames) (x : GoString) (o : KOut) :
    Persistent (opDone (GF := GF) γ x o) := by
  unfold opDone; infer_instance
instance opAns_persistent (γ : QNames) (x r : GoString) : Persistent (opAns (GF := GF) γ x r) := by
  unfold opAns; infer_instance
instance leadEv_persistent (γ : QNames) (c : QConf) (i me : Int) :
    Persistent (leadEv (GF := GF) γ c i me) := by
  unfold leadEv decided evIn; infer_instance
instance confIs_persistent (γ : QNames) (c : QConf) : Persistent (confIs (GF := GF) γ c) := by
  unfold confIs; infer_instance
instance netFresh_timeless (c : Nat) (b : Bool) :
    Timeless (netFresh (GF := GF) (extGlobalGS netExt) c b) := by
  unfold netFresh; infer_instance

instance ownState_timeless (γ : QNames) (σ : GoString → Option GoString) :
    Timeless (ownState (GF := GF) γ σ) := by
  unfold ownState; infer_instance

end laws

end Perennial.raxos
