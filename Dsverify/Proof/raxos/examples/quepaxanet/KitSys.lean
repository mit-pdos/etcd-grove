/-
Client machine `c`'s QuePaxa client (`kit.go`'s `Sys`): the lock invariant of `s.mu`, `sysInv`,
and `deliver` (the lab's `Kit/{RecvWait,RecvDeliver,OpDefs}.lean`, re-based on remote's `op`).

**The lock invariant holds the request counter** (the lab's `nextInv` does not fit remote:
`ServeClient` runs `op` any number of times, possibly overlapping, `notes/dsv-quepaxa.md`):
`s.mu` protects the `waiting` map (batch id `x` ↦ a one-shot future whose contract on the sent
`*ClientBatch` is an answer batch with id `x`, fit, with one result `r` and `opAns γ x r`), and
`s.next = n` (`n ≤ 20`: `Op` sends at most `K = 20` requests) with client `c`'s half of the
registry counter at `n` (`cntHalf`, the other half `smrInv`'s) and its unused tickets, those of
requests `n..19` at the five replicas. `Op` takes `s.next` and registers its request in one
critical section (`op_register`), and takes the request's tickets out.

Registering an entry needs no freshness: an id already present is overwritten, its old promise
dropped (an operation whose promise is dropped only never receives, a liveness matter).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitConn
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Dsverify.Proof.raxos.Smr.Laws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure raxos.msg

/-! ## Pure facts of the tickets -/

/-- Client `c`'s tickets of requests `n..19`, request by request, each at replicas `1..5`. -/
def ticketsFromL (c n : Nat) : List Ticket :=
  (List.range' n (20 - n)).flatMap (fun j => ([1, 2, 3, 4, 5] : List Nat).map
    (fun (k : Nat) => ((k : Int), c, j)))

theorem ticketsFromL_succ (c n : Nat) (hn : n < 20) :
    ticketsFromL c n = ([1, 2, 3, 4, 5] : List Nat).map (fun (k : Nat) => ((k : Int), c, n)) ++
      ticketsFromL c (n + 1) := by
  unfold ticketsFromL
  rw [show 20 - n = (20 - (n + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem tickets_pairs_perm :
    ((([1, 2, 3, 4, 5] : List Int).flatMap (fun k => (List.range 20).map (fun j => (k, j))))).Perm
      ((List.range' 0 20).flatMap (fun j => ([1, 2, 3, 4, 5] : List Nat).map
        (fun (k : Nat) => ((k : Int), j)))) := by
  decide +kernel

theorem ticketsOf_perm (c : Nat) : (ticketsOf c).Perm (ticketsFromL c 0) := by
  have h1 : ticketsOf c = (([1, 2, 3, 4, 5] : List Int).flatMap
      (fun k => (List.range 20).map (fun j => (k, j)))).map (fun p => (p.1, c, p.2)) := by
    simp [ticketsOf, serverIds, List.map_flatMap, List.map_map, Function.comp_def]
  have h2 : ticketsFromL c 0 = ((List.range' 0 20).flatMap (fun j => ([1, 2, 3, 4, 5] : List Nat).map
        (fun (k : Nat) => ((k : Int), j)))).map (fun p => (p.1, c, p.2)) := by
    simp [ticketsFromL, List.map_flatMap, List.map_map, Function.comp_def]
  rw [h1, h2]
  exact tickets_pairs_perm.map _

theorem tix_mem (k c j : Nat) (hk : 1 ≤ k ∧ k ≤ 5) (hc : c < 6) (hj : j < 20) :
    ((k : Int), c, j) ∈ tickets := by
  unfold tickets serverIds
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨(k : Int), ?_, c, hc, j, hj, rfl⟩
  obtain ⟨h1, h5⟩ := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "sysTy" => raxos.examples.quepaxanet.Sys

/-- The contract of request `x`'s future: the sent `*ClientBatch` `p` is an answer to `x` (fit,
its one result `r`, `x`'s answer). -/
def ansContract (γ : QNames) (x : GoString) : Loc → IProp GF :=
  fun p => iprop(∃ (b : Batch) (r : GoString), repCB p (DFrac.own 1) b ∗
    ⌜b.id = x ∧ b.cmds = [r] ∧ batchFit b⌝ ∗ opAns γ x r)

/-- The waiting entry `x ↦ ch`: `ch` is a future whose promise for `x`'s answer is held here. -/
def waitEntry (γ : QNames) (x : GoString) (ch : Loc) : IProp GF :=
  iprop(∃ γf : FutureNames, isFuture Loc γf ch ∗ Fulfill γf (ansContract γ x))

/-- Every waiting entry of the map's value `mv`. -/
def waitChans (γ : QNames) (mv : GMap GoString Loc) : IProp GF :=
  iprop([∗map] x ↦ ch ∈ mv, waitEntry γ x ch)

/-- Client `c`'s unused tickets: those of requests `n..19`. -/
def ticketsFrom (γ : QNames) (c n : Nat) : IProp GF :=
  iprop([∗list] t ∈ ticketsFromL c n, ticketTok γ t)

/-- **The lock invariant of `s.mu`** (see the file header). -/
def sysInv (γ : QNames) (c : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (m : Loc) (mv : GMap GoString Loc) (n : Nat),
    structFieldRef sysTy go!"waiting" s ↦ m ∗ m ↦$ mv ∗ waitChans γ mv ∗
    structFieldRef sysTy go!"next" s ↦ W64 n ∗ ⌜n ≤ 20⌝ ∗ cntHalf γ c n ∗ ticketsFrom γ c n)

/-- The `Sys` struct's fixed fields: client `c`'s name and number, checks off, the replicas'
slice. -/
def sysFields (s : Loc) (c : Nat) (rs : GoSlice) (rls : List Loc) : IProp GF :=
  iprop(structFieldRef sysTy go!"name" s ↦□ W64 ((21 + c : Nat) : Int) ∗
    structFieldRef sysTy go!"c" s ↦□ W64 (c : Int) ∗
    structFieldRef sysTy go!"checks" s ↦□ false ∗
    structFieldRef sysTy go!"replicas" s ↦□ rs ∗ rs ↦*□ rls)

instance sysFields_persistent (s : Loc) (c : Nat) (rs : GoSlice) (rls : List Loc) :
    Persistent (sysFields (GF := GF) s c rs rls) := by
  unfold sysFields; infer_instance

/-- Client `c`'s connections to the replicas (replica `i + 1` at index `i`). -/
def repsOk (γ : QNames) (c : Nat) (rls : List Loc) : IProp GF :=
  iprop([∗list] i ↦ rl ∈ rls, isReplica γ c (i + 1) rl)

instance repsOk_persistent (γ : QNames) (c : Nat) (rls : List Loc) :
    Persistent (repsOk (GF := GF) γ c rls) := by
  unfold repsOk; infer_instance

/-- Client `c`'s `*Sys` at `s` (persistent). -/
def isSysL (γ : QNames) (c : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (rs : GoSlice) (rls : List Loc), ⌜c < 6 ∧ rls.length ≤ 5⌝ ∗ sysFields s c rs rls ∗
    sync.isMutex (structFieldRef sysTy go!"mu" s) (sysInv γ c s) ∗ repsOk γ c rls ∗ sharedRes γ)

instance isSysL_persistent (γ : QNames) (c : Nat) (s : Loc) :
    Persistent (isSysL (GF := GF) γ c s) := by
  unfold isSysL; infer_instance

/-- `Op`'s registration `s.waiting[id] = ch` (under the lock): the entry joins the map. -/
theorem waitChans_insert (γ : QNames) (mv : GMap GoString Loc) (x : GoString) (ch : Loc) :
    waitChans (GF := GF) γ mv ∗ waitEntry γ x ch ⊢ waitChans γ (<[x := ch]> mv) := by
  unfold waitChans
  iintro ⟨Hchs, He⟩
  iapply BigSepM.bigSepM_insert_elim $$ He Hchs

/-- `delete(s.waiting, id)` (the timeout's). -/
theorem waitChans_delete (γ : QNames) (mv : GMap GoString Loc) (x : GoString) :
    waitChans (GF := GF) γ mv ⊢ waitChans γ (GMap.delete x mv) := by
  unfold waitChans
  iintro Hchs
  cases h : mv !! x with
  | none =>
    rw [show GMap.delete x mv = mv from GMap.delete_notin _ _ h]
    iexact Hchs
  | some ch =>
    icases (BigSepM.bigSepM_delete h).1 $$ Hchs with ⟨-, Hchs⟩
    iexact Hchs

/-- Taking the entry of `x` out of the map (`deliver`). -/
theorem waitChans_take (γ : QNames) (mv : GMap GoString Loc) (x : GoString) (ch : Loc)
    (h : mv !! x = some ch) :
    waitChans (GF := GF) γ mv ⊢ waitEntry γ x ch ∗ waitChans γ (GMap.delete x mv) := by
  unfold waitChans
  exact (BigSepM.bigSepM_delete h).1

/-- `Op`'s fresh channel `make(chan *ClientBatch, 1)` as `x`'s future: the entry for the map,
and `Op`'s side (`isFuture` and `Await` of the one contract, for the receive). -/
theorem wait_promise (γ : QNames) (x : GoString) (ch : Loc) (γc : ChanNames) :
    ⊢ isChan (GF := GF) ch γc Loc -∗ ownChan γc Loc (ChanState.Buffered ([] : List Loc)) ={⊤}=∗
      ∃ γf : FutureNames, waitEntry γ x ch ∗ isFuture Loc γf ch ∗
        Await γf [ansContract γ x] := by
  iintro #Hch Hoc
  imod start_future ch γc (ChanState.Buffered ([] : List Loc)) (Or.inr rfl) $$ Hch Hoc
    with ⟨%γf, #Hf, Haw⟩
  imod future_alloc_promise γf ch (ansContract γ x) [] $$ Hf Haw with ⟨Hfl, Haw⟩
  rw [List.nil_append]
  imodintro
  iexists γf
  iframe Hf Haw
  unfold waitEntry
  iexists γf
  iframe Hf Hfl

/-- An answer a replica sent: fit, one result `r` with its `opAns`. -/
def ansOk (γ : QNames) (b : Batch) : IProp GF :=
  iprop(∃ r, ⌜b.cmds = [r] ∧ batchFit b⌝ ∗ opAns γ b.id r)

instance ansOk_persistent (γ : QNames) (b : Batch) : Persistent (ansOk (GF := GF) γ b) := by
  unfold ansOk opAns opDone; infer_instance

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

set_option maxHeartbeats 800000 in
/-- `s.deliver(from, p)`. -/
theorem wp_deliver (γ : QNames) (c : Nat) (s : Loc) (frm : w64) (p : Loc) (b : Batch) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isSysL γ c s ∗
        repCB p (DFrac.own 1) b ∗ ansOk γ b }}
      (App (App (Val (s @!! go.GoType.PointerType raxos.examples.quepaxanet.Sys.ty @!!
        go!"deliver")) (Val #frm)) (Val #p))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hsys, Hrep, #Hans⟩
  iunfold isSysL at Hsys
  icases Hsys with ⟨%rs, %rls, %Hc, #Hf, #Hmu, -, -⟩
  iunfold sysFields at Hf
  icases Hf with ⟨-, -, #Hck, -, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold sysInv at Hinv
  icases Hinv with ⟨%m, %mv, %n, Hw, Hm, Hchs, Hnext, %Hn, Hcnt, Htix⟩
  iunfold repCB at Hrep
  icases Hrep with ⟨%xv, Hp, Hxv⟩
  wp_auto
  iunfold repCBVal at Hxv
  icases Hxv with ⟨%ps, %hid, Hps, Hl⟩
  have hid2 : xv.Id' = b.id := hid.2.1
  iunfold ansOk at Hans
  icases Hans with ⟨%r, %hr, #Hans⟩
  rw [hid2]
  wp_apply wp_map_lookup2 $$ Hm as Hm
  cases hx : mv !! b.id with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hm Hchs Hnext Hcnt Htix]
    · unfold sysInv; iexists m, mv, n; iframe; ipureintro; exact Hn
    wp_end
  | some ch =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    wp_auto
    rw [hid2]
    wp_apply wp_mapDelete $$ Hm as Hm
    icases waitChans_take γ mv b.id ch hx $$ Hchs with ⟨He, Hchs⟩
    iunfold waitEntry at He
    icases He with ⟨%γf, #Hfu, Hfl⟩
    wp_apply wp_future_fulfill γf ch p $$ [$Hfu Hfl Hp Hps Hl]
    · unfold Fulfilled
      iexists ansContract γ b.id
      iframe Hfl
      unfold ansContract repCB
      iexists b, r
      iframe Hans
      isplitl
      · iexists xv
        iframe Hp
        unfold repCBVal
        iexists ps
        iframe
        ipureintro; exact hid
      · ipureintro; exact ⟨rfl, hr⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hm Hchs Hnext Hcnt Htix]
    · unfold sysInv; iexists m, GMap.delete b.id mv, n; iframe; ipureintro; exact Hn
    wp_end

end defs

end raxos.examples.quepaxanet
end Perennial
