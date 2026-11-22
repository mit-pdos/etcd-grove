/-
# kvcheck's checker at the store (2026-11-22)

What kvcheck's `do`/`read`/`Check` are stated in, at kvnet's store (`Store.lean`, decision B: the store's
invariant is global, so the checking client mints its operations and reads on its own machine):

* `kvCnt γ n`: the checker's counters' predicate (`CheckerCnt`, `checkerInv`): for `nextOp` at `a` the
  store's operation counter half (`ghostVar γ.r.opn ½ a`, what `kd_mint` mints at), for `nextRead` at
  `b` the read sequence numbers of the replicas `1 … n` (each at most `b`, what `kd_mint_next` mints
  past). So `fresh` mints under the checker's lock, in the counters' order.
* `kvReadMinted γ id seq key l`: what minting the read `(id, seq, key)` after the log `l` gives the
  client: the read's fact on the wire (`readOkK`) and the log the context was committed after (so the
  replica's answer, which names that log existentially, names `l`: `readCtxAfter_agree`).
* `kv_mint_reads`: a fresh read sequence number mints the read at every replica id at once (the id is
  picked after `fresh`; the others' contexts are never used).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Client
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Facts
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ClientLemmas
public import KvNet.Proof.go_etcd_io.raft.v3.ReadCtxLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open raft_kvreconf (readCtxB bootVoters)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 raft_kvnet

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [kvnet_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- The checker's counters at the store (see the file header). -/
def kvCnt (γ : KdNames) (n : Nat) : CheckerCnt GF := fun w a =>
  if w then iprop([∗list] id ∈ bootVoters n,
      ∃ ns : w64, id ↪[γ.r.rseq] ns ∗ ⌜uint.Z ns ≤ uint.Z a⌝)
  else ghostVar γ.r.opn (1 : Qp).half a

/-- A read minted at `(id, seq, key)` after the log `l` (see the file header). -/
def kvReadMinted (γ : KdNames) (id seq : w64) (key : List w8) (l : List LogEntry) : IProp GF :=
  iprop(readOkK γ id seq key ∗ readCtxAfter γ.r.cluster kdRaftN (readCtxB id seq key) l)

instance kvReadMinted_persistent (γ : KdNames) (id seq : w64) (key : List w8) (l : List LogEntry) :
    Persistent (kvReadMinted (GF := GF) γ id seq key l) := by
  unfold kvReadMinted; infer_instance

/-- **A fresh read sequence number mints the read at every replica id** (see the file header). -/
theorem kv_mint_reads (γ : KdNames) (n : Nat) (b : w64) (key : List w8) (l : List LogEntry)
    (Hb : uint.Z b + 1 < 2 ^ 64) (Hk : (key.length : Int) < 2 ^ 61) :
    ⊢ rkvInv (GF := GF) γ -∗ isCommittedLogLb γ.r.cluster l -∗ kvCnt γ n true b ={⊤}=∗
      kvCnt γ n true (b + W64 1) ∗
      [∗list] id ∈ bootVoters n, kvReadMinted γ id (b + W64 1) key l := by
  iintro #Hinv #Hl Hc
  unfold kvCnt
  simp only [↓reduceIte]
  ihave Hu : iprop([∗list] id ∈ bootVoters n, |={⊤}=>
      ((∃ ns : w64, id ↪[γ.r.rseq] ns ∗ ⌜uint.Z ns ≤ uint.Z (b + W64 1)⌝) ∗
        kvReadMinted γ id (b + W64 1) key l)) $$ [Hc]
  · iapply BigSepL.bigSepL_impl $$ Hc
    iintro !> %k %id %_ ⟨%ns, Hfr, %Hns⟩
    imod kd_mint_next γ id ns b key l Hns Hb (by omega) $$ Hinv Hfr Hl with ⟨Hfr, #Hm, #Hrc, #Hra⟩
    imodintro
    isplitl [Hfr]
    · iexists (b + W64 1)
      iframe Hfr
      ipureintro; exact Int.le_refl _
    · unfold kvReadMinted readOkK
      isplitr
      · isplitr
        · ipureintro; exact Hk
        isplitr
        · iexact Hm
        isplitr
        · iexact Hrc
        iexists l
        isplitr
        · iexact Hra
        iexact Hl
      · iexact Hra
  imod BigSepL2.bigSepL_fupd $$ Hu with Hu
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hu with ⟨H1, H2⟩
  imodintro
  iframe H1 H2

/-- The minted read of the replica `id` (`1 ≤ id ≤ n`), from all of them. -/
theorem kvReadMinted_at (γ : KdNames) (n : Nat) (id seq : w64) (key : List w8) (l : List LogEntry)
    (h1 : 1 ≤ uint.nat id) (h2 : uint.nat id ≤ n) :
    ([∗list] id' ∈ bootVoters n, kvReadMinted (GF := GF) γ id' seq key l) ⊢
      kvReadMinted γ id seq key l := by
  have hget : (bootVoters n)[uint.nat id - 1]? = some id := by
    unfold bootVoters
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.some.injEq]
    rw [show ((uint.nat id - 1 : Nat) : Int) + 1 = (uint.nat id : Int) by omega]; word
  exact BigSepL.bigSepL_lookup (Φ := fun _ id' => kvReadMinted γ id' seq key l) hget

end defs

end raft_kvcheck
end EtcdGrove
end Perennial
