/-
The vocabulary of the hraft kit transport's specs (`rpctransport`, notes/dsv-hraft.md, S4): the
ownership of its wire structs and of raft's messages (their byte slices, a log entry's contents
`EntV`), and the pure wire-size bounds the transport checks before it sends a request
(`*ReqBound`, the size check: a request the net/rpc model could not send is refused).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-! ## The wire-size bounds (pure) -/

/-- `MaxRequest`. -/
abbrev maxReqN : Nat := 2 ^ 30

/-- `BytesBound` of a slice of `n` bytes. -/
def bytesBoundN (n : Nat) : Nat := if maxReqN < n then maxReqN + 1 else 17 + 8 * n

theorem bytesBoundN_le (n : Nat) : bytesBoundN n ≤ 17 + 8 * 2 ^ 30 := by
  unfold bytesBoundN maxReqN; split <;> omega

/-- `hdrBound` of a header whose slices hold `id` and `ad`. -/
def hdrBoundN (id ad : List w8) : Nat := 16 + bytesBoundN id.length + bytesBoundN ad.length

/-- A `uint64` sum that does not overflow. -/
theorem w64_add_nat (a b : w64) (h : uint.nat a + uint.nat b < 2 ^ 64) :
    uint.nat (a + b) = uint.nat a + uint.nat b := by
  show (a + b).toNat = a.toNat + b.toNat
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem w64_add_eq {a b : w64} {x y : Nat} (ha : uint.nat a = x) (hb : uint.nat b = y)
    (h : x + y < 2 ^ 64) : uint.nat (a + b) = x + y := by
  rw [w64_add_nat a b (by omega), ha, hb]

theorem w64_nat_lit (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  show (BitVec.ofInt 64 (n : Int)).toNat = n
  rw [BitVec.toNat_ofInt]
  omega

/-- A log entry's contents (a wire `Entry`, a raft `Log` but its `AppendedAt`). -/
structure EntV where
  index : w64
  term : w64
  ty : w8
  data : List w8
  ext : List w8

/-- `AppendReqBound`'s loop over the entries, from `n`. -/
def entsBoundN : Nat → List EntV → Nat
  | n, [] => n
  | n, v :: vs => if maxReqN < n then n else
      entsBoundN (n + 64 + bytesBoundN v.data.length + bytesBoundN v.ext.length) vs

theorem entsBoundN_cons (n : Nat) (v : EntV) (vs : List EntV) :
    entsBoundN n (v :: vs) = if maxReqN < n then n else
      entsBoundN (n + 64 + bytesBoundN v.data.length + bytesBoundN v.ext.length) vs := rfl

theorem entsBoundN_le (n : Nat) (vs : List EntV) (h : n ≤ 2 ^ 36) :
    entsBoundN n vs ≤ 2 ^ 36 := by
  induction vs generalizing n with
  | nil => exact h
  | cons v vs ih =>
    unfold entsBoundN
    split
    · exact h
    · next hn =>
      apply ih
      have := bytesBoundN_le v.data.length
      have := bytesBoundN_le v.ext.length
      unfold maxReqN at hn
      omega

/-- `AppendReqBound` of a request whose header holds `id`, `ad`, whose leader is `ld` and whose
entries are `vs`. -/
def aeBoundN (id ad ld : List w8) (vs : List EntV) : Nat :=
  entsBoundN (128 + hdrBoundN id ad + bytesBoundN ld.length + 64) vs

/-- `VoteReqBound`. -/
def voteBoundN (id ad cand : List w8) : Nat := 128 + hdrBoundN id ad + bytesBoundN cand.length + 64

/-- `PreVoteReqBound`. -/
def preVoteBoundN (id ad : List w8) : Nat := 128 + hdrBoundN id ad + 64

/-- `SnapReqBound`. -/
def snapBoundN (id ad ld peers cfg data : List w8) : Nat :=
  128 + hdrBoundN id ad + bytesBoundN ld.length + bytesBoundN peers.length +
    bytesBoundN cfg.length + bytesBoundN data.length + 128

/-- `TimeoutReqBound`. -/
def timeoutBoundN (id ad : List w8) : Nat := 128 + hdrBoundN id ad

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

section own
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Ownership of log entries -/

/-- The wire `Entry` value `e` holds the contents `v` (its slices at fraction `dq`). -/
def entOwn (e : Entry) (dq : DFrac) (v : EntV) : IProp GF :=
  iprop(⌜e.Index' = v.index ∧ e.Term' = v.term ∧ e.Type' = v.ty⌝ ∗
    e.Data' ↦*{dq} v.data ∗ e.Extensions' ↦*{dq} v.ext)

/-- The wire slice `sl` (a `[]Entry`) holds the entries `vs`. -/
def entsOwn (sl : GoSlice) (dq : DFrac) (vs : List EntV) : IProp GF :=
  iprop(∃ es : List Entry, sl ↦*{dq} es ∗ [∗list] e;v ∈ es;vs, entOwn e dq v)

/-- The raft `Log` value `lv` holds the contents `v`. -/
def logOwnV (lv : github_com.hashicorp.raft.Log) (dq : DFrac) (v : EntV) : IProp GF :=
  iprop(⌜lv.Index' = v.index ∧ lv.Term' = v.term ∧ lv.Type' = v.ty⌝ ∗
    lv.Data' ↦*{dq} v.data ∗ lv.Extensions' ↦*{dq} v.ext)

/-- The raft `*Log` `p` holds the contents `v`. -/
def logOwn (p : Loc) (dq : DFrac) (v : EntV) : IProp GF :=
  iprop(∃ lv : github_com.hashicorp.raft.Log, p ↦{dq} lv ∗ logOwnV lv dq v)

/-- The raft slice `sl` (a `[]*Log`) holds the entries `vs`. -/
def logsOwn (sl : GoSlice) (dq : DFrac) (vs : List EntV) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*{dq} ps ∗ [∗list] p;v ∈ ps;vs, logOwn p dq v)

end own

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
