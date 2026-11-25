/-
# kvraft-udp's datagrams, pure (2026-11-24, `notes/kvraft-udp-proof-plan.md`)

The pure models of `udptransport.go`'s datagram format and of its address parsing, which the specs of
`putHeader`, `putFragment`, `putAck`, `getDatagram`, `fragments`, `parseAddr` and `udpAddr` are stated
in, and the laws the transport's proofs use.

* `headerBytes`, `fragBytes`, `ackBytes`: what `putHeader`, `putFragment`, `putAck` write.
* `DgM`, `parseDg b`: what `getDatagram(b)` reads back (`none`: `ok` false). `DgM.key`: the message a
  fragment names, `(from, boot, seq)`.
* `nChunks body`, `chunkAt body i`, `fragsOf src dst boot seq body`: `fragments`' chunking (`[]`: Go's
  `nil`, a body that is empty or needs more than `maxFragmentsN` chunks).
* `FragOf body dg`: the fragment `dg` is the `dg.index`-th chunk of `body`, of `nChunks body`.
* `bootVal v n`: the boot counter's file contents `v` (`durable`'s, `none`: no file) hold `n`.
* `parseAddrM a`: `parseAddr(a)`: the IPv4 bytes and port of an address `Net.addrOk` accepts.

The laws: `parseDg_fragBytes`/`parseDg_ackBytes` (round trips), `parseDg_length` (whatever parses is
at most `maxDatagramN` bytes: what arrives intact, `Udp.intactMax`), `fragsOf_ok` (every fragment of a
body parses as one of its chunks, and is short enough), `chunks_flatten` (the chunks, in order, are
the body), `parseAddrM_ok` (`ValidDest` from `addrOk`).
-/
module

public import GooseLang.Ext.Udp.Impl
public import Perennial.Std.Word.LittleEndian
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpAddr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Net Udp

/-! ## The format's constants (`udptransport.go`) -/

/-- `maxDatagram`: the largest datagram sent (`Udp.intactMax`: it arrives intact). -/
def maxDatagramN : Nat := 524
/-- `chunkSize`: a fragment's largest chunk. -/
def chunkSizeN : Nat := 479
/-- `ackLen`: the header's length, an ack's. -/
def ackLenN : Nat := 37
/-- `fragHeaderLen`: a fragment's length before its chunk. -/
def fragHeaderLenN : Nat := 45
/-- `maxFragments`: the most fragments of a message. -/
def maxFragmentsN : Nat := 2 ^ 14
/-- `udpMagic`. -/
def udpMagicW : w32 := W32 0x4455564b
/-- `kindFragment`. -/
def kindFragmentB : w8 := W8 1
/-- `kindAck`. -/
def kindAckB : w8 := W8 2

theorem maxDatagramN_intact : maxDatagramN = intactMax := rfl

/-! ## Writing -/

/-- `putHeader`'s bytes. -/
def headerBytes (kind : w8) (src dst boot seq : w64) : List w8 :=
  u32Le udpMagicW ++ [kind] ++ u64Le src ++ u64Le dst ++ u64Le boot ++ u64Le seq

/-- `putFragment`'s bytes. -/
def fragBytes (src dst boot seq : w64) (index total : w32) (chunk : List w8) : List w8 :=
  headerBytes kindFragmentB src dst boot seq ++ u32Le index ++ u32Le total ++ chunk

/-- `putAck`'s bytes. -/
def ackBytes (src dst boot seq : w64) : List w8 := headerBytes kindAckB src dst boot seq

/-! ## Reading -/

/-- A datagram read back (`getDatagram`'s `datagram`; `src` is Go's `from`, `dst` its `to`). An ack's
`index`, `total` are 0 and its `chunk` empty (Go's nil). -/
structure DgM where
  kind : w8
  src : w64
  dst : w64
  boot : w64
  seq : w64
  index : w32
  total : w32
  chunk : List w8

/-- The message a datagram names: its sender, boot and sequence numbers. -/
def DgM.key (d : DgM) : w64 × w64 × w64 := (d.src, d.boot, d.seq)

/-- The 8 bytes of `b` at `off`, as a little-endian word. -/
def u64At (b : List w8) (off : Nat) : w64 := leToU64 ((b.drop off).take 8)

/-- The 4 bytes of `b` at `off`, as a little-endian word. -/
def u32At (b : List w8) (off : Nat) : w32 := leToU32 ((b.drop off).take 4)

/-- **`getDatagram(b)`** (see the file header): the datagram, or `none` for anything `putFragment` or
`putAck` did not write (a fragment's chunk empty or longer than `chunkSizeN`, its index not below its
total, its total 0 or above `maxFragmentsN`). -/
def parseDg (b : List w8) : Option DgM :=
  if b.length < ackLenN ∨ u32At b 0 ≠ udpMagicW then none
  else
    let kind := b.getD 4 0
    let src := u64At b 5
    let dst := u64At b 13
    let boot := u64At b 21
    let seq := u64At b 29
    if kind = kindAckB then
      if b.length = ackLenN then some ⟨kind, src, dst, boot, seq, 0, 0, []⟩ else none
    else if kind ≠ kindFragmentB ∨ b.length ≤ fragHeaderLenN ∨
        fragHeaderLenN + chunkSizeN < b.length then none
    else
      let index := u32At b ackLenN
      let total := u32At b (ackLenN + 4)
      if total.toNat = 0 ∨ maxFragmentsN < total.toNat ∨ total.toNat ≤ index.toNat then none
      else some ⟨kind, src, dst, boot, seq, index, total, b.drop fragHeaderLenN⟩

/-! ## Chunking -/

/-- How many chunks `body` is cut into. -/
def nChunks (body : List w8) : Nat := (body.length + chunkSizeN - 1) / chunkSizeN

/-- The `i`-th chunk of `body`. -/
def chunkAt (body : List w8) (i : Nat) : List w8 := (body.drop (i * chunkSizeN)).take chunkSizeN

/-- **`fragments(src, dst, boot, seq, body)`**: the fragments of the message, `[]` (Go's nil) if
`body` is empty or needs more than `maxFragmentsN` of them. -/
def fragsOf (src dst boot seq : w64) (body : List w8) : List (List w8) :=
  if nChunks body = 0 ∨ maxFragmentsN < nChunks body then []
  else (List.range (nChunks body)).map fun (i : Nat) =>
    fragBytes src dst boot seq (W32 (i : Int)) (W32 ((nChunks body : Nat) : Int)) (chunkAt body i)

/-- **The fragment `dg` is a chunk of `body`** (see the file header). -/
def FragOf (body : List w8) (dg : DgM) : Prop :=
  dg.kind = kindFragmentB ∧ dg.total.toNat = nChunks body ∧
    dg.index.toNat < nChunks body ∧ dg.chunk = chunkAt body dg.index.toNat

/-! ## The boot counter's file -/

/-- **The boot counter's file contents `v` hold `n`** (`nextBoot`): no file and `n = 0`, or the 8
bytes of `n`. -/
def bootVal (v : Option GoString) (n : w64) : Prop :=
  (v = none ∧ n = W64 0) ∨ v = some (u64Le n)

/-! ## Addresses -/

/-- **`parseAddr(a)`**: the IPv4 bytes and the port of `a`, if `Net.addrOk` accepts it; Go's `ok` is
`(parseAddrM a).isSome`. The bytes are the address's four numerals, the port its fifth. -/
def parseAddrM (a : GoString) : Option (List w8 × w64) :=
  if addrOk a = true then
    match (splitBy 58 a []) with
    | [h, p] =>
      match (splitBy 46 h []).map decNat, decNat p with
      | [some b1, some b2, some b3, some b4], some pt =>
        some ([W8 b1, W8 b2, W8 b3, W8 b4], W64 pt)
      | _, _ => none
    | _ => none
  else none

/-! ## The laws (phase 2) -/

theorem fragBytes_length (src dst boot seq : w64) (index total : w32) (chunk : List w8) :
    (fragBytes src dst boot seq index total chunk).length = fragHeaderLenN + chunk.length := by
  simp only [fragBytes, headerBytes, List.length_append, u32Le_length, u64Le_length, List.length_cons,
    List.length_nil, fragHeaderLenN]
  try omega

theorem ackBytes_length (src dst boot seq : w64) :
    (ackBytes src dst boot seq).length = ackLenN := by
  simp only [ackBytes, headerBytes, List.length_append, u32Le_length, u64Le_length, List.length_cons,
    List.length_nil, ackLenN]

/-- What `putFragment` writes, `getDatagram` reads back. -/
theorem parseDg_fragBytes (src dst boot seq : w64) (index total : w32) (chunk : List w8)
    (hc : chunk ≠ []) (hcl : chunk.length ≤ chunkSizeN) (ht : 0 < total.toNat)
    (htm : total.toNat ≤ maxFragmentsN) (hi : index.toNat < total.toNat) :
    parseDg (fragBytes src dst boot seq index total chunk) =
      some ⟨kindFragmentB, src, dst, boot, seq, index, total, chunk⟩ := by
  have key64 : ∀ (b A C : List w8) (x : w64) (n : Nat), b = A ++ (u64Le x ++ C) → A.length = n →
      u64At b n = x := by
    intro b A C x n hb hn; subst hb hn; unfold u64At
    rw [List.drop_left, List.take_left' (u64Le_length x)]; exact u64Le_to_word x
  have key32 : ∀ (b A C : List w8) (x : w32) (n : Nat), b = A ++ (u32Le x ++ C) → A.length = n →
      u32At b n = x := by
    intro b A C x n hb hn; subst hb hn; unfold u32At
    rw [List.drop_left, List.take_left' (u32Le_length x)]; exact u32Le_to_word x
  have keyB : ∀ (b A C : List w8) (k : w8) (n : Nat), b = A ++ (k :: C) → A.length = n →
      b.getD n 0 = k := by
    intro b A C k n hb hn; subst hb hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hL : fragBytes src dst boot seq index total chunk =
      u32Le udpMagicW ++ (kindFragmentB :: (u64Le src ++ (u64Le dst ++ (u64Le boot ++
        (u64Le seq ++ (u32Le index ++ (u32Le total ++ chunk))))))) := by
    simp [fragBytes, headerBytes]
  have hlen := fragBytes_length src dst boot seq index total chunk
  have hm := key32 (fragBytes src dst boot seq index total chunk) [] (kindFragmentB :: (u64Le src ++ (u64Le dst ++ (u64Le boot ++
        (u64Le seq ++ (u32Le index ++ (u32Le total ++ chunk))))))) udpMagicW 0 (by rw [hL]; simp) rfl
  have hk := keyB (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW) (u64Le src ++ (u64Le dst ++ (u64Le boot ++
        (u64Le seq ++ (u32Le index ++ (u32Le total ++ chunk)))))) kindFragmentB 4 hL (u32Le_length _)
  have hs := key64 (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW ++ [kindFragmentB]) (u64Le dst ++ (u64Le boot ++
        (u64Le seq ++ (u32Le index ++ (u32Le total ++ chunk))))) src 5 (by rw [hL]; simp)
    (by simp [u32Le_length])
  have hd := key64 (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW ++ [kindFragmentB] ++ u64Le src) (u64Le boot ++
        (u64Le seq ++ (u32Le index ++ (u32Le total ++ chunk)))) dst 13 (by rw [hL]; simp)
    (by simp [u32Le_length, u64Le_length])
  have hbo := key64 (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW ++ [kindFragmentB] ++ u64Le src ++ u64Le dst)
    (u64Le seq ++ (u32Le index ++ (u32Le total ++ chunk))) boot 21 (by rw [hL]; simp)
    (by simp [u32Le_length, u64Le_length])
  have hse := key64 (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW ++ [kindFragmentB] ++ u64Le src ++ u64Le dst ++ u64Le boot)
    (u32Le index ++ (u32Le total ++ chunk)) seq 29 (by rw [hL]; simp)
    (by simp [u32Le_length, u64Le_length])
  have hix := key32 (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW ++ [kindFragmentB] ++ u64Le src ++ u64Le dst ++ u64Le boot ++
    u64Le seq) (u32Le total ++ chunk) index 37 (by rw [hL]; simp)
    (by simp [u32Le_length, u64Le_length])
  have hto := key32 (fragBytes src dst boot seq index total chunk) (u32Le udpMagicW ++ [kindFragmentB] ++ u64Le src ++ u64Le dst ++ u64Le boot ++
    u64Le seq ++ u32Le index) chunk total 41 (by rw [hL]; simp)
    (by simp [u32Le_length, u64Le_length])
  have hdr : (fragBytes src dst boot seq index total chunk).drop fragHeaderLenN = chunk := by
    have e : fragBytes src dst boot seq index total chunk = (u32Le udpMagicW ++ [kindFragmentB] ++
        u64Le src ++ u64Le dst ++ u64Le boot ++ u64Le seq ++ u32Le index ++ u32Le total) ++ chunk := by
      rw [hL]; simp
    rw [e, List.drop_left']
    simp [u32Le_length, u64Le_length, fragHeaderLenN]
  generalize fragBytes src dst boot seq index total chunk = b at *
  have h1 : ¬(b.length < ackLenN ∨ u32At b 0 ≠ udpMagicW) := by
    rw [hm, hlen]; simp only [ne_eq, not_true_eq_false, or_false, ackLenN, fragHeaderLenN]; omega
  have h2 : ¬(kindFragmentB = kindAckB) := by decide
  have h3 : ¬(kindFragmentB ≠ kindFragmentB ∨ b.length ≤ fragHeaderLenN ∨
      fragHeaderLenN + chunkSizeN < b.length) := by
    rw [hlen]; simp only [ne_eq, not_true_eq_false, false_or, not_or]
    have : chunk.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    constructor <;> omega
  have h4 : ¬(total.toNat = 0 ∨ maxFragmentsN < total.toNat ∨ total.toNat ≤ index.toNat) := by omega
  unfold parseDg
  rw [if_neg h1]
  try dsimp only
  rw [hk, if_neg h2, if_neg h3]
  try dsimp only
  rw [show ackLenN + 4 = 41 from rfl, show ackLenN = 37 from rfl]
  rw [hix, hto, if_neg h4, hs, hd, hbo, hse, hdr]

/-- What `putAck` writes, `getDatagram` reads back. -/
theorem parseDg_ackBytes (src dst boot seq : w64) :
    parseDg (ackBytes src dst boot seq) = some ⟨kindAckB, src, dst, boot, seq, 0, 0, []⟩ := by
  have key64 : ∀ (b A C : List w8) (x : w64) (n : Nat), b = A ++ (u64Le x ++ C) → A.length = n →
      u64At b n = x := by
    intro b A C x n hb hn; subst hb hn; unfold u64At
    rw [List.drop_left, List.take_left' (u64Le_length x)]; exact u64Le_to_word x
  have key32 : ∀ (b A C : List w8) (x : w32) (n : Nat), b = A ++ (u32Le x ++ C) → A.length = n →
      u32At b n = x := by
    intro b A C x n hb hn; subst hb hn; unfold u32At
    rw [List.drop_left, List.take_left' (u32Le_length x)]; exact u32Le_to_word x
  have keyB : ∀ (b A C : List w8) (k : w8) (n : Nat), b = A ++ (k :: C) → A.length = n →
      b.getD n 0 = k := by
    intro b A C k n hb hn; subst hb hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hL : ackBytes src dst boot seq =
      u32Le udpMagicW ++ (kindAckB :: (u64Le src ++ (u64Le dst ++ (u64Le boot ++ (u64Le seq ++ []))))) := by
    simp [ackBytes, headerBytes]
  have hlen := ackBytes_length src dst boot seq
  have hm := key32 (ackBytes src dst boot seq) [] (kindAckB :: (u64Le src ++ (u64Le dst ++ (u64Le boot ++ (u64Le seq ++ []))))) udpMagicW
    0 (by rw [hL]; simp) rfl
  have hk := keyB (ackBytes src dst boot seq) (u32Le udpMagicW) (u64Le src ++ (u64Le dst ++ (u64Le boot ++ (u64Le seq ++ []))))
    kindAckB 4 hL (u32Le_length _)
  have hs := key64 (ackBytes src dst boot seq) (u32Le udpMagicW ++ [kindAckB]) (u64Le dst ++ (u64Le boot ++ (u64Le seq ++ [])))
    src 5 (by rw [hL]; simp) (by simp [u32Le_length])
  have hd := key64 (ackBytes src dst boot seq) (u32Le udpMagicW ++ [kindAckB] ++ u64Le src) (u64Le boot ++ (u64Le seq ++ []))
    dst 13 (by rw [hL]; simp) (by simp [u32Le_length, u64Le_length])
  have hbo := key64 (ackBytes src dst boot seq) (u32Le udpMagicW ++ [kindAckB] ++ u64Le src ++ u64Le dst) (u64Le seq ++ [])
    boot 21 (by rw [hL]; simp) (by simp [u32Le_length, u64Le_length])
  have hse := key64 (ackBytes src dst boot seq) (u32Le udpMagicW ++ [kindAckB] ++ u64Le src ++ u64Le dst ++ u64Le boot) []
    seq 29 (by rw [hL]; simp) (by simp [u32Le_length, u64Le_length])
  generalize ackBytes src dst boot seq = b at *
  have h1 : ¬(b.length < ackLenN ∨ u32At b 0 ≠ udpMagicW) := by
    rw [hm, hlen]; simp only [ne_eq, not_true_eq_false, or_false]; omega
  unfold parseDg
  rw [if_neg h1]
  try dsimp only
  rw [hk, if_pos rfl, if_pos hlen, hs, hd, hbo, hse]

/-- What parses is short enough to arrive intact. -/
theorem parseDg_length {b : List w8} {dg : DgM} (h : parseDg b = some dg) :
    b.length ≤ maxDatagramN := by
  unfold parseDg at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · next hl => rw [hl]; decide
      · cases h
    · split at h
      · cases h
      · next h3 =>
        simp only [not_or, Nat.not_lt] at h3
        unfold maxDatagramN
        unfold fragHeaderLenN chunkSizeN at h3
        omega

/-- What parses is an ack or a fragment. -/
theorem parseDg_kind {b : List w8} {dg : DgM} (h : parseDg b = some dg) :
    dg.kind = kindAckB ∨ (dg.kind = kindFragmentB ∧ dg.index.toNat < dg.total.toNat) := by
  unfold parseDg at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · next hk =>
      split at h
      · cases h; exact Or.inl hk
      · cases h
    · next hk =>
      split at h
      · cases h
      · next h3 =>
        split at h
        · cases h
        · next h4 =>
          cases h
          simp only [not_or, ne_eq, Decidable.not_not, Nat.not_le] at h3 h4
          exact Or.inr ⟨h3.1, h4.2.2⟩

/-- Every fragment of a body is short enough and parses as one of its chunks, under the message's
name. -/
theorem fragsOf_ok (src dst boot seq : w64) (body : List w8) :
    ∀ d ∈ fragsOf src dst boot seq body, d.length ≤ maxDatagramN ∧
      ∃ dg, parseDg d = some dg ∧ dg.key = (src, boot, seq) ∧ dg.dst = dst ∧ FragOf body dg := by
  intro d hd
  unfold fragsOf at hd
  split at hd
  · simp at hd
  · next hn =>
    simp only [not_or, Nat.not_lt] at hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have hi' : i < nChunks body := List.mem_range.mp hi
    have hne : chunkAt body i ≠ [] := by
      have hi2 := hi'
      unfold nChunks chunkSizeN at hi2
      unfold chunkAt chunkSizeN
      intro h
      have := congrArg List.length h
      simp only [List.length_take, List.length_drop, List.length_nil] at this
      omega
    have hcl : (chunkAt body i).length ≤ chunkSizeN := by
      unfold chunkAt chunkSizeN; simp only [List.length_take]; omega
    have hmax : maxFragmentsN = 16384 := rfl
    have hit : (W32 (i : Int)).toNat = i := by
      simp only [W32, BitVec.toNat_ofInt]; omega
    have hnt : (W32 ((nChunks body : Nat) : Int)).toNat = nChunks body := by
      simp only [W32, BitVec.toNat_ofInt]; omega
    refine ⟨by rw [fragBytes_length]; unfold fragHeaderLenN maxDatagramN; unfold chunkSizeN at hcl; omega,
      _, parseDg_fragBytes _ _ _ _ _ _ _ hne hcl (by omega) (by omega) (by omega), rfl, rfl, ?_⟩
    refine ⟨rfl, hnt, by simp only [hit]; exact hi', ?_⟩
    simp only [hit]

/-- `fragments` gives nil only for an empty body or one too long. -/
theorem fragsOf_nil (src dst boot seq : w64) (body : List w8) :
    fragsOf src dst boot seq body = [] ↔ (body = [] ∨ maxFragmentsN < nChunks body) := by
  have hn : nChunks body = 0 ↔ body = [] := by
    unfold nChunks chunkSizeN
    constructor
    · intro h; apply List.eq_nil_of_length_eq_zero; omega
    · intro h; subst h; rfl
  unfold fragsOf
  split
  · next h =>
    simp only [true_iff]
    rcases h with h | h
    · exact Or.inl (hn.1 h)
    · exact Or.inr h
  · next h =>
    simp only [List.map_eq_nil_iff, List.range_eq_nil]
    constructor
    · intro h'; exact absurd (Or.inl h') h
    · intro h'
      rcases h' with h' | h'
      · exact absurd (Or.inl (hn.2 h')) h
      · exact absurd (Or.inr h') h

/-- The chunks, in order, are the body. -/
theorem chunks_flatten (body : List w8) :
    ((List.range (nChunks body)).map (chunkAt body)).flatten = body := by
  have key : ∀ k, ((List.range k).map (chunkAt body)).flatten = body.take (k * chunkSizeN) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, ih, Nat.succ_mul, List.take_add]
      simp [chunkAt]
  rw [key]
  apply List.take_of_length_le
  unfold nChunks chunkSizeN
  omega

/-- A chunk of a body is nonempty and at most `chunkSizeN` bytes. -/
theorem chunkAt_length (body : List w8) (i : Nat) (hi : i < nChunks body) :
    chunkAt body i ≠ [] ∧ (chunkAt body i).length ≤ chunkSizeN := by
  unfold nChunks chunkSizeN at hi
  unfold chunkAt chunkSizeN
  constructor
  · intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_nil] at this
    omega
  · simp only [List.length_take]
    omega

/-- `parseAddr` accepts exactly what `AddrOk` does, and its bytes and port make the address. -/
theorem parseAddrM_ok (a : GoString) :
    (parseAddrM a).isSome = addrOk a ∧
      ∀ ip port, parseAddrM a = some (ip, port) → ValidDest ip port a ∧ ip.length = 4 := by
  by_cases hok : addrOk a = true
  · obtain ⟨h, p, x1, x2, x3, x4, n1, n2, n3, n4, pt, h58, h46, d1, d2, d3, d4, dp,
      b1, b2, b3, b4, b5, hpo⟩ := addrOk_parts hok
    have hP : parseAddrM a = some ([W8 (n1 : Int), W8 (n2 : Int), W8 (n3 : Int), W8 (n4 : Int)],
        W64 (pt : Int)) := by
      unfold parseAddrM
      rw [if_pos hok, h58]
      simp only [h46, List.map_cons, List.map_nil, d1, d2, d3, d4, dp]
    refine ⟨by rw [hP, hok]; rfl, ?_⟩
    intro ip port he
    rw [hP] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨⟨?_, hok⟩, rfl⟩
    have hpt : pt ≤ 65535 := by
      unfold portOk at hpo; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hpo
      omega
    have t1 : (W8 (n1 : Int)).toNat = n1 := by simp only [W8, BitVec.toNat_ofInt]; omega
    have t2 : (W8 (n2 : Int)).toNat = n2 := by simp only [W8, BitVec.toNat_ofInt]; omega
    have t3 : (W8 (n3 : Int)).toNat = n3 := by simp only [W8, BitVec.toNat_ofInt]; omega
    have t4 : (W8 (n4 : Int)).toNat = n4 := by simp only [W8, BitVec.toNat_ofInt]; omega
    have tp : (W64 (pt : Int)).toNat = pt := by simp only [W64, BitVec.toNat_ofInt]; omega
    unfold udpAddrOf ipv4Of
    simp only [List.length_cons, List.length_nil, ↓reduceIte, t1, t2, t3, t4, tp,
      show pt ≤ 65535 from hpt, decDigits_decNat d1, decDigits_decNat d2, decDigits_decNat d3,
      decDigits_decNat d4, decDigits_decNat dp]
    rw [addrOk_join h58 h46]
  · have hf : addrOk a = false := by simpa using hok
    refine ⟨by unfold parseAddrM; rw [if_neg hok, hf]; rfl, ?_⟩
    intro ip port he
    unfold parseAddrM at he
    rw [if_neg hok] at he
    cases he

/-- `parseAddr`'s result, from the address's parts (`addrOk_parts`). -/
theorem parseAddrM_parts {a h p x1 x2 x3 x4 : GoString} {n1 n2 n3 n4 pt : Nat} (hok : addrOk a = true)
    (h58 : splitBy 58 a [] = [h, p]) (h46 : splitBy 46 h [] = [x1, x2, x3, x4])
    (d1 : decNat x1 = some n1) (d2 : decNat x2 = some n2) (d3 : decNat x3 = some n3)
    (d4 : decNat x4 = some n4) (dp : decNat p = some pt) :
    parseAddrM a = some ([W8 (n1 : Int), W8 (n2 : Int), W8 (n3 : Int), W8 (n4 : Int)], W64 (pt : Int)) := by
  unfold parseAddrM
  rw [if_pos hok, h58]
  simp only [h46, List.map_cons, List.map_nil, d1, d2, d3, d4, dp]

end kvraft
end EtcdGrove
end Perennial
