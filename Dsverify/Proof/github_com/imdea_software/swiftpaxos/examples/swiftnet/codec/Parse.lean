/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Parse.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The parsers of the kit's codec (`examples/swiftnet/rpc_gen.go`'s `rpcDec_*`), as pure functions
on byte lists, following the Go code step by step: each returns the decoded value and the rest
of the input, or `none` where the Go function returns `ok = false`. The decoders' specs
(`Dec*.lean`) say each Go decoder computes its parser; the round-trip lemmas (`RoundTrip.lean`)
say each parser inverts the encoding of `Spec/swift/Wire.lean`.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.examples.swiftnet
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

section parse
variable [GooseExts]

/-- `rpcGetU64`: 8 bytes little-endian. -/
def pU64 (bs : List w8) : Option (w64 × List w8) :=
  if 8 ≤ bs.length then some (leToU64 (bs.take 8), bs.drop 8) else none

/-- `rpcDec_int`, `rpcDec_int64`, `rpcDec_state_Key`: any 64-bit word. -/
abbrev pInt (bs : List w8) : Option (w64 × List w8) := pU64 bs

/-- `rpcDec_int32`: a word in `int32`'s range. -/
def pI32 (bs : List w8) : Option (w32 × List w8) :=
  match pU64 bs with
  | some (x, r) => if -2147483648 ≤ sint.Z x ∧ sint.Z x ≤ 2147483647 then
      some (W32 (sint.Z x), r) else none
  | none => none

/-- `rpcDec_uint8`, `rpcDec_state_Operation`: a word below 256. -/
def pU8 (bs : List w8) : Option (w8 × List w8) :=
  match pU64 bs with
  | some (x, r) => if uint.Z x < 256 then some (W8 (uint.Z x), r) else none
  | none => none

/-- `rpcDec_bool`: one byte, 0 or 1. -/
def pBool (bs : List w8) : Option (Bool × List w8) :=
  match bs with
  | b :: r => if uint.Z b ≤ 1 then some (decide (b = W8 1), r) else none
  | [] => none

/-- `rpcDec_string`, `rpcDec_S_byte`: a count, then that many bytes. -/
def pBytes (bs : List w8) : Option (List w8 × List w8) :=
  match pU64 bs with
  | some (n, r) => if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n))
      else none
  | none => none

/-- `n` values with `p`, one after the other. -/
def pRep {A : Type} (p : List w8 → Option (A × List w8)) : Nat → List w8 → Option (List A × List w8)
  | 0, r => some ([], r)
  | n + 1, r => match p r with
    | some (x, r') => match pRep p n r' with
      | some (xs, r'') => some (x :: xs, r'')
      | none => none
    | none => none

/-- `rpcDec_S_*`: a count (at most the rest's length), then that many values. -/
def pList {A : Type} (p : List w8 → Option (A × List w8)) (bs : List w8) :
    Option (List A × List w8) :=
  match pU64 bs with
  | some (n, r) => if uint.nat n ≤ r.length then pRep p (uint.nat n) r else none
  | none => none

end parse

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

theorem pRep_succ {A : Type} (p : List w8 → Option (A × List w8)) (n : Nat) (r : List w8) :
    pRep p (n + 1) r = (match pRep p n r with
      | some (xs, r') => match p r' with
        | some (x, r'') => some (xs ++ [x], r'')
        | none => none
      | none => none) := by
  induction n generalizing r with
  | zero =>
    simp only [pRep]
    rcases p r with _ | ⟨x, r'⟩ <;> simp
  | succ n ih =>
    rw [pRep]
    conv => rhs; rw [pRep]
    rcases hp : p r with _ | ⟨x, r'⟩
    · simp
    · simp only
      rw [ih r']
      rcases pRep p n r' with _ | ⟨xs, r''⟩
      · simp
      · simp only
        rcases p r'' with _ | ⟨y, r'''⟩ <;> simp

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

theorem pRep_none_add {A : Type} (p : List w8 → Option (A × List w8)) (m k : Nat) (r : List w8)
    (h : pRep p m r = none) : pRep p (m + k) r = none := by
  induction k with
  | zero => exact h
  | succ k ih => rw [← Nat.add_assoc, pRep_succ, ih]

theorem pRep_none_le {A : Type} (p : List w8 → Option (A × List w8)) (m n : Nat) (r : List w8)
    (h : pRep p m r = none) (hmn : m ≤ n) : pRep p n r = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact pRep_none_add p m k r h

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section parse2
variable [GooseExts]

instance cmdIdDecEq : DecidableEq swift.CommandId := fun a b =>
  decidable_of_iff (a.ClientId' = b.ClientId' ∧ a.SeqNum' = b.SeqNum') (by
    cases a; cases b; simp)

/-- `rpcDec_swift_CommandId`: two `int32`s. -/
def pCmdId (bs : List w8) : Option (swift.CommandId × List w8) :=
  match pI32 bs with
  | some (c, r) => match pI32 r with
    | some (s, r') => some (⟨c, s⟩, r')
    | none => none
  | none => none

end parse2
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section parse3
variable [GooseExts]

/-- `rpcDec_state_Command`: operation, key, value. -/
def pCmd (bs : List w8) : Option (sp.Cmd × List w8) :=
  match pU8 bs with
  | some (op, r) => match pInt r with
    | some (k, r') => match pBytes r' with
      | some (v, r'') => some (⟨op, k, v⟩, r'')
      | none => none
    | none => none
  | none => none

/-- A map entry: its key (`rpcDec_swift_CommandId`), then its value. -/
def pEntry {V : Type} (pv : List w8 → Option (V × List w8)) (bs : List w8) :
    Option ((swift.CommandId × V) × List w8) :=
  match pCmdId bs with
  | some (k, r) => match pv r with
    | some (v, r') => some ((k, v), r')
    | none => none
  | none => none

/-- The entries of a Go map after inserting `es` in order into an empty map (`v[x] = y`): a
later entry of a key replaces the earlier one in place. -/
def insertAll {V : Type} (es : List (swift.CommandId × V)) : List (swift.CommandId × V) :=
  es.foldl (fun acc e => map.insertL e.1 e.2 acc) []

/-- `rpcDec_map_swift_CommandId_*`: a count, then that many entries, inserted in order. -/
def pMap {V : Type} (pv : List w8 → Option (V × List w8)) (bs : List w8) :
    Option (List (swift.CommandId × V) × List w8) :=
  match pList (pEntry pv) bs with
  | some (es, r) => some (insertAll es, r)
  | none => none

/-- A map field of `rpcDec_swift_MSync`: a presence byte (0: nil, 1: a map follows). -/
def pOpt {A : Type} (p : List w8 → Option (A × List w8)) (bs : List w8) :
    Option (Option A × List w8) :=
  match bs with
  | b :: r => if uint.Z b ≤ 1 then
      (if b = W8 1 then (match p r with
        | some (a, r') => some (some a, r')
        | none => none) else some (none, r))
      else none
  | [] => none

/-- The Go contents of a decoded `MSync`: replica, ballot, and each map's entries (`none`: nil). -/
structure SyncVal where
  rep : w32
  bal : w32
  phases : Option (List (swift.CommandId × w64))
  cmds : Option (List (swift.CommandId × sp.Cmd))
  deps : Option (List (swift.CommandId × List swift.CommandId))

/-- `rpcDec_swift_MSync`. -/
def pMSync (bs : List w8) : Option (SyncVal × List w8) :=
  match pI32 bs with
  | some (rep, r0) => match pI32 r0 with
    | some (bal, r1) => match pOpt (pMap pInt) r1 with
      | some (ph, r2) => match pOpt (pMap pCmd) r2 with
        | some (cm, r3) => match pOpt (pMap (pList pCmdId)) r3 with
          | some (dp, r4) => some (⟨rep, bal, ph, cm, dp⟩, r4)
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

end parse3
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section parse4
variable [GooseExts]

theorem insertAll_snoc {V : Type} (es : List (swift.CommandId × V)) (e : swift.CommandId × V) :
    insertAll (es ++ [e]) = map.insertL e.1 e.2 (insertAll es) := by
  simp [insertAll, List.foldl_append]

end parse4
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section parse5
variable [GooseExts]
open sp

/-- `rpcDec_defs_RegisterArgs`. -/
def pRegisterArgs (bs : List w8) : Option (KitVal × List w8) :=
  match pBytes bs with
  | some (a, r) => match pInt r with
    | some (p, r') => some (.registerArgs a p, r')
    | none => none
  | none => none

/-- `rpcDec_defs_RegisterReply`. -/
def pRegisterReply (bs : List w8) : Option (KitVal × List w8) :=
  match pInt bs with
  | some (i, r0) => match pList pBytes r0 with
    | some (ns, r1) => match pBool r1 with
      | some (rd, r2) => match pBool r2 with
        | some (il, r3) => some (.registerReply i ns rd il, r3)
        | none => none
      | none => none
    | none => none
  | none => none

/-- `rpcDec_defs_GetLeaderReply`. -/
def pGetLeaderReply (bs : List w8) : Option (KitVal × List w8) :=
  match pInt bs with
  | some (i, r) => some (.getLeaderReply i, r)
  | none => none

/-- `rpcDec_defs_GetReplicaListReply`. -/
def pGetReplicaListReply (bs : List w8) : Option (KitVal × List w8) :=
  match pList pBytes bs with
  | some (rs, r0) => match pList pBool r0 with
    | some (al, r1) => match pBool r1 with
      | some (rd, r2) => some (.getReplicaListReply rs al rd, r2)
      | none => none
    | none => none
  | none => none

/-- `rpcDec_defs_PingArgs`. -/
def pPingArgs (bs : List w8) : Option (KitVal × List w8) :=
  match pU8 bs with
  | some (a, r) => some (.pingArgs a, r)
  | none => none

/-- `rpcDec_defs_BeTheLeaderReply`. -/
def pBeTheLeaderReply (bs : List w8) : Option (KitVal × List w8) :=
  match pI32 bs with
  | some (l, r0) => match pI32 r0 with
    | some (n, r1) => some (.beTheLeaderReply l n, r1)
    | none => none
  | none => none

/-- The decoders of the field-less types: nothing read. -/
def pEmpty (x : KitVal) (bs : List w8) : Option (KitVal × List w8) := some (x, bs)

end parse5
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section parse6
variable [GooseExts]
open sp

/-- The value is well formed (`KitVal.wf` of `Spec/swiftnet/Codec.lean`): an `MSync`'s map
listings have distinct keys. -/
def kitWf : KitVal → Prop
  | .msync m => (m.phases.map (fun l => (l.map Prod.fst).Nodup)).getD True ∧
      (m.cmds.map (fun l => (l.map Prod.fst).Nodup)).getD True ∧
      (m.deps.map (fun l => (l.map Prod.fst).Nodup)).getD True
  | _ => True

end parse6
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
