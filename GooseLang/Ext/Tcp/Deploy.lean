/-
The deployment's plan, well formed (D20; `Impl.lean`, D13) [Trusted definitions!]: a decidable
premise of every top-level theorem over the TCP extension, which `decide` checks on the concrete
plan. A plan is given as a list of (address, host) pairs; the extension's plan is its map
(`GMap.ofList`).

`PlanWellFormed l`: no address twice, and each address the canonical spelling `a.b.c.d:p` (decimal,
no leading zeros) of an IPv4 address that is not `0.0.0.0/8` (Linux's "this network", where a
`Dial` reaches the local host) and below `224.0.0.0` (multicast, reserved, broadcast: no TCP
connection), and a port in 1-32767 or 61000-65535, outside Linux's default ephemeral range
(`net.ipv4.ip_local_port_range`, 32768-60999): a `Dial` to a port with no listener cannot then
connect to itself (TCP's simultaneous open with its own ephemeral port, which Go's `selfConnect`
guard retries only twice, `tcpsock_posix.go`). Canonical spellings of distinct `IP:port` pairs name
distinct sockets, and none is a wildcard or a hostname, so no two plan strings alias
(`examples/net/semantics/addr_test.go`, `TestAddressAliases`). Loopback (`127.0.0.0/8`) is allowed:
the examples' nodes run on one machine.

The other half of D13, the closed world (no process outside the system uses the plan's
addresses), is a property of the machine, not of the plan, and stays prose.
-/
module

public import GooseLang.Ext.Tcp.Impl

@[expose] public section

namespace Perennial

namespace Tcp

/-- `c` is an ASCII decimal digit. -/
def isDigit (c : w8) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The value of the decimal digits `s` after `acc`, if they are all digits. -/
def digitsVal : GoString → Nat → Option Nat
  | [], acc => some acc
  | c :: s, acc => if isDigit c then digitsVal s (acc * 10 + (c.toNat - 48)) else none

/-- The value of a canonical decimal numeral: digits, at least one, no leading zero. -/
def decNat : GoString → Option Nat
  | [] => none
  | [c] => digitsVal [c] 0
  | c :: d :: s => if c.toNat = 48 then none else digitsVal (c :: d :: s) 0

/-- `s` split at every `sep` (`cur`: the current piece, reversed). -/
def splitBy (sep : w8) : GoString → GoString → List GoString
  | [], cur => [cur.reverse]
  | c :: s, cur => if c.toNat = sep.toNat then cur.reverse :: splitBy sep s [] else splitBy sep s (c :: cur)

/-- `a` as a canonical `a.b.c.d:p`: its four octets' values and its port's. -/
def parseAddr (a : GoString) : Option (Nat × Nat × Nat × Nat × Nat) :=
  match splitBy 58 a [] with
  | [ip, p] =>
    match splitBy 46 ip [] with
    | [x1, x2, x3, x4] =>
      match decNat x1, decNat x2, decNat x3, decNat x4, decNat p with
      | some n1, some n2, some n3, some n4, some port => some (n1, n2, n3, n4, port)
      | _, _, _, _, _ => none
    | _ => none
  | _ => none

/-- `a` is a well-formed plan address (the file header). -/
def addrOk (a : GoString) : Bool :=
  match parseAddr a with
  | some (n1, n2, n3, n4, p) =>
    1 ≤ n1 && n1 < 224 && n2 ≤ 255 && n3 ≤ 255 && n4 ≤ 255 &&
      1 ≤ p && p ≤ 65535 && (p < 32768 || 60999 < p)
  | none => false

/-- No two pairs of `l` have the same address. -/
def keysDistinct : List (GoString × GoString) → Bool
  | [] => true
  | (a, _) :: l => l.all (fun x => !(x.1 == a)) && keysDistinct l

/-- D20. The plan `l` is well formed (the file header). -/
def PlanWellFormed (l : List (GoString × GoString)) : Prop :=
  (keysDistinct l && l.all (fun x => addrOk x.1)) = true

instance (l : List (GoString × GoString)) : Decidable (PlanWellFormed l) := by
  unfold PlanWellFormed; infer_instance

/-- Every address of a well-formed plan's map is well formed. -/
theorem PlanWellFormed.addrOk {l : List (GoString × GoString)} (h : PlanWellFormed l) (a : GoString)
    (ha : ((GMap.ofList l) !! a).isSome) : addrOk a = true := by
  unfold PlanWellFormed at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨-, h⟩ := h
  induction l with
  | nil => simp [GMap.ofList] at ha; cases ha
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    simp only [GMap.ofList] at ha
    by_cases hk : k = a
    · subst hk; exact h (k, v) List.mem_cons_self
    · rw [GMap.lookup_insert_ne _ _ hk] at ha
      exact ih ha (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The examples' plans (`examples/net/README.md`: `127.0.0.1:71xx`, one address each). -/
example : PlanWellFormed [(go!"127.0.0.1:7101", go!"h")] := by decide
example : PlanWellFormed [(go!"127.0.0.1:7101", go!"s"), (go!"127.0.0.1:7102", go!"s"),
    (go!"127.0.0.1:7103", go!"s"), (go!"127.0.0.1:7104", go!"s"), (go!"127.0.0.1:7105", go!"s"),
    (go!"127.0.0.1:7106", go!"s"), (go!"127.0.0.1:7107", go!"s")] := by decide

/-- Excluded: a wildcard, a hostname, a leading zero, an ephemeral port, port 0, `0.0.0.0/8`,
multicast, a duplicate. -/
example : ¬ PlanWellFormed [(go!":7101", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"localhost:7101", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"127.0.0.01:7101", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"127.0.0.1:40000", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"127.0.0.1:0", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"0.1.2.3:7101", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"224.0.0.1:7101", go!"h")] := by decide
example : ¬ PlanWellFormed [(go!"127.0.0.1:7101", go!"h"), (go!"127.0.0.1:7101", go!"g")] := by
  decide

end Tcp

end Perennial
