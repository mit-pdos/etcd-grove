/-
**A cluster of any size: the members' vocabulary** (`examples/lib/etcdstart/members.go`; the
clusterN Scope, `notes/clusterN-scope.md`, 2026-11-15). Lean-first (no Rocq counterpart).

* `membersOf pfx k pb cb`: what `Members(pfx, k, pb, cb)` returns, member `i` (from `0`) named
  `pfx-i` with peer address `127.0.0.1:(pb+i)` and client address `127.0.0.1:(cb+i)` (the numbers
  `strconv.FormatUint`'s decimal form `decStr`, the sums `uint64`'s);
* `iuOf ms`, `urlsN ms m`: the initial cluster's URLs by name that `StartMembers` builds (each
  member's one peer URL `http://Peer`), and member `m`'s configuration's URLs (`StartMember`'s
  `Uok` for a cluster of any size: `urls3` for a list);
* `MemberG`: a member's ghost names (its id, the cluster's server raft names with its registry, its
  request names, its stand-in apply environment), what `StartMembers`' spec pairs with each member;
* the names' distinctness (`decStr_inj`), their UTF-8 (ASCII), and a generated loopback address a
  literal (`netAddrLit_loopback`, the clusterN Scope's probe D).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.strconv.FormatUintDefs
public import Proof.strconv.FormatIntDefs
public import Proof.unicode.utf8.Valid

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A member of `Members`' result (the Go struct `etcdstart.Member`). -/
abbrev GMember := github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Member

/-- **Member `i` of `Members(pfx, k, pb, cb)`**: named `pfx-i`, peer address `127.0.0.1:(pb+i)`,
client address `127.0.0.1:(cb+i)`. -/
def memberAt (pfx : GoString) (pb cb i : w64) : GMember :=
  ⟨pfx ++ go!"-" ++ decStr i, go!"127.0.0.1:" ++ decStr (pb + i), go!"127.0.0.1:" ++ decStr (cb + i)⟩

/-- **`Members(pfx, k, pb, cb)`'s result**: members `0` to `k - 1`. -/
def membersOf (pfx : GoString) (k : Nat) (pb cb : w64) : List GMember :=
  (List.range k).map (fun i : Nat => memberAt pfx pb cb (W64 (i : Int)))

theorem membersOf_length (pfx : GoString) (k : Nat) (pb cb : w64) :
    (membersOf pfx k pb cb).length = k := by
  simp [membersOf]

theorem membersOf_getElem (pfx : GoString) (k : Nat) (pb cb : w64) (i : Nat) (h : i < k) :
    (membersOf pfx k pb cb)[i]? = some (memberAt pfx pb cb (W64 (i : Int))) := by
  simp [membersOf, h]

theorem membersOf_succ (pfx : GoString) (k : Nat) (pb cb : w64) :
    membersOf pfx (k + 1) pb cb = membersOf pfx k pb cb ++ [memberAt pfx pb cb (W64 (k : Int))] := by
  simp [membersOf, List.range_succ]

/-- **One more member stored** (`Members`' loop step). -/
theorem membersOf_set (pfx : GoString) (pb cb : w64) (j k : Nat) (hj : j < k) (z : GMember) :
    (membersOf pfx j pb cb ++ List.replicate (k - j) z).set j (memberAt pfx pb cb (W64 (j : Int))) =
      membersOf pfx (j + 1) pb cb ++ List.replicate (k - (j + 1)) z := by
  rw [List.set_append_right _ _ (by rw [membersOf_length]; exact Nat.le_refl _)]
  rw [membersOf_length, Nat.sub_self, membersOf_succ, List.append_assoc]
  obtain ⟨d, hd⟩ : ∃ d, k - j = d + 1 := ⟨k - j - 1, by omega⟩
  rw [hd, show k - (j + 1) = d by omega, List.replicate_succ]
  rfl

/-- **The initial cluster's URLs by name** (`StartMembers`' map): a member's name to its one peer
URL `http://Peer`, any other name to none. -/
def iuOf (ms : List GMember) (n : GoString) : List _root_.Perennial.net.url.URL :=
  match ms.find? (fun m => decide (m.Name' = n)) with
  | some m => [httpURL m.Peer']
  | none => []

/-- **The URLs of member `m`'s configuration, in the cluster `ms`** (`StartMember`'s `Uok`, from
`StartMembers`; `urls3` for any number of members): its peer URLs `[http://Peer]`, its client URLs
`[http://Client]`, the initial cluster's map, whose keys are the members' names, and its URLs by
name `iuOf ms`. -/
def urlsN (ms : List GMember) (m : GMember) (U : BootURLs) : Prop :=
  U.peer = [httpURL m.Peer'] ∧ U.client = [httpURL m.Client'] ∧
    (∀ n, (U.initMap.lookup n).isSome ↔ n ∈ ms.map (·.Name')) ∧ U.initURLs = iuOf ms

/-- A member's URLs in `iuOf`, when the names are distinct. -/
theorem iuOf_mem (ms : List GMember) (hnd : (ms.map (·.Name')).Nodup) (m : GMember) (hm : m ∈ ms) :
    iuOf ms m.Name' = [httpURL m.Peer'] := by
  unfold iuOf
  induction ms with
  | nil => simp at hm
  | cons q ms ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hq : q = m
    · subst hq; simp
    · have hm' : m ∈ ms := (List.mem_cons.1 hm).resolve_left (Ne.symm hq)
      have hne : q.Name' ≠ m.Name' := fun e => hnd.1 (by rw [e]; exact List.mem_map_of_mem hm')
      simp only [hne, decide_false]
      exact ih hnd.2 hm'

/-- A member's name is not among those of the members before it (the names distinct). -/
theorem name_not_mem_take (ms : List GMember) (hnd : (ms.map (·.Name')).Nodup) (j : Nat)
    (m : GMember) (h : ms[j]? = some m) : m.Name' ∉ (ms.take j).map (·.Name') := by
  rw [← List.take_append_drop j ms, List.map_append, List.nodup_append] at hnd
  obtain ⟨-, -, hdisj⟩ := hnd
  intro hm
  have hd : m ∈ ms.drop j := List.mem_of_getElem? (i := 0) (by rw [List.getElem?_drop]; simpa using h)
  exact hdisj _ hm _ (List.mem_map_of_mem hd) rfl

/-- The names of the members up to one more. -/
theorem take_succ_names (ms : List GMember) (j : Nat) (m : GMember) (h : ms[j]? = some m) (n : GoString) :
    n ∈ (ms.take (j + 1)).map (·.Name') ↔ n ∈ (ms.take j).map (·.Name') ∨ n = m.Name' := by
  rw [List.take_succ, h]
  simp [or_comm, eq_comm]

theorem drop_cons_of_getElem? {α : Type _} (l : List α) (n : Nat) (x : α) (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hn

theorem set_replicate_snoc {α : Type _} (l : List α) (n : Nat) (z a : α) (h : l.length < n) :
    (l ++ List.replicate (n - l.length) z).set l.length a =
      (l ++ [a]) ++ List.replicate (n - (l.length + 1)) z := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.append_assoc]
  obtain ⟨d, hd⟩ : ∃ d, n - l.length = d + 1 := ⟨n - l.length - 1, by omega⟩
  rw [hd, show n - (l.length + 1) = d by omega, List.replicate_succ]
  rfl

/-! ## Decimal digits -/

theorem digitChar_digit (d : Nat) (hd : d < 10) :
    48 ≤ (digitChar d).toNat ∧ (digitChar d).toNat ≤ 57 ∧ (digitChar d).toNat - 48 = d := by
  unfold digitChar; rw [if_pos hd]; simp [W8]; omega

theorem decStr_digits (p : w64) : ∀ c ∈ decStr p, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro c hc
  rw [decStr_eq, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have := digitChar_digit d (baseDigits_lt 10 _ _ d hd)
  exact ⟨this.1, this.2.1⟩

theorem decStr_ascii (p : w64) : asciiStr (decStr p) := by
  intro c hc; have := decStr_digits p c hc; omega

theorem ascii_append {s t : GoString} (hs : asciiStr s) (ht : asciiStr t) : asciiStr (s ++ t) := by
  intro b hb
  rcases List.mem_append.1 hb with h | h
  · exact hs b h
  · exact ht b h

/-- **A member's name is valid UTF-8**, of an ASCII prefix. -/
theorem memberAt_name_utf8 (pfx : GoString) (hp : asciiStr pfx) (pb cb i : w64) :
    utf8Valid (memberAt pfx pb cb i).Name' :=
  utf8Valid_of_ascii _ (ascii_append (ascii_append hp (fun b hb => by
    simp only [List.mem_singleton] at hb; subst hb; decide)) (decStr_ascii i))

/-- A 64-bit number's decimal form has at most 65 digits (a loose bound: 20 would do). -/
theorem decStr_length_le (p : w64) : (decStr p).length ≤ 65 := by
  rw [decStr_eq, List.length_map]
  exact baseDigits_length_le 10 (by omega) 64 p.toNat p.isLt

/-- **A member's name is at most 200 bytes**, of a prefix of at most 134 (wal-fsfix, 2026-11-20: the
data directory's bound, `dirFits_memberDataDir`). -/
theorem memberAt_name_len (pfx : GoString) (hp : pfx.length ≤ 134) (pb cb i : w64) :
    (memberAt pfx pb cb i).Name'.length ≤ 200 := by
  have := decStr_length_le i
  simp only [memberAt, List.length_append, List.length_cons, List.length_nil]
  omega

/-- `127.0.0.1:<p>` is `host:port` with a numeric port (fmt stage 1, 2026-11-24: the examples' Dir
files have their own copies, `loopback_plain`). -/
theorem loopback_plainPeerURL (p : w64) :
    types.plainPeerURL (go!"http://" ++ (go!"127.0.0.1:" ++ decStr p)) := by
  have hne := decStr_ne_nil p
  have hd := decStr_digits p
  unfold types.plainPeerURL types.plainHostPort
  refine ⟨List.isPrefixOf_iff_prefix.2 (List.prefix_append _ _), ?_⟩
  have hdrop : (go!"http://" ++ (go!"127.0.0.1:" ++ decStr p) : List w8).drop 7 =
      go!"127.0.0.1:" ++ decStr p := by simp
  rw [hdrop]
  have hidx : (go!"127.0.0.1:" ++ decStr p : List w8).idxOf (58 : w8) = 9 := by
    rw [List.idxOf_append]; simp only [show (58 : w8) ∈ (go!"127.0.0.1:" : List w8) from by decide, ite_true]; decide
  simp only [hidx]
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp; exact List.length_pos_iff.2 hne
  · rw [List.take_append_of_le_length (by decide)]; decide
  · intro c hc
    rw [List.drop_append_of_le_length (by decide)] at hc
    simp at hc
    exact hd c hc

/-- **`127.0.0.1:<p>` is within etcd's URL bounds** (`addrFits`, fmt stage 1, 2026-11-24). -/
theorem loopback_addrFits (p : w64) : addrFits (go!"127.0.0.1:" ++ decStr p) := by
  refine ⟨loopback_plainPeerURL p, ?_⟩
  have := decStr_length_le p
  simp only [List.length_append, etcdURLLenMax]
  have h1 : (go!"http://").length = 7 := rfl
  have h2 : (go!"127.0.0.1:").length = 10 := rfl
  omega

/-- **The members' addresses are within etcd's URL bounds** (`StartMembers`'s premise). -/
theorem membersOf_addrFits (pfx : GoString) (k : Nat) (pb cb : w64) :
    ∀ m ∈ membersOf pfx k pb cb, addrFits m.Peer' ∧ addrFits m.Client' := by
  intro m hm
  unfold membersOf at hm
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hm
  exact ⟨loopback_addrFits _, loopback_addrFits _⟩

/-- **The members' names are distinct.** -/
theorem membersOf_names_nodup (pfx : GoString) (k : Nat) (hk : k ≤ 2 ^ 64) (pb cb : w64) :
    ((membersOf pfx k pb cb).map (·.Name')).Nodup := by
  unfold membersOf
  rw [List.map_map]
  refine List.pairwise_map.2 (List.Pairwise.imp_of_mem ?_ List.nodup_range)
  intro i j hi hj hne h
  simp only [Function.comp, memberAt] at h
  have h' := decStr_inj (List.append_cancel_left h)
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  have := congrArg BitVec.toNat h'
  simp [W64] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact hne this

/-! ## A generated loopback address is a literal (probe D) -/

theorem bytesSplit_noSep (c : w8) (s : List w8) (h : c ∉ s) : bytesSplit c s = [s] := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    have hb : b ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have hbs : c ∉ bs := fun e => h (List.mem_cons_of_mem _ e)
    simp [bytesSplit, ih hbs, hb]

theorem not_mem_decStr (c : w8) (hc : c.toNat < 48 ∨ 57 < c.toNat) (p : w64) : c ∉ decStr p := by
  intro h; have := decStr_digits p c h; omega

theorem foldl_digits (ds : List Nat) (hd : ∀ d ∈ ds, d < 10) (a : Nat) :
    (ds.map digitChar).foldl (fun acc c => acc.bind fun n =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10 * n + (c.toNat - 48)) else none) (some a) =
      some (ds.foldl (fun a d => 10 * a + d) a) := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    have h := digitChar_digit d (hd d (by simp))
    have hc : 48 ≤ (digitChar d).toNat ∧ (digitChar d).toNat ≤ 57 := ⟨h.1, h.2.1⟩
    simp only [List.map_cons, List.foldl_cons, Option.bind_some, hc, and_self, ite_true, h.2.2]
    exact ih (fun x hx => hd x (by simp [hx])) _

theorem baseDigits_head_ne0 (n : Nat) (hn : 0 < n) :
    ∃ d ds, baseDigits 10 (by omega) n = d :: ds ∧ d ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · exact ⟨n, [], rfl, by omega⟩
    · obtain ⟨d, ds, h, hd⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨d, ds ++ [n % 10], by rw [h]; rfl, hd⟩

theorem decNumeral_decStr (p : w64) (hp : 0 < p.toNat) : decNumeral? (decStr p) = some p.toNat := by
  unfold decNumeral?
  obtain ⟨d, ds, hds, hd0⟩ := baseDigits_head_ne0 p.toNat hp
  rw [if_neg]
  · rw [decStr_eq, foldl_digits _ (baseDigits_lt 10 _ _) 0]
    have := digitsVal_baseDigits 10 (by omega) p.toNat
    unfold digitsVal at this
    rw [this]
  · rw [decStr_eq, hds]
    rintro (h | ⟨-, h⟩)
    · simp at h
    · have hlt := baseDigits_lt 10 (by omega) p.toNat d (by rw [hds]; simp)
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at h
      have := (digitChar_digit d hlt).2.2
      rw [h] at this; simp [W8] at this; omega

/-- **A generated loopback address is a literal** (`netAddrLit`, what `etcd_adequate_members`'
`hAsLit` needs): `127.0.0.1:<p>` for any port `1 ≤ p ≤ 65535`. -/
theorem netAddrLit_loopback (p : w64) (h1 : 1 ≤ p.toNat) (h2 : p.toNat ≤ 65535) :
    netAddrLit (go!"127.0.0.1:" ++ decStr p) = true := by
  have hcol : bytesSplit (W8 58) (decStr p) = [decStr p] :=
    bytesSplit_noSep _ _ (not_mem_decStr _ (by right; decide) p)
  have hsplit : bytesSplit (W8 58) (go!"127.0.0.1:" ++ decStr p) = [go!"127.0.0.1", decStr p] := by
    generalize decStr p = s at hcol ⊢
    have hcol' : bytesSplit (58#8) s = [s] := hcol
    simp [bytesSplit, hcol']
  unfold netAddrLit
  rw [hsplit]
  simp only
  rw [decNumeral_decStr p (by omega)]
  have hh : bytesSplit (W8 46) (go!"127.0.0.1" : List w8) = [go!"127", go!"0", go!"0", go!"1"] := by
    decide
  rw [hh]
  simp only
  have e127 : decNumeral? (go!"127" : List w8) = some 127 := by decide
  have e0 : decNumeral? (go!"0" : List w8) = some 0 := by decide
  have e1 : decNumeral? (go!"1" : List w8) = some 1 := by decide
  simp [e127, e0, e1]
  omega

/-- Two loopback addresses of distinct ports are distinct. -/
theorem loopback_ne (p q : w64) (h : p ≠ q) :
    (go!"127.0.0.1:" ++ decStr p : GoString) ≠ go!"127.0.0.1:" ++ decStr q :=
  fun e => h (decStr_inj (List.append_cancel_left e))

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A member's ghost names** (what `StartMembers`' spec pairs with each member): its id, the
cluster's server raft names with its own storage registry, its request names and its stand-in
apply environment (`memberBoot`'s and `StartMember`'s `id`, `γ`, `ρ`, `E₀`). -/
structure MemberG (GF : BundledGFunctors) where
  id : w64
  γ : SrvRaft
  ρ : ReqNames
  E : apply.AEnv GF

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A started member's thread token, lent out** (`StartMembers` passes the token from one
member's `memberUp` to the next member's start): `memberUp` is the token and the rest. -/
theorem memberUp_tok (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (m : lease.Mode) :
    memberUp (GF := GF) s ρ E₀ lg γn id m ⊢
      threadTok ∗ (threadTok -∗ memberUp s ρ E₀ lg γn id m) := by
  iintro Hup
  iunfold memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, H1, H2, H3, H4, Hgo, H6, H7, H8, H9, H10, H11, H12, H13⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwg, Htok⟩
  iframe Htok
  iintro Htok
  ihave Hgo : srvGoRes s $$ [Hwg Htok]
  · iunfold srvGoRes; iframe
  iunfold memberUp
  iexists E, cfg, γw
  iframe
  ipureintro; exact HEc

/-- **What `StartMembers` takes per member** (`StartMember`'s resources): `bootstrap`'s contract
at the member's name, URLs and id, its `memberBoot`, its network's HTTP side and its fresh bundle. -/
def memberPre (N : Nat) (token : GoString) (ms : List GMember) (ps : List w64)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode)
    (x : GMember × MemberG GF) (cmp : Bool := false) : IProp GF :=
  iprop(bootPremise N ps bootLog ctxs dir token x.1.Name' (urlsN ms x.1) x.2.id ∗
    memberBoot x.2.γ ctxs x.2.ρ x.2.E Φs x.2.id cmp lm ∗ netHttpOk γn x.2.id ∗
    memberFreshRes x.1.Name' ⟨some x.1.Peer', none⟩ γn)

end defs

end etcdstart
end EtcdGrove
end Perennial
