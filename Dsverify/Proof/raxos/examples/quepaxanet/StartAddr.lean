/-
The deployment's addresses (the kit's start, notes/dsv-quepaxa.md): the listed addresses
`kitAddrs` (every address a machine listens at or dials but the proxies' and the recorders',
`DistDeploy`'s), the wildcard listeners `kitLis` (the proxies' `proxyLis k` and the recorders'
`recLis r`, `0.0.0.0:7607..7611` and `0.0.0.0:7627..7631`), and the side conditions of
`robust_of_distProtoLisRB` (dsv-epaxos's `epaxosnet/Bridge.lean`): the listed addresses distinct
and valid, no two wildcards taking an address in common, no wildcard taking a listed address.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Kit
public import Dsverify.Proof.raxos.examples.quepaxanet.KitConf
public import GooseLang.Ext.Net.Decide

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Net

namespace raxos.examples.quepaxanet

open raxos raxos.pure

/-! ## The lists -/

/-- The listed addresses, in `netProtos`' order: node 0's, the unused ones, the clients' (the
replicas' connections back), the client machines' and the server machines' configuration
addresses, and remote's request addresses of the client machines (`clientAddrs`). -/
def kitAddrs : List GoString :=
  [orchAddr] ++ unusedAddrs ++ (List.range 6).map clientAddr ++ (List.range 6).map cconfAddr ++
    ([1, 2, 3, 4, 5] : List Nat).map confAddr ++ clientAddrs

/-- The wildcard listeners: the proxies', then the recorders'. -/
def kitLis : List GoString :=
  ([1, 2, 3, 4, 5] : List Nat).map proxyLis ++ ([1, 2, 3, 4, 5] : List Nat).map recLis

/-- `decStr` of a port `76xx`, for a literal port. -/
theorem decStr_76' (n : Nat) (h1 : 7600 ≤ n) (h2 : n < 7700) :
    decStr n = [BitVec.ofNat 8 55, BitVec.ofNat 8 54, BitVec.ofNat 8 (48 + (n - 7600) / 10),
      BitVec.ofNat 8 (48 + (n - 7600) % 10)] := by
  have h := decStr_76 (n - 7600) (by omega)
  rwa [show 7600 + (n - 7600) = n by omega] at h

theorem kitAddrs_lit : kitAddrs = [go!"127.0.0.1:7600",
    go!"127.0.0.1:7640", go!"127.0.0.1:7620", go!"127.0.0.1:7621", go!"127.0.0.1:7622",
    go!"127.0.0.1:7623", go!"127.0.0.1:7624", go!"127.0.0.1:7625", go!"127.0.0.1:7626",
    go!"127.0.0.1:7601", go!"127.0.0.1:7602", go!"127.0.0.1:7603", go!"127.0.0.1:7604",
    go!"127.0.0.1:7605", go!"127.0.0.1:7606",
    go!"127.0.0.1:7641", go!"127.0.0.1:7642", go!"127.0.0.1:7643", go!"127.0.0.1:7644",
    go!"127.0.0.1:7645", go!"127.0.0.1:7646",
    go!"127.0.0.1:7647", go!"127.0.0.1:7648", go!"127.0.0.1:7649", go!"127.0.0.1:7650",
    go!"127.0.0.1:7651",
    go!"127.0.0.1:7661", go!"127.0.0.1:7662", go!"127.0.0.1:7663", go!"127.0.0.1:7664",
    go!"127.0.0.1:7665", go!"127.0.0.1:7666"] := by
  simp only [kitAddrs, unusedAddrs, orchAddr, clientAddr, cconfAddr, confAddr, clientAddrs,
    portAddr, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, Nat.reduceAdd]
  simp (disch := decide) only [decStr_76', Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceAdd]

theorem kitLis_lit : kitLis = [go!"0.0.0.0:7607", go!"0.0.0.0:7608", go!"0.0.0.0:7609",
    go!"0.0.0.0:7610", go!"0.0.0.0:7611", go!"0.0.0.0:7627", go!"0.0.0.0:7628",
    go!"0.0.0.0:7629", go!"0.0.0.0:7630", go!"0.0.0.0:7631"] := by
  simp only [kitLis, proxyLis, recLis, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Nat.reduceAdd]
  simp (disch := decide) only [decStr_76', Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceAdd]

/-! ## The side conditions -/

theorem kitAddrs_nodup : kitAddrs.Nodup := by
  rw [kitAddrs_lit]; decide

theorem kitAddrs_ok : ∀ a ∈ kitAddrs, addrOk a = true := by
  rw [kitAddrs_lit]; decide

/-- A listener that takes its own address only through its port (a wildcard `0.0.0.0:p`) takes
exactly the addresses with port `p`. -/
theorem lisAccepts_port {la a : GoString} {p : GoString} (hw : wildPort la = some p)
    (hp : portOf la = some p) (h : lisAccepts la a) : portOf a = some p := by
  rcases h with rfl | ⟨q, hq, ha⟩
  · exact hp
  · rw [hw] at hq; cases hq; exact ha

/-- Listeners whose ports are distinct wildcards take no address in common. -/
theorem lis_pairwise : ∀ las : List GoString,
    (∀ la ∈ las, (wildPort la).isSome ∧ portOf la = wildPort la) → (las.map wildPort).Nodup →
    las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a)
  | [], _, _ => List.Pairwise.nil
  | la :: las, hw, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine List.Pairwise.cons (fun l2 hl2 a h1 h2 => ?_) (lis_pairwise las
      (fun l h => hw l (List.mem_cons_of_mem _ h)) hnd.2)
    obtain ⟨hs1, hp1⟩ := hw la List.mem_cons_self
    obtain ⟨hs2, hp2⟩ := hw l2 (List.mem_cons_of_mem _ hl2)
    obtain ⟨p1, e1⟩ := Option.isSome_iff_exists.1 hs1
    obtain ⟨p2, e2⟩ := Option.isSome_iff_exists.1 hs2
    have a1 := lisAccepts_port e1 (hp1.trans e1) h1
    have a2 := lisAccepts_port e2 (hp2.trans e2) h2
    rw [a1] at a2
    cases a2
    exact hnd.1 (List.mem_map.2 ⟨l2, hl2, e2.trans e1.symm⟩)

theorem kitLis_pairwise :
    kitLis.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a) :=
  lis_pairwise kitLis (by rw [kitLis_lit]; decide) (by rw [kitLis_lit]; decide)

theorem kitLis_disjB : ∀ a ∈ kitAddrs, ∀ la ∈ kitLis, lisAcceptsB la a = false := by
  rw [kitAddrs_lit, kitLis_lit]; decide

theorem kitLis_disj : ∀ a ∈ kitAddrs, ∀ la ∈ kitLis, ¬ lisAccepts la a := by
  intro a ha la hla h
  have h' := lisAcceptsB_iff.2 h
  rw [kitLis_disjB a ha la hla] at h'
  cases h'

end raxos.examples.quepaxanet
end Perennial
