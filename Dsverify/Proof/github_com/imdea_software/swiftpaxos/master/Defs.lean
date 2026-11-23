/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The master's internal predicates (the master group's; not frozen):

* `master.fld m f`: the address of field `f` of the master struct at `m`;
* `master.regOk N nodes addrs ports`: the registrations' pure facts: `nodes[i]` is
  `addrPort addrs[i] ports[i]`, distinct, among the first `N` replica addresses;
* `master.lists`: the registrations' resources: before the `N`-th registration, the fields
  `nodeList`, `addrList`, `portList` and their slices (with capacity `N`) owned, with the
  membership's writer token; from it on, all persistent, with the membership's fact `memIs`;
* `master.lockInv`: the invariant of `master.lock` (M1): the registrations, `leader`, `alive`,
  `latencies`'s contents, `finishInit` (true only once the registrations are complete);
* `master.isMaster m γc γm N`: the persistent facts every method uses: the read-only fields,
  the quiet logger, the plain configuration, the configuration's fact (`N` replicas), the mutex
  and the condition variable on it;
* `master.createdFull`: what `New` returns, in full (see `notes/hub-requests.md`, request 1:
  the frozen `master.created` lacks the mutex, the condition variable, `latencies` and the
  configuration).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs
public import Perennial.Proof.sync
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The registrations' pure facts. -/
def master.regOk (N : Nat) (nodes addrs : List GoString) (ports : List w64) : Prop :=
  addrs.length = nodes.length ∧ ports.length = nodes.length ∧ nodes.length ≤ N ∧
    nodes = List.zipWith sp.addrPort addrs ports ∧ nodes.Nodup ∧
    ∀ a ∈ nodes, a ∈ replicaAddrs.take N

/-- Every registered member is a configured replica node (R-E2: `sp.cfg`'s fact). -/
theorem master.regOk_nodeOf {N : Nat} {nodes addrs : List GoString} {ports : List w64}
    (h : master.regOk N nodes addrs ports) : ∀ r k, nodeOf nodes r = some k → k < N := by
  intro r k hk
  unfold nodeOf at hk
  cases hr : nodes[r]? with
  | none => rw [hr] at hk; simp at hk
  | some a =>
    rw [hr] at hk
    simp only [Option.bind_some] at hk
    have ha : a ∈ replicaAddrs.take N := h.2.2.2.2.2 a (List.mem_of_getElem? hr)
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
    rw [List.getElem_take] at hia
    have hi' : i < N := by simp only [List.length_take] at hi; omega
    obtain ⟨_, _, hk'⟩ := List.idxOf?_eq_some_iff.mp hk
    rcases Nat.lt_or_ge i k with hlt | hge
    · exact absurd hia (hk' i hlt)
    · omega

/-- An address of the configuration absent from the registrations: there is room. -/
theorem master.regOk_lt {N : Nat} {nodes addrs : List GoString} {ports : List w64} {a : GoString}
    (h : master.regOk N nodes addrs ports) (ha : a ∈ replicaAddrs.take N) (hn : a ∉ nodes) :
    nodes.length < N := by
  have hnd : (a :: nodes).Nodup := List.nodup_cons.mpr ⟨hn, h.2.2.2.2.1⟩
  have hsub : (a :: nodes) ⊆ replicaAddrs.take N := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact h.2.2.2.2.2 x hx
  have := hnd.length_le_of_subset hsub
  simp only [List.length_cons, List.length_take] at this
  omega

/-- A new registration keeps the facts. -/
theorem master.regOk_snoc {N : Nat} {nodes addrs : List GoString} {ports : List w64}
    {ip : GoString} {port : w64}
    (h : master.regOk N nodes addrs ports) (ha : sp.addrPort ip port ∈ replicaAddrs.take N)
    (hn : sp.addrPort ip port ∉ nodes) :
    master.regOk N (nodes ++ [sp.addrPort ip port]) (addrs ++ [ip]) (ports ++ [port]) := by
  have hlt := master.regOk_lt h ha hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by simp [h1], by simp [h2], by simp; omega, ?_, ?_, ?_⟩
  · rw [List.zipWith_append (by omega), h4]; rfl
  · exact List.nodup_append.mpr ⟨h5, by simp, by
      intro x hx y hy; simp at hy; subst hy; intro e; subst e; exact hn hx⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h6 x hx
    · simp at hx; subst hx; exact ha

theorem master.bounds_ext (len cap : w64) (h0 : 0 ≤ sint.Z len) (h : sint.Z len < sint.Z cap) :
    0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (len + W64 1) ∧ sint.Z (len + W64 1) ≤ sint.Z cap := by
  word

theorem master.bounds_last (len cap : w64) (h0 : 0 ≤ sint.Z len) (h : sint.Z len < sint.Z cap) :
    0 ≤ sint.Z len ∧ sint.Z len < sint.Z (len + W64 1 - W64 0) := by
  word

theorem master.set_last {A : Type} (l : List A) (y x : A) (n : Nat) (h : n = l.length) :
    (l ++ [y]).set n x = l ++ [x] := by
  subst h; simp

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions]

/-- Field `f` of the master at `m`. -/
abbrev master.fld (m : Loc) (f : GoString) : Loc := structFieldRef master.Master f m

/-- The registrations' resources (see the file header). -/
def master.lists (m : Loc) (γm : GName) (N : Nat) (nl al pl : GoSlice)
    (nodes addrs : List GoString) (ports : List w64) : IProp netDistGF :=
  if nodes.length = N then
    iprop(master.fld m go!"nodeList" ↦□ nl ∗ master.fld m go!"addrList" ↦□ al ∗
      master.fld m go!"portList" ↦□ pl ∗ nl ↦*□ nodes ∗ al ↦*□ addrs ∗ pl ↦*□ ports ∗
      memIs γm nodes)
  else
    iprop(master.fld m go!"nodeList" ↦ nl ∗ master.fld m go!"addrList" ↦ al ∗
      master.fld m go!"portList" ↦ pl ∗ nl ↦* nodes ∗ al ↦* addrs ∗ pl ↦* ports ∗
      ownSliceCap GoString nl (DFrac.own 1) ∗ ownSliceCap GoString al (DFrac.own 1) ∗
      ownSliceCap w64 pl (DFrac.own 1) ∗
      ⌜nl.cap = W64 N ∧ al.cap = W64 N ∧ pl.cap = W64 N⌝ ∗
      monoListAuthOwn (A := List GoString) γm 1 [])

theorem master.lists_full (m : Loc) (γm : GName) (N : Nat) (nl al pl : GoSlice)
    (nodes addrs : List GoString) (ports : List w64) (h : nodes.length = N) :
    ⊢ master.fld m go!"nodeList" ↦□ nl -∗ master.fld m go!"addrList" ↦□ al -∗
      master.fld m go!"portList" ↦□ pl -∗ nl ↦*□ nodes -∗ al ↦*□ addrs -∗ pl ↦*□ ports -∗
      memIs γm nodes -∗ master.lists m γm N nl al pl nodes addrs ports := by
  iintro #H1 #H2 #H3 #H4 #H5 #H6 #H7
  unfold master.lists
  rw [if_pos h]
  iframe H1 H2 H3 H4 H5 H6 H7

theorem master.lists_partial (m : Loc) (γm : GName) (N : Nat) (nl al pl : GoSlice)
    (nodes addrs : List GoString) (ports : List w64) (h : nodes.length ≠ N)
    (hc : nl.cap = W64 N ∧ al.cap = W64 N ∧ pl.cap = W64 N) :
    ⊢ master.fld m go!"nodeList" ↦ nl -∗ master.fld m go!"addrList" ↦ al -∗
      master.fld m go!"portList" ↦ pl -∗ nl ↦* nodes -∗ al ↦* addrs -∗ pl ↦* ports -∗
      ownSliceCap GoString nl (DFrac.own 1) -∗ ownSliceCap GoString al (DFrac.own 1) -∗
      ownSliceCap w64 pl (DFrac.own 1) -∗ monoListAuthOwn (A := List GoString) γm 1 [] -∗
      master.lists m γm N nl al pl nodes addrs ports := by
  iintro H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
  unfold master.lists
  rw [if_neg h]
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
  ipureintro; exact hc

/-- Once the membership is written (`memIs`), the lock invariant's registrations are in their
full state (unfolds `memIs`, Spec/swiftnet/Base.lean: a missing law `memIs_written`). -/
theorem master.lists_full_of (m : Loc) (γm : GName) (N : Nat) (nl al pl : GoSlice)
    (nodes' nodes addrs : List GoString) (ports : List w64) :
    memIs γm nodes' ∗ master.lists m γm N nl al pl nodes addrs ports ⊢
      master.lists m γm N nl al pl nodes addrs ports ∗ ⌜nodes.length = N⌝ := by
  iintro ⟨#H, Hl⟩
  by_cases h : nodes.length = N
  · iframe Hl; ipureintro; exact h
  unfold master.lists
  · rw [if_neg h]
    icases Hl with ⟨-, -, -, -, -, -, -, -, -, -, Ha⟩
    unfold memIs
    icases H with ⟨#Hlb, -⟩
    ihave %Hv := mono_list_auth_lb_valid γm 1 [] [nodes'] $$ Ha Hlb
    exfalso
    simp at Hv

/-- The invariant of `master.lock` (see the file header). -/
def master.lockInv (m : Loc) (γm : GName) (N : Nat) (leaderS aliveS latS : GoSlice) :
    IProp netDistGF :=
  iprop(∃ (nl al pl : GoSlice) (nodes addrs : List GoString) (ports : List w64)
      (leaders alive : List Bool) (lats : List w64) (fi : Bool),
    "Hlists" ∷ master.lists m γm N nl al pl nodes addrs ports ∗
    "Hleaders" ∷ leaderS ↦* leaders ∗ "Halives" ∷ aliveS ↦* alive ∗ "Hlats" ∷ latS ↦* lats ∗
    "Hfi" ∷ master.fld m go!"finishInit" ↦ fi ∗
    "%Hwf" ∷ ⌜master.regOk N nodes addrs ports ∧ leaders.length = N ∧ alive.length = N ∧
      lats.length = N ∧ (fi = true → nodes.length = N)⌝)

/-- The master's persistent facts (see the file header). -/
def master.isMaster (m : Loc) (γc γm : GName) (N : Nat) : IProp netDistGF :=
  iprop(∃ (lg lk cd cfgp : Loc) (nodesS leaderS aliveS latS : GoSlice) (c : Conf) (fr : Bool),
    "#Hlg" ∷ master.fld m go!"Logger" ↦□ lg ∗ "#Hquiet" ∷ dlog.quiet lg ∗
    "#HN" ∷ master.fld m go!"N" ↦□ W64 N ∗
    "#Hlock" ∷ master.fld m go!"lock" ↦□ lk ∗ "#Hcond" ∷ master.fld m go!"initCond" ↦□ cd ∗
    "#Hnodes" ∷ master.fld m go!"nodes" ↦□ nodesS ∗
    "#Hleader" ∷ master.fld m go!"leader" ↦□ leaderS ∗
    "#Halive" ∷ master.fld m go!"alive" ↦□ aliveS ∗
    "#Hlat" ∷ master.fld m go!"latencies" ↦□ latS ∗
    "#Hcfg" ∷ master.fld m go!"config" ↦□ cfgp ∗ "#Hplain" ∷ config.plain cfgp fr ∗
    "#Hconf" ∷ confIs γc c ∗
    "%HN" ∷ ⌜c.n = N ∧ N ≤ 5⌝ ∗
    "#Hmu" ∷ sync.isMutex lk (master.lockInv m γm N leaderS aliveS latS) ∗
    "#HisCond" ∷ sync.isCond cd (interface.mk (go.GoType.PointerType sync.Mutex.ty) #lk) ∗
    "#HpkgM" ∷ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master)

/-- What `New` returns (`master.created`'s body, change log C7). -/
abbrev master.createdFull (m : Loc) (γc γm : GName) (N : Nat) (port : w64) : IProp netDistGF :=
  master.createdBody m γc γm N port

theorem master.createdFull_created (m : Loc) (γc γm : GName) (N : Nat) (port : w64) :
    master.createdFull m γc γm N port ⊢ master.created m γc γm N port := by
  rw [master.created_eq]

theorem master.created_full (m : Loc) (γc γm : GName) (N : Nat) (port : w64) :
    master.created m γc γm N port ⊢ master.createdFull m γc γm N port := by
  rw [master.created_eq]

theorem master.isMaster_pkg (m : Loc) (γc γm : GName) (N : Nat) :
    master.isMaster m γc γm N ⊢
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master := by
  iintro Hm
  unfold master.isMaster
  iNamed Hm
  iexact HpkgM

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
instance master.isMaster_persistent (m : Loc) (γc γm : GName) (N : Nat) :
    Persistent (master.isMaster m γc γm N) := by
  unfold master.isMaster named; infer_instance

/-- `s[0 : len(s)+1]` within the capacity: one more element (of some value). -/
theorem master.slice_extend {V : Type} [ZeroVal V] [TypedPointsto (GF := netDistGF) V]
    (s : GoSlice) (vs : List V) (h : sint.Z s.len < sint.Z s.cap) :
    (s ↦* vs ∗ ownSliceCap V s (DFrac.own 1) : IProp netDistGF) ⊢
      ∃ y : V, slice.slice s V (W64 0) (s.len + W64 1) ↦* (vs ++ [y]) ∗
        ownSliceCap V (slice.slice s V (W64 0) (s.len + W64 1)) (DFrac.own 1) := by
  iintro ⟨Hs, Hcap⟩
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  icases ownSlice_slice_into_capacity (W64 0) (s.len + W64 1) s vs $$ [Hs Hcap]
    with ⟨%vs', -, Hs', Hcap'⟩
  · iframe Hs Hcap; ipureintro; refine ⟨by word, by word, by word, by word⟩
  ihave %Hlen' := ownSlice_len _ _ _ $$ Hs'
  have h0 : sint.nat (W64 0) = 0 := rfl
  rw [h0, List.drop_zero]
  rw [h0, List.drop_zero] at Hlen'
  simp only [slice.slice, List.length_append] at Hlen'
  obtain ⟨y, hy⟩ : ∃ y, vs' = [y] := by
    match vs', Hlen' with
    | [y], _ => exact ⟨y, rfl⟩
    | [], h => exfalso; simp at h; word
    | _ :: _ :: _, h => exfalso; simp at h; word
  subst hy
  iexists y
  iframe Hs' Hcap'

/-- The membership's write, if the registrations are complete. -/
theorem master.write_if (γm : GName) (l : List GoString) (b : Prop) [Decidable b]
    (h : l.Nodup ∧ ∀ a ∈ l, a ∈ replicaAddrs) :
    monoListAuthOwn (A := List GoString) γm 1 [] ⊢
      |==> (if b then memIs γm l else monoListAuthOwn (A := List GoString) γm 1 []) := by
  iintro Ha
  by_cases hb : b
  · rw [if_pos hb]
    -- (`memIs_write`'s statement reads `(|==> memIs γm l) ∗ …`: notes/hub-requests.md, 2)
    icases memIs_write γm l $$ [Ha] with ⟨Hm, -⟩
    · iframe Ha; ipureintro; exact h
    imod Hm with #Hm
    imodintro; iexact Hm
  · rw [if_neg hb]
    imodintro; iexact Ha

/-- A read view of the registrations' `nodeList` (both states), and the way back. -/
theorem master.lists_read (m : Loc) (γm : GName) (N : Nat) (nl al pl : GoSlice)
    (nodes addrs : List GoString) (ports : List w64) :
    master.lists m γm N nl al pl nodes addrs ports ⊢
      ∃ dq : DFrac, master.fld m go!"nodeList" ↦{dq} nl ∗ nl ↦*{dq} nodes ∗
        (master.fld m go!"nodeList" ↦{dq} nl -∗ nl ↦*{dq} nodes -∗
          master.lists m γm N nl al pl nodes addrs ports) := by
  unfold master.lists
  by_cases h : nodes.length = N
  · simp only [h, ↓reduceIte]
    iintro ⟨#H1, #H2, #H3, #H4, #H5, #H6, #H7⟩
    iexists DFrac.discard
    isplitr
    · iexact H1
    isplitr
    · iexact H4
    iintro - -
    iframe H1 H2 H3 H4 H5 H6 H7
  · simp only [h, ↓reduceIte]
    iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %H10, H11⟩
    iexists DFrac.own 1
    iframe H1 H4
    iintro H1 H4
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H11
    ipureintro; exact H10

end defs

section logger
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [dlog.Assumptions]

/-- The promoted `m.Printf(...)` (the embedded quiet logger's). -/
theorem master.wp_Printf (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (m lg : Loc) (f : GoString) (sl : GoSlice) :
    {{ master.fld m go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (App (Val #(methods (go.GoType.PointerType master.Master.ty) go!"Printf" #m)) (Val #f))
        (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Printf $$ [$Hq]
  wp_end

/-- The promoted `m.Fatal(...)` (the embedded quiet logger's: it returns). -/
theorem master.wp_Fatal (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (m lg : Loc) (sl : GoSlice) :
    {{ master.fld m go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (Val #(methods (go.GoType.PointerType master.Master.ty) go!"Fatal" #m)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Fatal $$ [$Hq]
  wp_end

end logger

end Perennial.github_com.imdea_software.swiftpaxos
