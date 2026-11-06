/-
`goToFirstElementOnTheStack` of a writer's cursor (U6aa, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"): the pure facts of its loop over a stack prefix (`sPrefix`) with the
writer's registry (`nlX`): what the top reference is (a registered node, the inline root page, a
view page), when it is a leaf the prefix is a path (`sPathR`), and pushing the first child that
`pageNode` returns keeps a prefix whose new leaf page, if any, holds its bounds' entries.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WStkTop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WGoFirst

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge

section pure
variable [GooseExts]

/-- The writer's node-location registry as a function. -/
def nlX (X : WX) : Loc → Option (Loc × Nat) := fun l => X.nloc !! l

theorem sPrefix_congr (nl nl2 : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (els : List elemRef) (pids : List Nat)
    (h : ∀ e ∈ els, e.node' ≠ null → nl e.node' = nl2 e.node')
    (hp : sPrefix nl v b rt els pids) : sPrefix nl2 v b rt els pids := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨h1, h2, h3, fun j e pid he hpj => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h4 j e pid he hpj
  exact ⟨fun hn => by rw [← h e (List.mem_of_getElem? he) hn]; exact a1 hn, a2, a3, a4⟩

theorem sPathR_congr (nl nl2 : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (els : List elemRef) (pids : List Nat)
    (h : ∀ e ∈ els, e.node' ≠ null → nl e.node' = nl2 e.node')
    (hp : sPathR nl v b rt els pids) : sPathR nl2 v b rt els pids := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨h1, h2, h3, fun j e pid he hpj => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h4 j e pid he hpj
  exact ⟨fun hn => by rw [← h e (List.mem_of_getElem? he) hn]; exact a1 hn, a2, a3, a4⟩

theorem getLast_idx {α : Type} (l : List α) (x : α) (h : l.getLast? = some x) :
    l[l.length - 1]? = some x := by
  rw [← List.getLast?_eq_getElem?]; exact h

/-- A prefix whose top is a leaf position is a path. -/
theorem sPrefix_sPathR (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (els : List elemRef) (pids : List Nat) (hp : sPrefix nl v b rt els pids)
    (hl : ∀ e pid, els.getLast? = some e → pids.getLast? = some pid →
      pid = 0 ∨ ∃ pg, v.pages !! pid = some pg ∧ pageFlags pg = leafPageFlag) :
    sPathR nl v b rt els pids := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨h1, h2, h3, fun j e pid he hpj => ?_⟩
  obtain ⟨a1, a2, a3, -⟩ := h4 j e pid he hpj
  refine ⟨a1, a2, a3, fun hj => ?_⟩
  have hjl : j = els.length - 1 := by omega
  subst hjl
  refine hl e pid ?_ ?_
  · rw [List.getLast?_eq_getElem?]; exact he
  · rw [List.getLast?_eq_getElem?, h2]; exact hpj

/-- The opened bucket's record. -/
theorem wCurCtx_B (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (hc : wCurCtx X n bl rt) :
    ∃ B, X.t.bs !! bl = some B := by
  obtain ⟨hok, hb, -⟩ := hc
  unfold bktLoc at hb
  cases hR : X.t.bs !! X.rl with
  | none => rw [hR] at hb; cases hb
  | some R =>
    rw [hR] at hb
    have := (hok.1.2.2.2.2.2 X.rl R hR).2 n bl hb
    exact Option.isSome_iff_exists.1 this

/-- A prefix's positions: the root, or view pages. -/
theorem sPrefix_pids (nl : Loc → Option (Loc × Nat)) (v : View) (hv : viewWF v) (b : Loc)
    (rt : Nat) (els : List elemRef) (pids : List Nat) (hp : sPrefix nl v b rt els pids) :
    ∀ j p, pids[j]? = some p → (j = 0 ∧ p = rt) ∨ ((∃ pg, v.pages !! p = some pg) ∧ p < 2 ^ 64) := by
  obtain ⟨-, hlen, hhd, hall⟩ := hp
  intro j p hj
  cases j with
  | zero =>
    left; refine ⟨rfl, ?_⟩
    rw [List.head?_eq_getElem?] at hhd; rw [hhd] at hj; cases hj; rfl
  | succ j =>
    right
    have hjl : j + 1 < els.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨e0, he0⟩ : ∃ e0, els[j]? = some e0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨p0, hp0⟩ : ∃ p0, pids[j]? = some p0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; omega)⟩
    obtain ⟨pg, hpg, hf, hi, hnx⟩ := (hall j e0 p0 he0 hp0).2.2.1 hjl
    rw [hnx] at hj; cases hj
    exact ⟨viewWF_child _ hv _ _ hpg hf _ hi, branchPgid_lt _ _⟩

/-- A writer prefix's positions are below `2 ^ 64`. -/
theorem sPrefix_lt (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (hc : wCurCtx X n bl rt)
    (nl : Loc → Option (Loc × Nat)) (els : List elemRef) (pids : List Nat)
    (hp : sPrefix nl X.v bl rt els pids) (j p : Nat) (hj : pids[j]? = some p) : p < 2 ^ 64 := by
  rcases sPrefix_pids nl X.v hc.1.2.2.2.2.2.2.2 bl rt els pids hp j p hj with ⟨-, rfl⟩ | ⟨-, h⟩
  · rw [← hc.2.2.2.1]; exact BitVec.isLt _
  · exact h

/-- An inline bucket's prefix is its root alone. -/
theorem sPrefix_root0 (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (nl : Loc → Option (Loc × Nat))
    (els : List elemRef) (pids : List Nat) (hp : sPrefix nl X.v bl rt els pids)
    (h0 : B.ib.root' = W64 0) : els.length = 1 ∧ pids = [0] := by
  have hv : viewWF X.v := hc.1.2.2.2.2.2.2.2
  have hrt : rt = 0 := by rw [← hc.2.2.2.1]; simp [WX.rootPid, hB, h0]
  obtain ⟨hne, hlen, hhd, hall⟩ := hp
  have hhd0 : pids[0]? = some 0 := by rw [← List.head?_eq_getElem?, hhd, hrt]
  have hpos' : 0 < els.length := List.length_pos_iff.2 hne
  have hlen1 : els.length = 1 := by
    rcases Nat.lt_or_ge 1 els.length with h1 | h1
    · exfalso
      obtain ⟨e0, he0⟩ : ∃ e0, els[0]? = some e0 := ⟨_, List.getElem?_eq_getElem hpos'⟩
      obtain ⟨pg, hpg, -⟩ := (hall 0 e0 0 he0 hhd0).2.2.1 (by omega)
      have := (Read.viewWF_page _ hv _ _ hpg).1; omega
    · omega
  refine ⟨hlen1, ?_⟩
  rw [hlen1] at hlen
  match pids, hlen, hhd0 with
  | [x], _, h => simp at h; rw [h]

/-- A prefix position `0` is an inline bucket's root. -/
theorem sPrefix_pid0 (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (nl : Loc → Option (Loc × Nat))
    (els : List elemRef) (pids : List Nat) (hp : sPrefix nl X.v bl rt els pids) (j : Nat)
    (hj : pids[j]? = some 0) : B.ib.root' = W64 0 := by
  rcases sPrefix_pids nl X.v hc.1.2.2.2.2.2.2.2 bl rt els pids hp j 0 hj with ⟨-, h⟩ | ⟨⟨pg, hpg⟩, -⟩
  · have hr := hc.2.2.2.1
    simp only [WX.rootPid, hB, Option.map_some, Option.getD_some] at hr
    apply BitVec.eq_of_toNat_eq; rw [hr, ← h]; rfl
  · have := (Read.viewWF_page _ hc.1.2.2.2.2.2.2.2 _ _ hpg).1; omega

theorem flag_ne {pg : List w8} (h1 : pageFlags pg = branchPageFlag) (h2 : pageFlags pg = leafPageFlag) :
    False := by
  rw [h1] at h2; exact absurd h2 (by decide)

/-- **A node at the top of a writer prefix**: a live node of the bucket; a leaf makes the prefix a
path; a branch is at a branch page of the view, its entries the page's children. -/
theorem top_node (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (els : List elemRef) (pids : List Nat)
    (hp : sPrefix (nlX X) X.v bl rt els pids) (e : elemRef) (p : Nat)
    (he : els.getLast? = some e) (hpl : pids.getLast? = some p) (hn : e.node' ≠ null) :
    ∃ rn, B.ns !! e.node' = some rn ∧ e.node' ∈ X.live ∧
      (rn.nv.isLeaf' = true → sPathR (nlX X) X.v bl rt els pids) ∧
      (rn.nv.isLeaf' = false → B.ib.root' ≠ W64 0 ∧ ∃ pg, X.v.pages !! p = some pg ∧
        pageFlags pg = branchPageFlag ∧ e.index'.toNat < pageCount pg ∧
        rn.ws.length = pageCount pg ∧
        ∀ i w, rn.ws[i]? = some w → w.pgid = W64 (branchPgid pg i : Int)) := by
  have hok := hc.1
  have hcl := wOK_bktClean X hok bl B hB
  have hlen : pids.length = els.length := hp.2.1
  have he' := getLast_idx els e he
  have hpos : 0 < els.length := List.length_pos_iff.2 hp.1
  have hpj : pids[els.length - 1]? = some p := by rw [← hlen]; exact getLast_idx pids p hpl
  obtain ⟨h1, -, -, h4⟩ := hp.2.2.2 _ e p he' hpj
  have hx : X.nloc !! e.node' = some (bl, p) := h1 hn
  have hres := nodeRef_current X n bl rt B hc hB _ p hn hx
  have hP : (W64 (p : Int)).toNat = p := W64_toNat_lt p (sPrefix_lt X n bl rt hc _ els pids hp _ p hpj)
  have hnm : B.nm !! W64 (p : Int) = some e.node' := by
    by_cases hin : B.ib.root' = W64 0
    · obtain ⟨-, hP0⟩ := sPrefix_root0 X n bl rt B hc hB _ els pids hp hin
      rw [hP0] at hpl; simp at hpl; subst hpl
      unfold resolve at hres; rw [if_pos hin] at hres
      by_cases hrn : B.bv.rootNode' = null
      · rw [if_pos hrn] at hres; cases hres
      · rw [if_neg hrn] at hres
        rw [← Option.some.inj hres]
        have := hcl.2.2.2.1 hrn; rw [hin] at this; exact this
    · rw [← resolve_tree B _ hin]; exact hres
  obtain ⟨-, rn, hrn, hpgid⟩ := hcl.2.2.2.2.1 _ _ hnm
  have hnp := hok.2.2.1 bl B hB _ rn hrn
  refine ⟨rn, hrn, wOK_nsLive X hok bl B _ rn hB hrn, fun hleaf => ?_, fun hleaf => ?_⟩
  · refine sPrefix_sPathR _ _ _ _ els pids hp (fun e0 p0 h1 h2 => ?_)
    rw [hpl] at h2; cases h2
    by_cases hin : B.ib.root' = W64 0
    · left
      obtain ⟨-, hP0⟩ := sPrefix_root0 X n bl rt B hc hB _ els pids hp hin
      rw [hP0] at hpl; simpa using hpl.symm
    · obtain ⟨pg, hpg, hf⟩ := (hnp.1 hleaf).2 hin
      rw [hpgid, hP] at hpg
      exact Or.inr ⟨pg, hpg, hf⟩
  · have hin : B.ib.root' ≠ W64 0 := by
      intro h0
      have := hcl.2.2.2.2.2.2.1 h0 _ rn hrn
      rw [hleaf] at this; cases this
    obtain ⟨-, pg, hpg, hf, hwl, hwp⟩ := hnp.2 hleaf
    rw [hpgid, hP] at hpg
    refine ⟨hin, pg, hpg, hf, ?_, hwl, hwp⟩
    rcases h4 (by omega) with h | ⟨pg', hpg', hk⟩
    · subst h; exact absurd (sPrefix_pid0 X n bl rt B hc hB _ els pids hp _ hpj) hin
    · rw [hpg] at hpg'; cases hpg'
      rcases hk with h | ⟨-, h⟩
      · exact (flag_ne hf h).elim
      · exact h

/-- **A page at the top of a writer prefix**: the inline root (the stack its root alone, a path),
or a view page at its location, a leaf (the prefix a path) or a branch on an entry. -/
theorem top_page (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (els : List elemRef) (pids : List Nat)
    (hp : sPrefix (nlX X) X.v bl rt els pids) (e : elemRef) (p : Nat)
    (he : els.getLast? = some e) (hpl : pids.getLast? = some p) (hn : e.node' = null) :
    (p = 0 ∧ els = [e] ∧ rt = 0 ∧ e.page' ≠ null ∧ sPathR (nlX X) X.v bl rt els pids) ∨
    (p ≠ 0 ∧ B.ib.root' ≠ W64 0 ∧ e.page' = pageLoc X.v p ∧ ∃ pg, X.v.pages !! p = some pg ∧
      ((pageFlags pg = leafPageFlag ∧ sPathR (nlX X) X.v bl rt els pids) ∨
       (pageFlags pg = branchPageFlag ∧ e.index'.toNat < pageCount pg))) := by
  have hlen : pids.length = els.length := hp.2.1
  have he' := getLast_idx els e he
  have hpos : 0 < els.length := List.length_pos_iff.2 hp.1
  have hpj : pids[els.length - 1]? = some p := by rw [← hlen]; exact getLast_idx pids p hpl
  obtain ⟨-, h2, -, h4⟩ := hp.2.2.2 _ e p he' hpj
  obtain ⟨hpnn, hpl'⟩ := h2 hn
  by_cases hp0 : p = 0
  · subst hp0
    have hin := sPrefix_pid0 X n bl rt B hc hB _ els pids hp _ hpj
    obtain ⟨hl1, hP0⟩ := sPrefix_root0 X n bl rt B hc hB _ els pids hp hin
    have hrt : rt = 0 := by
      have := hp.2.2.1; rw [hP0] at this; simpa using this.symm
    have hels : els = [e] := by
      match els, hl1, he with
      | [x], _, h => simp at h; rw [h]
    refine Or.inl ⟨rfl, hels, hrt, hpnn, sPrefix_sPathR _ _ _ _ els pids hp (fun e0 p0 h1 h2 => ?_)⟩
    rw [hpl] at h2; cases h2; exact Or.inl rfl
  · have hin : B.ib.root' ≠ W64 0 := by
      intro h0
      obtain ⟨-, hP0⟩ := sPrefix_root0 X n bl rt B hc hB _ els pids hp h0
      rw [hP0] at hpl; simp at hpl; exact hp0 hpl.symm
    rcases h4 (by omega) with h | ⟨pg, hpg, hk⟩
    · exact absurd h hp0
    refine Or.inr ⟨hp0, hin, hpl' hp0, pg, hpg, ?_⟩
    rcases hk with h | h
    · refine Or.inl ⟨h, sPrefix_sPathR _ _ _ _ els pids hp (fun e0 p0 h1 h2 => ?_)⟩
      rw [hpl] at h2; cases h2; exact Or.inr ⟨pg, hpg, h⟩
    · exact Or.inr h

/-- A view branch page is well-formed (`Write.viewWF_branch`'s). -/
theorem viewWF_branchWF (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = branchPageFlag) :
    ∃ hwm, branchWF pg pg.length hwm := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf _ _ => rw [hb] at hf; exact absurd hf (by decide)
    | branch _ _ _ hbw _ => exact ⟨_, hbw⟩

/-- **`pageNode`'s premises at a view page position** of a bucket with a root page. -/
theorem pn_pre (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (hmax : ∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF)
    (h0 : B.ib.root' ≠ W64 0) (c : Nat) (pgc : List w8) (hpgc : X.v.pages !! c = some pgc)
    (hcl : c < 2 ^ 64) :
    bl ∈ X.liveB ∧ (B.ib.root' = W64 0 → W64 (c : Int) = W64 0) ∧
    (∀ c l, B.nm !! c = some l → l ≠ null) ∧
    (resolve B (W64 (c : Int)) = none → ∃ pa pg, wpageAt X.v B (W64 (c : Int)) = some (pa, pg) ∧
      (B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) ∧
      (B.ib.root' ≠ W64 0 → X.t.pm !! W64 (c : Int) = none ∧ 16 ≤ pg.length ∧
        pageId pg = (W64 (c : Int)).toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        (W64 (c : Int)).toNat * 4096 < 0xFFFFFFFFFFFF)) := by
  have hok := hc.1
  have hcl' := wOK_bktClean X hok bl B hB
  have hC : (W64 (c : Int)).toNat = c := W64_toNat_lt c hcl
  refine ⟨hok.2.2.2.2.2.1.2.2.1 bl B hB, fun h => absurd h h0,
    fun c l h => (hcl'.2.2.2.2.1 c l h).1, fun _ => ?_⟩
  obtain ⟨h2, hid, h4096, hfl⟩ := Read.viewWF_page _ hok.2.2.2.2.2.2.2 _ _ hpgc
  refine ⟨pageLoc X.v c, pgc, ?_, fun h => absurd h h0, fun _ => ⟨?_, by omega, by rw [hC]; exact hid, hfl,
    by rw [hC]; exact hmax _ _ hpgc⟩⟩
  · unfold wpageAt; rw [if_neg h0, hC, hpgc]; rfl
  · rw [hok.1.2.1.1]; rfl

/-- **Pushing the first child**: from a branch top at view page `pg` on an entry, the reference
`pageNode` returns for its child keeps a prefix, whose leaf page, once a path, holds its bounds'
entries. -/
theorem push (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hp : sPrefix (nlX X) X.v bl rt els pids) (e : elemRef) (p : Nat)
    (he : els.getLast? = some e) (hpl : pids.getLast? = some p) (pg : List w8)
    (hpg : X.v.pages !! p = some pg) (hf : pageFlags pg = branchPageFlag)
    (hi : e.index'.toNat < pageCount pg) (h0 : B.ib.root' ≠ W64 0) (e' : elemRef)
    (hi' : e'.index' = W64 0)
    (hpn : match resolve B (W64 (branchPgid pg e.index'.toNat : Int)) with
      | some l => e'.page' = null ∧ e'.node' = l
      | none => e'.node' = null ∧ ∃ pg2, wpageAt X.v B (W64 (branchPgid pg e.index'.toNat : Int)) =
          some (e'.page', pg2)) :
    sPrefix (nlX X) X.v bl rt (els ++ [e']) (pids ++ [branchPgid pg e.index'.toNat]) ∧
    (sPathR (nlX X) X.v bl rt (els ++ [e']) (pids ++ [branchPgid pg e.index'.toNat]) →
      sLeafOK X.v ipg (wEs X n) (pids ++ [branchPgid pg e.index'.toNat]) (els ++ [e'])) := by
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := wOK_bktClean X hok bl B hB
  have hlen : pids.length = els.length := hp.2.1
  have hpos : 0 < els.length := List.length_pos_iff.2 hp.1
  generalize hcdef : branchPgid pg e.index'.toNat = c at hpn ⊢
  obtain ⟨pgc, hpgc⟩ : ∃ pgc, X.v.pages !! c = some pgc := by
    rw [← hcdef]; exact viewWF_child _ hv _ _ hpg hf _ hi
  have hc2 : 2 ≤ c := (Read.viewWF_page _ hv _ _ hpgc).1
  have hclt : c < 2 ^ 64 := by rw [← hcdef]; exact branchPgid_lt _ _
  have hC : (W64 (c : Int)).toNat = c := W64_toNat_lt c hclt
  -- the new reference's position facts
  obtain ⟨lf, ws, hra, hL⟩ : ∃ lf ws, refAt X bl (W64 (c : Int)) e' ∧
      ltree X bl (W64 (c : Int)) = some (lf, ws) := by
    cases hr : resolve B (W64 (c : Int)) with
    | some l =>
      rw [hr] at hpn
      obtain ⟨-, r, hr', -⟩ := hcl.2.2.2.2.1 _ l (by rw [← resolve_tree B _ h0]; exact hr)
      exact ⟨r.nv.isLeaf', r.ws, refAt_node X bl B _ l e' hB hr hpn.2, ltree_node X bl B _ l r hB hr hr'⟩
    | none =>
      rw [hr] at hpn
      obtain ⟨hnn, pg', hw⟩ := hpn
      have h1 := refAt_page X bl B (W64 (c : Int)) pg' e' hB hr hnn hw
      have h2 := ltree_page X bl B (W64 (c : Int)) _ pg' hB hr hw
      exact ⟨_, _, h1, h2⟩
  obtain ⟨P1, P2, P3, P4, P5⟩ := pos_facts X bl B hok hB hc.2.2.1 hbase _ e' lf ws hra hL
    (fun h => absurd h h0)
  rw [hC] at P1 P2 P3 P4 P5
  have hget : ∀ j e0 p0, (els ++ [e'])[j]? = some e0 → (pids ++ [c])[j]? = some p0 →
      (j < els.length ∧ els[j]? = some e0 ∧ pids[j]? = some p0) ∨
      (j = els.length ∧ e0 = e' ∧ p0 = c) := by
    intro j e0 p0 h1 h2
    by_cases hj : j < els.length
    · left
      rw [List.getElem?_append_left hj] at h1
      rw [List.getElem?_append_left (by omega)] at h2
      exact ⟨hj, h1, h2⟩
    · right
      rw [List.getElem?_append_right (by omega)] at h1
      rw [List.getElem?_append_right (by omega)] at h2
      have hj' : j - els.length = 0 := by
        rcases Nat.eq_zero_or_pos (j - els.length) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by simp; omega)] at h1; cases h1
      rw [hj'] at h1
      rw [hlen, hj'] at h2
      simp at h1 h2
      exact ⟨by omega, h1.symm, h2.symm⟩
  have hlast : (els ++ [e']).getLast? = some e' := by simp
  have hplast : (pids ++ [c]).getLast? = some c := by simp
  refine ⟨⟨by simp, by simp [hlen], ?_, fun j e0 p0 h1 h2 => ?_⟩, fun hpath => ?_⟩
  · cases pids with
    | nil => simp at hlen; omega
    | cons a t => simpa using hp.2.2.1
  · rcases hget j e0 p0 h1 h2 with ⟨hj, h1', h2'⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨a1, a2, a3, -⟩ := hp.2.2.2 j e0 p0 h1' h2'
      refine ⟨a1, a2, fun hj1 => ?_, fun hj1 => by simp at hj1; omega⟩
      by_cases hj2 : j + 1 < els.length
      · obtain ⟨pg', h1, h2, h3, h4⟩ := a3 hj2
        exact ⟨pg', h1, h2, h3, by rw [List.getElem?_append_left (by omega)]; exact h4⟩
      · have hjl : j = els.length - 1 := by omega
        subst hjl
        rw [getLast_idx els e he] at h1'; cases h1'
        rw [← hlen, getLast_idx pids p hpl] at h2'; cases h2'
        refine ⟨pg, hpg, hf, hi, ?_⟩
        rw [show els.length - 1 + 1 = pids.length by omega]
        simp [← hcdef]
    · refine ⟨P1, P2, fun hj1 => by simp at hj1, fun _ => Or.inr ?_⟩
      cases lf with
      | false =>
        obtain ⟨pg', hpg', hb', -⟩ := P3 rfl
        obtain ⟨_, hbw⟩ := viewWF_branchWF _ hv _ _ hpg' hb'
        refine ⟨pg', hpg', Or.inr ⟨hb', ?_⟩⟩
        rw [hi']; exact hbw.1
      | true =>
        rcases P4 rfl with h | ⟨pg', hpg', hl'⟩
        · omega
        · exact ⟨pg', hpg', Or.inl hl'⟩
  · intro e0 p0 h1 h2 hnull
    rw [hlast] at h1; cases h1
    rw [hplast] at h2; cases h2
    obtain ⟨ws0, hL0, hents, -, hplain, -⟩ :=
      wStk_top X n bl rt B hc hB hbase (nlX X) _ _ hpath (fun _ _ _ => rfl) e' c hlast hplast
    rw [hL] at hL0
    simp only [Option.some.injEq, Prod.mk.injEq] at hL0
    obtain ⟨-, rfl⟩ := hL0
    obtain ⟨pg', hlp, hws, -⟩ := P5 hnull
    refine ⟨pg', ?_, by rw [← hws]; exact hplain, ?_, fun h => by omega⟩
    · unfold leafPgAt at hlp ⊢; rw [if_neg (by omega)] at hlp ⊢; exact hlp
    · unfold pgEnts; rw [← hws]; exact hents

end pure

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A registered node's registry fragment** (out of `wtxWQ`'s `nlFrags`). -/
theorem wtxWQ_nlFrag (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (l : Loc)
    (y : Loc × Nat) (hl : X.nloc !! l = some y) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ l ↪[r.n.nl]□ y := by
  unfold wtxWQ wtxCoreQ nlAuth
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, ⟨Hnl, #Hf⟩, Hdb, Hview, Hst⟩, Hcells,
    Hmap⟩
  ihave #Hy := nlFrags_lookup r X.nloc l y hl $$ Hf
  iframe; iframe #
  ipureintro; exact Hr

theorem nodeLocs_congr (r : TxReg) (nl nl2 : Loc → Option (Loc × Nat)) :
    ∀ els : List elemRef, (∀ e ∈ els, e.node' ≠ null → nl e.node' = nl2 e.node') →
    ([∗list] e ∈ els, nodeLoc (GF := GF) r nl e) ⊢ [∗list] e ∈ els, nodeLoc r nl2 e
  | [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: t, h => by
    iintro Ht
    icases (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).1 $$ Ht with ⟨Ha, Ht⟩
    ihave Ht := nodeLocs_congr r nl nl2 t (fun e he => h e (List.mem_cons_of_mem _ he)) $$ Ht
    iapply (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r nl2 e)).2
    iframe Ht
    unfold nodeLoc
    by_cases hn : a.node' = null
    · rw [if_pos hn, if_pos hn]; iexact Ha
    · rw [if_neg hn, if_neg hn]
      icases Ha with ⟨%y, %hy, #Hf⟩
      iexists y
      iframe #
      ipureintro; rw [← h a (List.mem_cons_self ..) hn]; exact hy

theorem wStkOwn_congr (r : TxReg) (nl nl2 : Loc → Option (Loc × Nat)) (v : View) (rt : Nat)
    (ipg : List w8) (els : List elemRef)
    (h : ∀ e ∈ els, e.node' ≠ null → nl e.node' = nl2 e.node') :
    wStkOwn (GF := GF) r nl v rt ipg els ⊢ wStkOwn r nl2 v rt ipg els := by
  unfold wStkOwn
  iintro ⟨Hn, Hi⟩
  iframe Hi
  iapply nodeLocs_congr r nl nl2 els h $$ Hn

theorem wInlOwn_snoc (v : View) (rt : Nat) (ipg : List w8) (els : List elemRef) (e : elemRef)
    (h : els ≠ []) : wInlOwn (GF := GF) v rt ipg (els ++ [e]) = wInlOwn v rt ipg els := by
  cases els with
  | nil => exact absurd rfl h
  | cons a t => rfl

theorem wStkOwn_snoc (r : TxReg) (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat)
    (ipg : List w8) (els : List elemRef) (e : elemRef) (h : els ≠ []) :
    wStkOwn (GF := GF) r nl v rt ipg els ∗ nodeLoc r nl e ⊢ wStkOwn r nl v rt ipg (els ++ [e]) := by
  unfold wStkOwn
  rw [wInlOwn_snoc v rt ipg els e h]
  iintro ⟨⟨Hn, Hi⟩, He⟩
  iframe Hi
  iapply (BigSepL.bigSepL_snoc (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).2
  iframe

/-- An inline page's bytes, through a source. -/
theorem locOwn_srcLoc (v : View) (p : Loc) (bs : List w8) :
    locOwn (GF := GF) v p bs ⊢ ∃ s, srcLoc v p s bs := by
  unfold locOwn
  iintro (%H | #H)
  · iexists Src.view; unfold srcLoc; ipureintro; exact H
  · iexists Src.own DFrac.discard; unfold srcLoc; iexact H

/-- **A writer stack's registry agrees with the writer's** (its `wStkOwn`, persistent, kept). -/
theorem wtxWQ_wStkOwn_agree (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat) (ipg : List w8) (els : List elemRef) :
    wtxWQ (GF := GF) K tx r m q X ∗ wStkOwn r nl v rt ipg els ⊢
      wtxWQ K tx r m q X ∗ ⌜∀ e ∈ els, e.node' ≠ null → nl e.node' = nlX X e.node'⌝ := by
  unfold wStkOwn nlX
  iintro ⟨Hw, Hn, -⟩
  iapply wtxWQ_nodeLoc_agree K tx r m q X nl els $$ [Hw Hn]
  iframe

end iprop

end WGoFirst

end bbolt
end EtcdGrove
end Perennial
